//! AKX reasoner wrapper around the CDCL solver — Milestone M2.
//!
//! `CdclReasoner` implements the [`Reasoner`] trait (spec §3.2) for
//! [`CdclSolver`]. One instance is bound to a single [`WorkUnit`]; the worker
//! runtime creates a fresh reasoner (or restarts one from a checkpoint) when a
//! new work unit is dispatched.
//!
//! # Import soundness
//! Every imported object passes through the §7.3 import gate, so only
//! knowledge with `ctx ⊇ asmpts` is applied. The clause DB therefore only ever
//! contains clauses entailed by `F ∧ ctx`, and every clause the solver learns
//! is consequently entailed by `F ∧ ctx` — so exported clause knowledge is
//! always tagged with `assumptions = ctx`, which is a sound claim.

use std::sync::{atomic::AtomicBool, Arc, Mutex};
use std::time::Instant;

use rm_akx::{
    Capabilities, Checkpoint, ClauseKnowledge, CubePath, ExportPolicy, HardwareClass,
    ImportDecision, ImportGate, ImportPolicy, ImportStats, KnowledgeBatch, KnowledgeId,
    KnowledgeKind, KnowledgeKindTag, KnowledgeObject, Literal, PartialModel, Priority, ProblemId,
    Reasoner, ReasonerError, ReasonerEvent, ReasonerId, Scope, TrustLevel, WorkBudget, WorkUnit,
    WorkerId,
};

use crate::cdcl::{CdclSolver, SolveResult};

/// ID domain size for a single worker: `next_kid` never collides across
/// workers because each worker's knowledge IDs live in its own high word.
const KID_WORD: u64 = 1 << 32;

/// AKX reasoner over the CDCL solver.
///
/// `step` runs the solver under `work.assumptions` for one conflict budget and
/// returns [`ReasonerEvent::Progress`] at chunk boundaries so the scheduler can
/// export newly learned clauses. `export` returns only objects with
/// `id > policy.watermark`.
pub struct CdclReasoner {
    id: ReasonerId,
    worker_id: WorkerId,
    solver: CdclSolver,
    work: WorkUnit,

    gate: ImportGate,
    /// Sorted assumption literals of `work` (== `ctx_W`).
    ctx: Vec<Literal>,

    /// Knowledge produced by `step` but not yet exported.
    pending: Mutex<Vec<KnowledgeObject>>,
    /// Next knowledge ID to assign to an exported object.
    next_kid: u64,
    /// Highest `KnowledgeId` that has been applied through `import`.
    max_imported_id: u64,

    pub num_vars: u32,
}

impl CdclReasoner {
    /// Create a reasoner bound to `work`, solving the formula already loaded
    /// into `solver` (with `solver.num_vars` matching the problem). The solver
    /// must be freshly constructed (or returned to level 0) at this point.
    pub fn new(id: ReasonerId, worker_id: WorkerId, solver: CdclSolver, work: WorkUnit) -> Self {
        let num_vars = solver.num_vars();
        let mut ctx = work.assumptions.clone();
        ctx.sort_unstable();
        ctx.dedup();

        let gate = ImportGate::new(ImportPolicy::default());
        let mut r = CdclReasoner {
            id,
            worker_id,
            solver,
            work,
            gate,
            ctx,
            pending: Mutex::new(Vec::new()),
            next_kid: ((worker_id.0 as u64) * KID_WORD) | 1,
            max_imported_id: 0,
            num_vars,
        };
        r.gate.set_context(&r.ctx);
        r
    }

    /// As [`CdclReasoner::new`], but with a custom import policy and a Bloom
    /// pre-filter sized at `bits_per_ctx_literal` bits per context literal.
    pub fn with_import_policy(
        id: ReasonerId,
        worker_id: WorkerId,
        solver: CdclSolver,
        work: WorkUnit,
        policy: ImportPolicy,
        bloom_bits: Option<(usize, u32)>,
    ) -> Self {
        let num_vars = solver.num_vars();
        let mut ctx = work.assumptions.clone();
        ctx.sort_unstable();
        ctx.dedup();

        let gate = match bloom_bits {
            Some((bits, hashes)) => ImportGate::with_bloom(policy, bits, hashes),
            None => ImportGate::new(policy),
        };
        let mut r = CdclReasoner {
            id,
            worker_id,
            solver,
            work,
            gate,
            ctx,
            pending: Mutex::new(Vec::new()),
            next_kid: ((worker_id.0 as u64) * KID_WORD) | 1,
            max_imported_id: 0,
            num_vars,
        };
        r.gate.set_context(&r.ctx);
        r
    }

    pub fn worker_id(&self) -> WorkerId {
        self.worker_id
    }

    /// The solver backing this reasoner (exposed for tests and model checks).
    pub fn solver(&self) -> &CdclSolver {
        &self.solver
    }

    /// Drain newly learned clauses from the solver into `pending`, tagged with
    /// `assumptions = ctx` (sound: every DB clause is entailed by `F ∧ ctx`).
    fn drain_learned_to_pending(&mut self) {
        let mut pending = self.pending.lock().unwrap();
        for (lits, lbd) in self.solver.drain_learned() {
            let mut sorted = lits;
            sorted.sort_unstable();
            sorted.dedup();
            let obj = KnowledgeObject {
                id: KnowledgeId(self.next_kid),
                kind: KnowledgeKind::Clause(ClauseKnowledge {
                    literals: sorted.into_iter().collect(),
                    lbd,
                }),
                assumptions: self.ctx.clone().into(),
                scope: Scope::Process,
                trust: TrustLevel::Trusted,
                utility: utility_of(lbd),
                proof_ref: None,
                source: self.worker_id.0,
            };
            self.next_kid += 1;
            pending.push(obj);
        }
    }

    /// Drain and export in one pass, avoiding KnowledgeObject allocation when the
    /// policy will reject everything (e.g. isolated portfolio with `max_items == 0`).
    ///
    /// Use this instead of the `export(&self, policy)` trait method when `&mut self`
    /// is available (i.e. from `drain_export_import`). It is strictly more efficient
    /// because it skips the allocation+drop cycle for clauses that will never be sent.
    pub fn drain_and_export(&mut self, policy: &ExportPolicy) -> KnowledgeBatch {
        if policy.max_items == 0 {
            self.solver.drain_learned();
            return KnowledgeBatch::new();
        }
        self.drain_learned_to_pending();
        self.export(policy).unwrap_or_default()
    }

    fn to_partial_model(&self, m: &crate::model::Model) -> PartialModel {
        let mut assignments = vec![Some(false); m.num_vars() as usize + 1];
        for v in 1..=m.num_vars() {
            assignments[v as usize] = Some(m.value_of(v));
        }
        PartialModel {
            assignments,
            work_unit_ancestry: self.work.ancestry.clone(),
        }
    }
}

impl Reasoner for CdclReasoner {
    fn id(&self) -> ReasonerId {
        self.id
    }

    fn capabilities(&self) -> Capabilities {
        Capabilities {
            can_produce: smallvec::smallvec![KnowledgeKindTag::Clause],
            can_consume: smallvec::smallvec![KnowledgeKindTag::Clause],
            is_complete: true,
            produces_proofs: false,
            hardware: HardwareClass::Cpu,
        }
    }

    fn import(&mut self, batch: KnowledgeBatch) -> Result<ImportStats, ReasonerError> {
        let decisions = self.gate.submit(&batch);
        let mut stats = ImportStats {
            received: batch.len() as u32,
            ..ImportStats::default()
        };

        let mut clauses: Vec<Vec<Literal>> = Vec::new();
        for (obj, d) in batch.iter().zip(decisions.iter()) {
            match d {
                ImportDecision::Applied => {
                    if let KnowledgeKind::Clause(c) = &obj.kind {
                        if c.literals.iter().any(|l| l.var() > self.num_vars) {
                            stats.discarded_no_overlap += 1;
                            continue;
                        }
                        clauses.push(c.literals.iter().copied().collect());
                    }
                    stats.applied += 1;
                    self.max_imported_id = self.max_imported_id.max(obj.id.0);
                }
                ImportDecision::Buffered => stats.buffered += 1,
                ImportDecision::Duplicate => stats.discarded_duplicate += 1,
                ImportDecision::DiscardedNoOverlap => stats.discarded_no_overlap += 1,
                ImportDecision::DiscardedLowUtility => stats.discarded_no_overlap += 1,
            }
        }

        if !clauses.is_empty() {
            self.solver.import_clauses(&clauses);
        }
        Ok(stats)
    }

    fn step(&mut self, budget: WorkBudget) -> Result<ReasonerEvent, ReasonerError> {
        if self.work.is_cancelled() {
            return Ok(ReasonerEvent::Cancelled);
        }

        let started = Instant::now();
        let deadline = if budget.max_ms > 0 {
            started.checked_add(std::time::Duration::from_millis(budget.max_ms))
        } else {
            None
        };
        let result =
            self.solver
                .solve_with_deadline(&self.work.assumptions, budget.max_conflicts, deadline);

        if self.work.is_cancelled() {
            return Ok(ReasonerEvent::Cancelled);
        }

        match result {
            SolveResult::Sat(model) => Ok(ReasonerEvent::SatCandidate {
                model: Arc::new(self.to_partial_model(&model)),
            }),
            SolveResult::Unsat => Ok(ReasonerEvent::UnsatLocal { proof_ref: None }),
            SolveResult::Unknown => {
                let wall_budget_hit = started.elapsed().as_millis() as u64 >= budget.max_ms;
                if wall_budget_hit {
                    Ok(ReasonerEvent::BudgetExhausted)
                } else {
                    Ok(ReasonerEvent::Progress)
                }
            }
        }
    }

    fn export(&self, policy: &ExportPolicy) -> Result<KnowledgeBatch, ReasonerError> {
        let mut pending = self.pending.lock().unwrap();
        pending.retain(|o| o.id > policy.watermark);

        let mut out = KnowledgeBatch::new();
        let mut keep = Vec::new();
        for obj in pending.drain(..) {
            if out.len() >= policy.max_items {
                keep.push(obj);
                continue;
            }
            if obj.utility < policy.min_utility {
                continue;
            }
            if obj.scope > policy.max_scope {
                continue;
            }
            if !policy.kind_filter.is_empty() && !policy.kind_filter.contains(&obj.kind.tag()) {
                continue;
            }
            out.push(obj);
        }
        pending.extend(keep);
        Ok(out)
    }

    fn checkpoint(&self) -> Result<Option<Checkpoint>, ReasonerError> {
        Ok(Some(Checkpoint {
            worker_id: self.worker_id,
            work_unit: self.work.clone(),
            internal_state: None,
            knowledge_watermark: KnowledgeId(self.max_imported_id),
        }))
    }
}

/// Estimate the utility of a learned clause from its LBD. Lower LBD = more
/// useful, so `lbd = 1` maps to the top of the range.
fn utility_of(lbd: u32) -> f32 {
    (1.0 / (1.0 + lbd as f32)).clamp(0.0, 1.0)
}

/// Build a [`WorkUnit`] from scratch (helper for the worker runtime and tests).
pub fn make_work_unit(
    problem_id: u64,
    assumptions: Vec<Literal>,
    seed: u64,
    budget: WorkBudget,
) -> WorkUnit {
    WorkUnit {
        problem: ProblemId(problem_id),
        assumptions,
        ancestry: CubePath::default(),
        priority: Priority::NORMAL,
        budget,
        seed,
        shutdown: Arc::new(AtomicBool::new(false)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rm_akx::WorkBudget;

    /// The pigeonhole problem PHP(3,2): 3 pigeons in 2 holes is UNSAT — the
    /// classic hard-ish instance. Variables x1..x3 = hole 1, x4..x6 = hole 2.
    fn php_unsat() -> CdclSolver {
        let mut s = CdclSolver::new(6);
        // Each pigeon must have a hole: x1∨x4, x2∨x5, x3∨x6
        s.add_clause(&[Literal::positive(1), Literal::positive(4)]);
        s.add_clause(&[Literal::positive(2), Literal::positive(5)]);
        s.add_clause(&[Literal::positive(3), Literal::positive(6)]);
        // No two pigeons in hole 1: ¬x1∨¬x2, ¬x1∨¬x3, ¬x2∨¬x3
        s.add_clause(&[Literal::negative(1), Literal::negative(2)]);
        s.add_clause(&[Literal::negative(1), Literal::negative(3)]);
        s.add_clause(&[Literal::negative(2), Literal::negative(3)]);
        // No two pigeons in hole 2: ¬x4∨¬x5, ¬x4∨¬x6, ¬x5∨¬x6
        s.add_clause(&[Literal::negative(4), Literal::negative(5)]);
        s.add_clause(&[Literal::negative(4), Literal::negative(6)]);
        s.add_clause(&[Literal::negative(5), Literal::negative(6)]);
        s
    }

    /// PHP(2,2): 2 pigeons in 2 holes is satisfiable. x1,x2 = hole 1;
    /// x3,x4 = hole 2.
    fn php_sat() -> CdclSolver {
        let mut s = CdclSolver::new(4);
        s.add_clause(&[Literal::positive(1), Literal::positive(3)]);
        s.add_clause(&[Literal::positive(2), Literal::positive(4)]);
        s.add_clause(&[Literal::negative(1), Literal::negative(2)]);
        s.add_clause(&[Literal::negative(3), Literal::negative(4)]);
        s
    }

    fn work(assumptions: Vec<Literal>) -> WorkUnit {
        make_work_unit(
            1,
            assumptions,
            7,
            WorkBudget {
                max_conflicts: 1000,
                max_ms: 500,
            },
        )
    }

    #[test]
    fn step_finds_sat_model() {
        let mut r = CdclReasoner::new(ReasonerId(0), WorkerId(0), php_sat(), work(vec![]));
        let ev = r.step(WorkBudget::default()).unwrap();
        match ev {
            ReasonerEvent::SatCandidate { model } => {
                assert!(model.is_complete());
                for v in 1..=4u32 {
                    assert!(model.get(v).is_some());
                }
            }
            other => panic!("expected SatCandidate, got {other:?}"),
        }
    }

    #[test]
    fn step_reports_unsat_under_contradictory_assumptions() {
        // Force x1=true and ¬x1: immediately UNSAT at the assumption boundary.
        let mut r = CdclReasoner::new(
            ReasonerId(0),
            WorkerId(1),
            php_sat(),
            work(vec![Literal::positive(1), Literal::negative(1)]),
        );
        let ev = r.step(WorkBudget::default()).unwrap();
        match ev {
            ReasonerEvent::UnsatLocal { proof_ref } => assert!(proof_ref.is_none()),
            other => panic!("expected UnsatLocal, got {other:?}"),
        }
    }

    #[test]
    fn budget_exhausted_when_conflicts_run_out() {
        // Zero conflict budget on an UNSAT formula: the solver can never finish
        // in 0 conflicts, and max_ms = 0 forces a wall-clock stop too.
        let mut r = CdclReasoner::new(ReasonerId(0), WorkerId(2), php_unsat(), work(vec![]));
        let ev = r
            .step(WorkBudget {
                max_conflicts: 0,
                max_ms: 0,
            })
            .unwrap();
        assert!(matches!(ev, ReasonerEvent::BudgetExhausted));
    }

    #[test]
    fn learned_clauses_are_exported_with_ctx_and_filtered_by_watermark() {
        // UNSAT formula, capped budget: the solver is guaranteed to hit the
        // conflict budget before concluding, learning clauses along the way.
        let mut r = CdclReasoner::new(ReasonerId(0), WorkerId(4), php_unsat(), work(vec![]));
        let _ = r
            .step(WorkBudget {
                max_conflicts: 100,
                max_ms: 0,
            })
            .unwrap();

        // drain_and_export() performs the lazy drain from the solver's outbox
        // and then applies the policy filter in one pass.
        let batch = r.drain_and_export(&ExportPolicy::default());
        assert!(!batch.is_empty());
        // Everything exported carries ctx assumptions (or fewer).
        for obj in &batch {
            assert!(matches!(obj.kind, KnowledgeKind::Clause(_)));
            assert!(obj.assumptions.iter().all(|l| r.ctx.contains(l)));
        }

        // Re-export with the watermark past everything: the outbox is empty
        // (already drained above) and pending is now empty too.
        let max_id = batch.iter().map(|o| o.id).max().unwrap();
        let empty = r.drain_and_export(&ExportPolicy {
            watermark: max_id,
            ..ExportPolicy::default()
        });
        assert!(empty.is_empty());
    }

    #[test]
    fn import_applies_unconditional_and_ctx_subset_clauses() {
        let mut r = CdclReasoner::new(ReasonerId(0), WorkerId(5), php_sat(), work(vec![]));

        // Unconditional clause: x4 ∨ ¬x1 — always applicable (ctx = ∅).
        let unconditional = KnowledgeObject {
            id: KnowledgeId(9001),
            kind: KnowledgeKind::Clause(ClauseKnowledge {
                literals: smallvec::smallvec![Literal::positive(4), Literal::negative(1)],
                lbd: 2,
            }),
            assumptions: smallvec::smallvec![],
            scope: Scope::Process,
            trust: TrustLevel::Trusted,
            utility: 0.5,
            proof_ref: None,
            source: 99,
        };

        let stats = r.import(vec![unconditional]).unwrap();
        assert_eq!(stats.received, 1);
        assert_eq!(stats.applied, 1);
        assert_eq!(stats.buffered, 0);

        let cp = r.checkpoint().unwrap().unwrap();
        assert_eq!(cp.knowledge_watermark, KnowledgeId(9001));
    }

    #[test]
    fn import_defers_out_of_context_knowledge() {
        // Worker assumes {x1}; the object is conditional on {x5} → no overlap.
        let mut r = CdclReasoner::new(
            ReasonerId(0),
            WorkerId(6),
            php_sat(),
            work(vec![Literal::positive(1)]),
        );

        let conditional = KnowledgeObject {
            id: KnowledgeId(42),
            kind: KnowledgeKind::Clause(ClauseKnowledge {
                literals: smallvec::smallvec![Literal::negative(2)],
                lbd: 2,
            }),
            assumptions: smallvec::smallvec![Literal::positive(5)],
            scope: Scope::Process,
            trust: TrustLevel::Trusted,
            utility: 0.5,
            proof_ref: None,
            source: 7,
        };

        let stats = r.import(vec![conditional]).unwrap();
        assert_eq!(stats.discarded_no_overlap, 1);
        assert_eq!(stats.applied, 0);
        assert_eq!(r.gate.buffer_len(), 0);
    }

    #[test]
    fn capabilities_declare_clause_io() {
        let r = CdclReasoner::new(ReasonerId(0), WorkerId(7), php_sat(), work(vec![]));
        let c = r.capabilities();
        assert!(c.is_complete);
        assert!(c.can_produce.contains(&KnowledgeKindTag::Clause));
        assert!(c.can_consume.contains(&KnowledgeKindTag::Clause));
    }
}
