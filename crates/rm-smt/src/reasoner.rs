//! AKX reasoner wrapper around the CDCL(T) SMT solver.
//!
//! `SmtReasoner` implements the [`Reasoner`] trait for the combined EUF+DL
//! solver. One instance is bound to one `WorkUnit`; the scheduler creates a
//! fresh reasoner per problem.
//!
//! # Knowledge exchange
//! - **Export**: learned SAT backbone clauses (tagged with `assumptions = ctx`).
//! - **Import**: SAT clauses from peer CDCL(T) workers with overlapping contexts.
//! - Theory lemmas (N-O derived equalities) are a future extension (spec §11.1).

use std::sync::{Arc, Mutex};
use std::time::Instant;

use rm_akx::{
    Capabilities, Checkpoint, ClauseKnowledge, CubePath, ExportPolicy, HardwareClass,
    ImportDecision, ImportGate, ImportPolicy, ImportStats, KnowledgeBatch, KnowledgeId,
    KnowledgeKind, KnowledgeKindTag, KnowledgeObject, Literal, PartialModel, Priority, ProblemId,
    Reasoner, ReasonerError, ReasonerEvent, ReasonerId, Scope, TrustLevel, WorkBudget, WorkUnit,
    WorkerId,
};

use crate::cdclt::{build_cdclt_from_text, CdclT, NoResult};

const KID_WORD: u64 = 1 << 32;

/// AKX reasoner wrapping the CDCL(T) SMT solver.
pub struct SmtReasoner {
    id: ReasonerId,
    worker_id: WorkerId,
    work: WorkUnit,

    /// The CDCL(T) engine. `None` only if encoding produced an immediate contradiction.
    cdclt: Option<CdclT>,
    gate: ImportGate,
    /// Sorted assumption literals of `work` (== `ctx_W`).
    ctx: Vec<Literal>,

    pending: Mutex<Vec<KnowledgeObject>>,
    next_kid: u64,
    max_imported_id: u64,

    /// Upper bound on backbone SAT variable IDs; used to filter out foreign vars.
    num_vars: u32,
    /// Cached final verdict; set once `cdclt.solve()` returns Sat or Unsat.
    done: Option<NoResult>,
}

impl SmtReasoner {
    /// Parse and encode `text` into a fresh reasoner bound to `work`.
    pub fn new(
        id: ReasonerId,
        worker_id: WorkerId,
        text: &str,
        work: WorkUnit,
    ) -> Result<Self, String> {
        let cancel = work.shutdown.clone();
        let cdclt = build_cdclt_from_text(text, cancel)?;
        let num_vars = cdclt.as_ref().map(|c| c.num_sat_vars()).unwrap_or(0);

        let mut ctx = work.assumptions.clone();
        ctx.sort_unstable();
        ctx.dedup();

        let gate = ImportGate::new(ImportPolicy::default());
        let mut r = SmtReasoner {
            id,
            worker_id,
            work,
            cdclt,
            gate,
            ctx,
            pending: Mutex::new(Vec::new()),
            next_kid: ((worker_id.0 as u64) * KID_WORD) | 1,
            max_imported_id: 0,
            num_vars,
            done: None,
        };
        r.gate.set_context(&r.ctx);
        Ok(r)
    }

    fn drain_learned_to_pending(&mut self) {
        let Some(cdclt) = &mut self.cdclt else { return };
        let mut pending = self.pending.lock().unwrap();
        for (lits, lbd) in cdclt.drain_learned_clauses() {
            let mut sorted = lits;
            sorted.sort_unstable();
            sorted.dedup();
            pending.push(KnowledgeObject {
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
            });
            self.next_kid += 1;
        }
    }

    /// Drain and export without accumulating into `pending` when policy rejects everything.
    pub fn drain_and_export(&mut self, policy: &ExportPolicy) -> KnowledgeBatch {
        if policy.max_items == 0 {
            if let Some(cdclt) = &mut self.cdclt {
                cdclt.drain_learned_clauses();
            }
            return KnowledgeBatch::new();
        }
        self.drain_learned_to_pending();
        self.export(policy).unwrap_or_default()
    }
}

impl Reasoner for SmtReasoner {
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
                ImportDecision::DiscardedNoOverlap | ImportDecision::DiscardedLowUtility => {
                    stats.discarded_no_overlap += 1;
                }
            }
        }

        if !clauses.is_empty() {
            if let Some(cdclt) = &mut self.cdclt {
                cdclt.import_sat_clauses(&clauses);
            }
        }
        Ok(stats)
    }

    fn step(&mut self, budget: WorkBudget) -> Result<ReasonerEvent, ReasonerError> {
        if self.work.is_cancelled() {
            return Ok(ReasonerEvent::Cancelled);
        }

        // Encoding produced an immediate contradiction → permanently Unknown.
        let Some(cdclt) = &mut self.cdclt else {
            return Ok(ReasonerEvent::BudgetExhausted);
        };

        if let Some(result) = self.done {
            return match result {
                NoResult::Sat => {
                    let model = PartialModel {
                        assignments: Vec::new(),
                        work_unit_ancestry: self.work.ancestry.clone(),
                    };
                    Ok(ReasonerEvent::SatCandidate {
                        model: Arc::new(model),
                    })
                }
                NoResult::Unsat => Ok(ReasonerEvent::UnsatLocal { proof_ref: None }),
                NoResult::Unknown => Ok(ReasonerEvent::BudgetExhausted),
            };
        }

        let _started = Instant::now();
        let result = cdclt.solve(budget.max_conflicts);

        if self.work.is_cancelled() {
            return Ok(ReasonerEvent::Cancelled);
        }

        match result {
            NoResult::Sat => {
                self.done = Some(NoResult::Sat);
                let model = PartialModel {
                    assignments: Vec::new(),
                    work_unit_ancestry: self.work.ancestry.clone(),
                };
                Ok(ReasonerEvent::SatCandidate {
                    model: Arc::new(model),
                })
            }
            NoResult::Unsat => {
                self.done = Some(NoResult::Unsat);
                Ok(ReasonerEvent::UnsatLocal { proof_ref: None })
            }
            NoResult::Unknown => Ok(ReasonerEvent::BudgetExhausted),
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

fn utility_of(lbd: u32) -> f32 {
    (1.0 / (1.0 + lbd as f32)).clamp(0.0, 1.0)
}

// ---------------------------------------------------------------------------
// make_smt_work_unit — helper for tests and driver code
// ---------------------------------------------------------------------------

pub fn make_smt_work_unit(seed: u64, budget: WorkBudget) -> WorkUnit {
    use std::sync::atomic::AtomicBool;
    WorkUnit {
        problem: ProblemId(0),
        assumptions: Vec::new(),
        ancestry: CubePath::default(),
        priority: Priority::NORMAL,
        budget,
        seed,
        shutdown: Arc::new(AtomicBool::new(false)),
    }
}

// ---------------------------------------------------------------------------
// SmtWorkerPool — run N SmtReasoners in parallel on the same problem
// ---------------------------------------------------------------------------

use rm_bus::{inproc::InprocBus, BusConfig, BusError, KnowledgeBus, PollBudget};

/// Configuration for a parallel SMT worker pool.
#[derive(Clone, Debug)]
pub struct SmtWorkerConfig {
    pub num_workers: usize,
    pub bus: BusConfig,
    pub step_budget: WorkBudget,
    pub export_policy: ExportPolicy,
    pub import_policy: ImportPolicy,
    pub seed: u64,
}

impl Default for SmtWorkerConfig {
    fn default() -> Self {
        SmtWorkerConfig {
            num_workers: 4,
            bus: BusConfig::default(),
            step_budget: WorkBudget::default(),
            export_policy: ExportPolicy::default(),
            import_policy: ImportPolicy::default(),
            seed: 1,
        }
    }
}

/// Outcome of a single SMT worker.
#[derive(Debug, Clone)]
pub enum SmtWorkerOutcome {
    Sat { worker: WorkerId },
    Unsat { worker: WorkerId },
    Aborted { worker: WorkerId },
}

/// Run `num_workers` `SmtReasoner`s in parallel on `text`, sharing learned
/// clauses via an in-process AKX bus. Returns the first conclusive outcome.
pub fn run_smt_pool(
    text: &str,
    config: SmtWorkerConfig,
    deadline: Option<std::time::Duration>,
) -> Vec<SmtWorkerOutcome> {
    use std::sync::atomic::AtomicBool;

    let bus: Arc<dyn KnowledgeBus> =
        Arc::new(InprocBus::new(&config.bus));
    let shutdown = Arc::new(AtomicBool::new(false));

    let handles: Vec<_> = (0..config.num_workers)
        .map(|i| {
            let text = text.to_owned();
            let bus = Arc::clone(&bus);
            let shutdown = Arc::clone(&shutdown);
            let cfg = config.clone();
            std::thread::Builder::new()
                .name(format!("smt-worker-{i}"))
                .spawn(move || {
                    run_smt_worker(WorkerId(i as u32), &text, cfg, bus, shutdown, deadline)
                })
                .expect("spawn")
        })
        .collect();

    handles
        .into_iter()
        .map(|h| h.join().expect("smt worker panicked"))
        .collect()
}

fn splitmix64(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9e3779b97f4a7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d049bb133111eb);
    x ^ (x >> 31)
}

fn run_smt_worker(
    worker: WorkerId,
    text: &str,
    cfg: SmtWorkerConfig,
    bus: Arc<dyn KnowledgeBus>,
    shutdown: Arc<std::sync::atomic::AtomicBool>,
    deadline: Option<std::time::Duration>,
) -> SmtWorkerOutcome {
    let seed = splitmix64(cfg.seed ^ ((worker.0 as u64).wrapping_shl(32)));
    let budget = cfg.step_budget;
    let work = make_smt_work_unit(seed, budget);
    // Wire the pool-level shutdown into the work unit's cancel flag.
    let work = WorkUnit {
        shutdown: Arc::clone(&shutdown),
        ..work
    };

    let mut reasoner = match SmtReasoner::new(ReasonerId(worker.0), worker, text, work) {
        Ok(r) => r,
        Err(_) => return SmtWorkerOutcome::Aborted { worker },
    };

    let started = std::time::Instant::now();
    loop {
        if deadline.is_some_and(|d| started.elapsed() >= d)
            || shutdown.load(std::sync::atomic::Ordering::SeqCst)
        {
            return SmtWorkerOutcome::Aborted { worker };
        }

        match reasoner.step(cfg.step_budget) {
            Ok(ReasonerEvent::UnsatLocal { .. }) => {
                shutdown.store(true, std::sync::atomic::Ordering::SeqCst);
                return SmtWorkerOutcome::Unsat { worker };
            }
            Ok(ReasonerEvent::SatCandidate { .. }) => {
                shutdown.store(true, std::sync::atomic::Ordering::SeqCst);
                return SmtWorkerOutcome::Sat { worker };
            }
            Ok(ReasonerEvent::Progress) | Ok(ReasonerEvent::BudgetExhausted) => {
                drain_export_import_smt(&mut reasoner, &bus, &cfg);
            }
            Ok(ReasonerEvent::Cancelled) | Ok(ReasonerEvent::NeedWork) => {
                return SmtWorkerOutcome::Aborted { worker };
            }
            Ok(ReasonerEvent::InternalError(e)) | Err(e) => {
                log::error!("smt worker {worker:?} failed: {e}");
                return SmtWorkerOutcome::Aborted { worker };
            }
        }
    }
}

fn drain_export_import_smt(
    reasoner: &mut SmtReasoner,
    bus: &Arc<dyn KnowledgeBus>,
    cfg: &SmtWorkerConfig,
) {
    let batch = reasoner.drain_and_export(&cfg.export_policy);
    if !batch.is_empty() {
        match bus.publish(Scope::Process, batch) {
            Ok(_) => {}
            Err(BusError::BufferFull) => {}
            Err(e) => log::warn!("smt bus publish: {e}"),
        }
    }
    match bus.poll(PollBudget::default()) {
        Ok(batch) if !batch.is_empty() => {
            let _ = reasoner.import(batch);
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn work() -> WorkUnit {
        make_smt_work_unit(42, WorkBudget { max_conflicts: 50_000, max_ms: 10_000 })
    }

    #[test]
    fn smt_reasoner_unsat_simple() {
        let text = "(set-logic QF_UFIDL)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (= (f 0) 1))
(assert (= (f 1) 2))
(assert (or (= x 0) (= x 1)))
(assert (= (f x) 3))
(check-sat)";
        let mut r = SmtReasoner::new(ReasonerId(0), WorkerId(0), text, work()).unwrap();
        let budget = WorkBudget { max_conflicts: 100_000, max_ms: 30_000 };
        loop {
            match r.step(budget).unwrap() {
                ReasonerEvent::UnsatLocal { .. } => return,
                ReasonerEvent::SatCandidate { .. } => panic!("expected unsat"),
                ReasonerEvent::BudgetExhausted | ReasonerEvent::Progress => continue,
                ReasonerEvent::Cancelled | ReasonerEvent::NeedWork => panic!("unexpected"),
                ReasonerEvent::InternalError(e) => panic!("error: {e}"),
            }
        }
    }

    #[test]
    fn smt_reasoner_sat_simple() {
        let text = "(set-logic QF_IDL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (<= (- x y) 5))
(assert (<= (- y x) 3))
(check-sat)";
        let mut r = SmtReasoner::new(ReasonerId(0), WorkerId(0), text, work()).unwrap();
        let budget = WorkBudget { max_conflicts: 100_000, max_ms: 30_000 };
        loop {
            match r.step(budget).unwrap() {
                ReasonerEvent::SatCandidate { .. } => return,
                ReasonerEvent::UnsatLocal { .. } => panic!("expected sat"),
                ReasonerEvent::BudgetExhausted | ReasonerEvent::Progress => continue,
                ReasonerEvent::Cancelled | ReasonerEvent::NeedWork => panic!("unexpected"),
                ReasonerEvent::InternalError(e) => panic!("error: {e}"),
            }
        }
    }

    #[test]
    fn smt_pool_unsat() {
        let text = "(set-logic QF_UFIDL)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (= (f 0) 1))
(assert (= (f 1) 2))
(assert (or (= x 0) (= x 1)))
(assert (= (f x) 3))
(check-sat)";
        let cfg = SmtWorkerConfig { num_workers: 2, ..SmtWorkerConfig::default() };
        let outcomes = run_smt_pool(text, cfg, Some(std::time::Duration::from_secs(30)));
        assert!(
            outcomes.iter().any(|o| matches!(o, SmtWorkerOutcome::Unsat { .. })),
            "expected unsat: {outcomes:?}"
        );
        assert!(
            !outcomes.iter().any(|o| matches!(o, SmtWorkerOutcome::Sat { .. })),
            "no sat expected: {outcomes:?}"
        );
    }
}
