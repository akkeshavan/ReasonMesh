//! rm-worker — in-process worker runtime (spec §11).
//!
//! A [`WorkerPool`] runs N [`CdclReasoner`]s on a shared [`InprocBus`]. Every
//! worker solves the same formula (its own clause DB + heuristic seed), and
//! learned clauses flow between workers through the bus. Each worker enforces
//! the §7.3 import predicate via its import gate before applying foreign
//! knowledge.
//!
//! # Soundness
//! A worker that reports `Sat` carries an independently validated model; a
//! worker that reports `Unsat` under its cube is a complete solver, so the
//! cube is closed. Imported clauses are consequences of the worker's context
//! (§7.3), so sharing can only prune search, never change the answer.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use rm_akx::{
    CubePath, ExportPolicy, ImportPolicy, Literal, PartialModel, Priority, ProblemId, Reasoner,
    ReasonerEvent, ReasonerId, Scope, WorkBudget, WorkUnit, WorkerId,
};
use rm_bus::{inproc::InprocBus, BusConfig, BusError, KnowledgeBus, PollBudget};
use rm_sat::{CdclReasoner, CdclSolver};

/// Configuration for a [`WorkerPool`].
#[derive(Clone, Debug)]
pub struct WorkerConfig {
    /// Number of concurrent CDCL workers.
    pub num_workers: usize,
    pub bus: BusConfig,
    /// Per-`step` work budget handed to each reasoner.
    pub step_budget: WorkBudget,
    pub export_policy: ExportPolicy,
    pub import_policy: ImportPolicy,
    /// Base random seed; worker `i` is seeded with `seed + i` for portfolio
    /// diversification.
    pub seed: u64,
    /// Cumulative conflict budget: abort a worker once its total search
    /// exceeds this. `None` = unbounded (the step deadline still bounds wall
    /// time). Distinct from [`WorkerConfig::step_budget`], which is the *chunk*
    /// cadence that paces asynchronous clause exchange.
    pub conflict_budget: Option<u64>,
}

impl Default for WorkerConfig {
    fn default() -> Self {
        WorkerConfig {
            num_workers: 4,
            bus: BusConfig::default(),
            step_budget: WorkBudget::default(),
            export_policy: ExportPolicy::default(),
            import_policy: ImportPolicy::default(),
            seed: 1,
            conflict_budget: None,
        }
    }
}

/// Per-worker search counters captured at the point a worker reports an
/// outcome (spec §16.2 "Search" metrics; used to compare portfolios).
#[derive(Debug, Clone, Copy, Default)]
pub struct WorkerStats {
    pub conflicts: u64,
    pub decisions: u64,
    pub propagations: u64,
    pub restarts: u64,
    // Knowledge-exchange diagnostics (spec §16.2 "Knowledge"): accumulated
    // across the drain/export/import rounds of one run.
    /// Objects the worker exported to the bus (before bus dedup/eviction).
    pub exported: u64,
    /// Objects actually enqueued on the bus (after dedup/eviction).
    pub published: u64,
    /// Objects this worker polled from the bus.
    pub received: u64,
    /// Polled objects applied through the import gate.
    pub applied: u64,
    /// Polled objects buffered awaiting context match.
    pub buffered: u64,
    /// Polled objects discarded (no overlap, duplicate, or low utility).
    pub discarded: u64,
}

/// The outcome of a single worker in a run.
#[derive(Debug, Clone)]
pub enum WorkerOutcome {
    /// Worker found a satisfying assignment (validated against F ∧ cube).
    Sat {
        worker: WorkerId,
        model: PartialModel,
        stats: WorkerStats,
    },
    /// Worker proved its cube unsatisfiable (complete solver ⇒ cube closed).
    Unsat {
        worker: WorkerId,
        stats: WorkerStats,
    },
    /// Worker stopped without a conclusion (deadline or cancellation).
    Aborted {
        worker: WorkerId,
        stats: WorkerStats,
    },
}

/// Snapshot the solver's search counters.
fn stats_of(solver: &CdclSolver) -> WorkerStats {
    WorkerStats {
        conflicts: solver.conflicts,
        decisions: solver.decisions,
        propagations: solver.propagations,
        restarts: solver.restarts,
        ..Default::default()
    }
}

/// Combine live search counters with the accumulated knowledge-exchange
/// diagnostics from this worker's drain/export/import rounds.
fn fold_stats(solver: &CdclSolver, shared: &WorkerStats) -> WorkerStats {
    let mut s = stats_of(solver);
    s.exported = shared.exported;
    s.published = shared.published;
    s.received = shared.received;
    s.applied = shared.applied;
    s.buffered = shared.buffered;
    s.discarded = shared.discarded;
    s
}

/// A shared-solver runtime: `num_workers` threads each running a reasoner on a
/// shared knowledge bus. The bus may be an in-process `InprocBus`, a networked
/// `NetBus`, or any composite implementation (`BroadcastBus`, etc.) as long as
/// it implements `KnowledgeBus + Send + Sync`.
pub struct WorkerPool {
    problem: Problem,
    bus: Arc<dyn KnowledgeBus>,
    config: WorkerConfig,
    shutdown: Arc<AtomicBool>,
    results: Mutex<Vec<WorkerOutcome>>,
}

/// DIMACS-style problem given to a pool: variables 1..=num_vars, `clauses` a
/// list of literal lists.
#[derive(Clone)]
pub struct Problem {
    pub num_vars: u32,
    pub clauses: Vec<Vec<Literal>>,
}

impl Problem {
    pub fn new(num_vars: u32, clauses: Vec<Vec<Literal>>) -> Self {
        Problem { num_vars, clauses }
    }

    /// Build a fresh solver with this problem loaded.
    pub fn solver(&self) -> CdclSolver {
        let mut s = CdclSolver::new(self.num_vars);
        for c in &self.clauses {
            s.add_clause(c);
        }
        s
    }

    /// Independently verify `model` against the problem and `cube`.
    pub fn validates(&self, model: &PartialModel, cube: &[Literal]) -> bool {
        for &lit in cube {
            match model.get(lit.var()) {
                Some(v) if v == lit.is_positive() => {}
                _ => return false,
            }
        }
        for clause in &self.clauses {
            let sat = clause.iter().any(|&l| match model.get(l.var()) {
                Some(v) => v == l.is_positive(),
                None => false,
            });
            if !sat {
                return false;
            }
        }
        true
    }
}

impl WorkerPool {
    /// Create a pool for `problem` with a fresh `InprocBus`.
    pub fn new(problem: Problem, config: WorkerConfig) -> Self {
        let bus = Arc::new(InprocBus::new(&config.bus)) as Arc<dyn KnowledgeBus>;
        WorkerPool::with_bus(problem, config, bus)
    }

    /// Create a pool using a caller-supplied bus implementation. Use this to
    /// inject a `BroadcastBus`, `NetBus`, or other composite transport.
    pub fn with_bus(problem: Problem, config: WorkerConfig, bus: Arc<dyn KnowledgeBus>) -> Self {
        WorkerPool {
            problem,
            bus,
            config,
            shutdown: Arc::new(AtomicBool::new(false)),
            results: Mutex::new(Vec::new()),
        }
    }

    /// The shared bus (for inspection and bridge wiring).
    pub fn bus(&self) -> Arc<dyn KnowledgeBus> {
        Arc::clone(&self.bus)
    }

    /// §16.2 bus-level operational metrics, as of the last poll.
    pub fn bus_metrics(&self) -> rm_akx::BusMetrics {
        self.bus.metrics()
    }

    /// Run every worker to a conclusion or `deadline`. Returns the outcomes
    /// in worker-id order (an entry for each worker that ran).
    ///
    /// `cubes[i]` are the assumption literals restricting worker `i`; pass
    /// empty cubes for a flat portfolio. `cubes` must have exactly
    /// `config.num_workers` entries (or be empty to default to root search).
    pub fn run(&self, cubes: &[Vec<Literal>], deadline: Option<Duration>) -> Vec<WorkerOutcome> {
        let problem = &self.problem;
        let mut handles = Vec::with_capacity(self.config.num_workers);
        for i in 0..self.config.num_workers {
            let assumptions = if cubes.is_empty() {
                Vec::new()
            } else {
                cubes[i].clone()
            };
            let bus: Arc<dyn KnowledgeBus> = Arc::clone(&self.bus);
            let shutdown = Arc::clone(&self.shutdown);
            let cfg = self.config.clone();
            let problem = Problem {
                num_vars: problem.num_vars,
                clauses: problem.clauses.clone(),
            };
            handles.push(
                std::thread::Builder::new()
                    .name(format!("rm-worker-{i}"))
                    .spawn(move || {
                        run_worker(
                            WorkerId(i as u32),
                            &problem,
                            assumptions,
                            cfg,
                            bus,
                            shutdown,
                            deadline,
                        )
                    })
                    .expect("spawn worker thread"),
            );
        }

        let outcomes: Vec<WorkerOutcome> = handles
            .into_iter()
            .map(|h| h.join().expect("worker thread panicked"))
            .collect();
        let mut results = self.results.lock().unwrap();
        results.extend(outcomes.iter().cloned());
        outcomes
    }

    /// Force all running workers to cancel.
    pub fn cancel(&self) {
        self.shutdown.store(true, Ordering::SeqCst);
    }

    /// Outcomes observed so far across runs.
    pub fn results(&self) -> Vec<WorkerOutcome> {
        self.results.lock().unwrap().clone()
    }
}

fn validate_sat_and_finish(
    problem: &Problem,
    assumptions: &[Literal],
    worker: WorkerId,
    model: Arc<PartialModel>,
    solver: &CdclSolver,
    shared: &WorkerStats,
    shutdown: &Arc<AtomicBool>,
) -> WorkerOutcome {
    if problem.validates(&model, assumptions) {
        shutdown.store(true, Ordering::SeqCst);
        return WorkerOutcome::Sat {
            worker,
            model: (*model).clone(),
            stats: fold_stats(solver, shared),
        };
    }
    log::error!("worker {worker:?} returned an invalid model");
    WorkerOutcome::Aborted {
        worker,
        stats: fold_stats(solver, shared),
    }
}

fn finish_unsat(
    worker: WorkerId,
    assumptions: &[Literal],
    solver: &CdclSolver,
    shared: &WorkerStats,
    shutdown: &Arc<AtomicBool>,
) -> WorkerOutcome {
    if assumptions.is_empty() {
        shutdown.store(true, Ordering::SeqCst);
    }
    WorkerOutcome::Unsat {
        worker,
        stats: fold_stats(solver, shared),
    }
}

fn run_worker(
    worker: WorkerId,
    problem: &Problem,
    assumptions: Vec<Literal>,
    cfg: WorkerConfig,
    bus: Arc<dyn KnowledgeBus>,
    shutdown: Arc<AtomicBool>,
    deadline: Option<Duration>,
) -> WorkerOutcome {
    let solver = problem.solver();
    let work = make_work_unit_with(assumptions.clone(), cfg.seed + worker.0 as u64);
    let mut reasoner = CdclReasoner::with_import_policy(
        ReasonerId(worker.0),
        worker,
        solver,
        work,
        cfg.import_policy.clone(),
        None,
    );
    let started = Instant::now();
    let mut shared = WorkerStats::default();
    let mut ran_conflicts = 0u64;
    loop {
        if deadline.is_some_and(|d| started.elapsed() >= d) || shutdown.load(Ordering::SeqCst) {
            return WorkerOutcome::Aborted {
                worker,
                stats: fold_stats(reasoner.solver(), &shared),
            };
        }
        let conflicts_before = reasoner.solver().conflicts;
        match reasoner.step(cfg.step_budget) {
            Ok(ReasonerEvent::SatCandidate { model }) => {
                return validate_sat_and_finish(
                    problem,
                    &assumptions,
                    worker,
                    model,
                    reasoner.solver(),
                    &shared,
                    &shutdown,
                );
            }
            Ok(ReasonerEvent::UnsatLocal { .. }) => {
                return finish_unsat(worker, &assumptions, reasoner.solver(), &shared, &shutdown);
            }
            Ok(ReasonerEvent::Progress) | Ok(ReasonerEvent::BudgetExhausted) => {
                ran_conflicts = ran_conflicts
                    .saturating_add(reasoner.solver().conflicts.saturating_sub(conflicts_before));
                if cfg.conflict_budget.is_some_and(|cap| ran_conflicts >= cap) {
                    return WorkerOutcome::Aborted {
                        worker,
                        stats: fold_stats(reasoner.solver(), &shared),
                    };
                }
                drain_export_import(&mut reasoner, &bus, &cfg, &mut shared);
            }
            Ok(ReasonerEvent::Cancelled) | Ok(ReasonerEvent::NeedWork) => {
                return WorkerOutcome::Aborted {
                    worker,
                    stats: fold_stats(reasoner.solver(), &shared),
                };
            }
            Ok(ReasonerEvent::InternalError(e)) | Err(e) => {
                log::error!("worker {worker:?} failed: {e}");
                return WorkerOutcome::Aborted {
                    worker,
                    stats: fold_stats(reasoner.solver(), &shared),
                };
            }
        }
    }
}

/// One round of knowledge exchange: export new learned clauses to the bus,
/// then import anything peers published. Back-pressure is handled by dropping
/// (the exporter backs off naturally because the next export carries a
/// watermark the caller advances only for accepted items). Every batch is
/// accounted into `acc` so the final [`WorkerStats`] reports the §16.2
/// "Knowledge" metrics.
fn drain_export_import(
    reasoner: &mut CdclReasoner,
    bus: &Arc<dyn KnowledgeBus>,
    cfg: &WorkerConfig,
    acc: &mut WorkerStats,
) {
    let batch = reasoner.drain_and_export(&cfg.export_policy);
    acc.exported += batch.len() as u64;
    if !batch.is_empty() {
        match bus.publish(Scope::Process, batch) {
            Ok(handle) => acc.published += handle.enqueued as u64,
            Err(BusError::BufferFull) => {}
            Err(e) => log::warn!("bus publish failed: {e}"),
        }
    }
    match bus.poll(PollBudget::default()) {
        Ok(batch) => {
            acc.received += batch.len() as u64;
            if !batch.is_empty() {
                match reasoner.import(batch) {
                    Ok(st) => {
                        acc.applied += st.applied as u64;
                        acc.buffered += st.buffered as u64;
                        acc.discarded += (st.discarded_no_overlap + st.discarded_duplicate) as u64;
                    }
                    Err(e) => log::warn!("bus import failed: {e}"),
                }
            }
        }
        Err(e) => log::warn!("bus poll failed: {e}"),
    }
}

fn make_work_unit_with(assumptions: Vec<Literal>, seed: u64) -> WorkUnit {
    let budget = WorkBudget::default();
    WorkUnit {
        problem: ProblemId(0),
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

    /// Brute-force SAT oracle over a small problem + cube.
    fn brute_force(problem: &Problem, cube: &[Literal]) -> bool {
        let n = problem.num_vars as usize;
        for mask in 0u64..(1u64 << n) {
            let mut ok = cube.iter().all(|&l| {
                let v = (mask >> (l.var() - 1)) & 1 == 1;
                v == l.is_positive()
            });
            if !ok {
                continue;
            }
            for clause in &problem.clauses {
                ok = clause.iter().any(|&l| {
                    let v = (mask >> (l.var() - 1)) & 1 == 1;
                    v == l.is_positive()
                });
                if !ok {
                    break;
                }
            }
            if ok {
                return true;
            }
        }
        false
    }

    fn php2_2_sat() -> Problem {
        let clauses = vec![
            vec![Literal::positive(1), Literal::positive(3)],
            vec![Literal::positive(2), Literal::positive(4)],
            vec![Literal::negative(1), Literal::negative(2)],
            vec![Literal::negative(3), Literal::negative(4)],
        ];
        Problem::new(4, clauses)
    }

    fn php3_2_unsat() -> Problem {
        let clauses = vec![
            vec![Literal::positive(1), Literal::positive(4)],
            vec![Literal::positive(2), Literal::positive(5)],
            vec![Literal::positive(3), Literal::positive(6)],
            vec![Literal::negative(1), Literal::negative(2)],
            vec![Literal::negative(1), Literal::negative(3)],
            vec![Literal::negative(2), Literal::negative(3)],
            vec![Literal::negative(4), Literal::negative(5)],
            vec![Literal::negative(4), Literal::negative(6)],
            vec![Literal::negative(5), Literal::negative(6)],
        ];
        Problem::new(6, clauses)
    }

    #[test]
    fn pool_finds_sat_on_satisfiable_problem() {
        let problem = php2_2_sat();
        let pool = WorkerPool::new(problem.clone(), WorkerConfig::default());
        let outcomes = pool.run(&[], Some(Duration::from_secs(5)));
        assert!(
            outcomes
                .iter()
                .any(|o| matches!(o, WorkerOutcome::Sat { .. })),
            "expected at least one SAT worker, got {outcomes:?}"
        );
        for o in &outcomes {
            if let WorkerOutcome::Sat { model, .. } = o {
                assert!(problem.validates(model, &[]));
            }
        }
    }

    #[test]
    fn pool_proves_unsat_problem() {
        let problem = php3_2_unsat();
        let pool = WorkerPool::new(problem.clone(), WorkerConfig::default());
        let outcomes = pool.run(&[], Some(Duration::from_secs(5)));
        // Every worker is complete: each must either close its cube (UNSAT) or
        // be aborted by the deadline; no worker may claim SAT on an UNSAT problem.
        assert!(
            outcomes
                .iter()
                .all(|o| !matches!(o, WorkerOutcome::Sat { .. })),
            "no SAT expected, got {outcomes:?}"
        );
        assert!(
            outcomes
                .iter()
                .any(|o| matches!(o, WorkerOutcome::Unsat { .. })),
            "at least one worker should close the root cube, got {outcomes:?}"
        );
    }

    #[test]
    fn cancelled_workers_abort_promptly() {
        let problem = php3_2_unsat();
        let pool = WorkerPool::new(problem.clone(), WorkerConfig::default());
        // Cancel before running: every worker must stop without claiming SAT.
        pool.cancel();
        let outcomes = pool.run(&[], Some(Duration::from_secs(5)));
        assert!(outcomes
            .iter()
            .all(|o| !matches!(o, WorkerOutcome::Sat { .. })));
    }

    #[test]
    fn deadline_aborts_unsatisfiable_search() {
        let problem = php3_2_unsat();
        let pool = WorkerPool::new(problem.clone(), WorkerConfig::default());
        let outcomes = pool.run(&[], Some(Duration::from_millis(1)));
        assert!(outcomes
            .iter()
            .all(|o| !matches!(o, WorkerOutcome::Sat { .. })));
    }

    #[test]
    fn cubes_report_correct_outcomes() {
        // Split PHP(2,2) by pigeon-1's hole choice. Both cubes are actually
        // satisfiable (x1 ⇒ x2=F,x3=F,x4=T; ¬x1 ⇒ x2=T,x3=T,x4=F), so every
        // worker may find SAT. Once the first worker proves SAT it cancels the
        // rest, so peers may legitimately come back `Aborted`. What must never
        // happen is a wrong claim.
        let problem = php2_2_sat();
        let cubes = vec![vec![Literal::positive(1)], vec![Literal::negative(1)]];
        assert!(brute_force(&problem, &cubes[0]), "cube 0 must be SAT");
        assert!(brute_force(&problem, &cubes[1]), "cube 1 must be SAT");

        let cfg = WorkerConfig {
            num_workers: 2,
            ..WorkerConfig::default()
        };
        let pool = WorkerPool::new(problem.clone(), cfg);
        let outcomes = pool.run(&cubes, Some(Duration::from_secs(5)));
        assert_eq!(outcomes.len(), 2);
        let mut saw_sat = false;
        for (i, cube) in cubes.iter().enumerate() {
            let expected = brute_force(&problem, cube);
            match &outcomes[i] {
                WorkerOutcome::Sat { model, .. } => {
                    saw_sat = true;
                    assert!(expected, "cube {i:?} claimed SAT but oracle says UNSAT");
                    assert!(problem.validates(model, cube));
                }
                WorkerOutcome::Unsat { .. } => {
                    assert!(!expected, "cube {i:?} claimed UNSAT but oracle says SAT");
                }
                // A peer proved SAT first and cancelled this worker: fine.
                WorkerOutcome::Aborted { .. } => {}
            }
        }
        assert!(
            saw_sat,
            "at least one worker must prove SAT, got {outcomes:?}"
        );
    }

    /// Import-predicate fuzz: random small CNF, random cubes; every worker's
    /// reported outcome must agree with brute force on F ∧ cube.
    #[test]
    fn import_predicate_fuzz_matches_brute_force() {
        let mut state: u64 = 0x9E3779B97F4A7C15;
        let mut rng = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };

        for round in 0..30u32 {
            let num_vars = 1 + (rng() % 4) as u32; // 1..=4
            let mut clauses: Vec<Vec<Literal>> = Vec::new();
            let num_clauses = 1 + (rng() % 6) as usize;
            for _ in 0..num_clauses {
                let len = 1 + (rng() % 3) as usize;
                let mut clause: Vec<Literal> = (0..len)
                    .map(|_| {
                        let v = 1 + (rng() % num_vars as u64) as u32;
                        if rng() & 1 == 0 {
                            Literal::positive(v)
                        } else {
                            Literal::negative(v)
                        }
                    })
                    .collect();
                clause.sort_unstable();
                clause.dedup();
                clauses.push(clause);
            }
            let problem = Problem::new(num_vars, clauses);

            let num_workers = 2usize;
            let mut cubes: Vec<Vec<Literal>> = Vec::new();
            for _ in 0..num_workers {
                let mut cube: Vec<Literal> = (0..(rng() % 3))
                    .map(|_| {
                        let v = 1 + (rng() % num_vars as u64) as u32;
                        if rng() & 1 == 0 {
                            Literal::positive(v)
                        } else {
                            Literal::negative(v)
                        }
                    })
                    .collect();
                cube.sort_unstable();
                cube.dedup();
                cubes.push(cube);
            }

            let cfg = WorkerConfig {
                num_workers,
                ..WorkerConfig::default()
            };
            let pool = WorkerPool::new(problem.clone(), cfg);
            let outcomes = pool.run(&cubes, Some(Duration::from_secs(5)));

            assert_eq!(outcomes.len(), num_workers);
            for (i, cube) in cubes.iter().enumerate() {
                let expected_sat = brute_force(&problem, cube);
                match &outcomes[i] {
                    WorkerOutcome::Sat { model, .. } => {
                        assert!(
                            expected_sat,
                            "round {round} worker {i}: FALSE SAT claim under {cube:?}"
                        );
                        assert!(problem.validates(model, cube));
                    }
                    WorkerOutcome::Unsat { .. } => {
                        assert!(
                            !expected_sat,
                            "round {round} worker {i}: FALSE UNSAT claim under {cube:?}"
                        );
                    }
                    WorkerOutcome::Aborted { .. } => {
                        // Time-bound aborts are allowed; but we must never have
                        // claimed SAT/UNSAT wrongly above.
                    }
                }
            }
        }
    }
}
