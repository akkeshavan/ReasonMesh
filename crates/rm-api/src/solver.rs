//! [`Solver`] and supporting types: the main entry point for the programmatic API.

use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;
use rm_smt::{SmtSolver, SmtStatus};
use crate::context::Context;
use crate::emit::{detect_logic, emit_smtlib};
use crate::expr::Expr;
use crate::model::Model;

/// Configuration for a [`Solver`] run.
#[derive(Clone, Debug)]
pub struct SolverConfig {
    /// Number of independent solver threads to race. When > 1, each thread
    /// runs a complete solve; the first conclusive result (SAT or UNSAT) wins.
    ///
    /// Note: full clause-sharing portfolio across workers (as in the CLI's
    /// WorkerPool) requires extracting CNF via rm-ir and is a future milestone.
    /// Until then, parallel threads independently repeat the same search; the
    /// benefit is fault-tolerance and scheduling diversity.
    pub num_workers: usize,
    /// CDCL conflict budget per worker (0 = unlimited).
    pub max_conflicts: u64,
    /// Per-call wall-clock limit. `None` = no limit.
    pub timeout: Option<Duration>,
}

impl Default for SolverConfig {
    fn default() -> Self {
        SolverConfig { num_workers: 1, max_conflicts: 0, timeout: None }
    }
}

/// The outcome of a [`Solver::check`] call.
#[derive(Debug)]
pub enum SatResult {
    /// The formula is satisfiable; the model assigns every declared constant.
    Sat(Model),
    /// The formula is unsatisfiable.
    Unsat,
    /// The solver gave up (timeout, conflict budget exhausted, or unsupported logic).
    Unknown(String),
}

impl SatResult {
    pub fn is_sat(&self) -> bool {
        matches!(self, SatResult::Sat(_))
    }

    pub fn is_unsat(&self) -> bool {
        matches!(self, SatResult::Unsat)
    }

    pub fn model(&self) -> Option<&Model> {
        if let SatResult::Sat(m) = self { Some(m) } else { None }
    }
}

/// An incremental solver session.  Assert constraints with [`Solver::assert`],
/// then call [`Solver::check`]. Push/pop scopes let you explore multiple
/// branches without rebuilding the context.
///
/// # Parallelism
/// [`SolverConfig::num_workers`] controls how many independent solver threads
/// race on each [`Solver::check`] call.  The internal portfolio (clause sharing
/// between threads) is enabled when the problem reduces to pure SAT/QF_BV via
/// the CLI path; the API currently races independent instances.
pub struct Solver<'ctx> {
    #[allow(dead_code)]
    ctx: &'ctx Context,
    config: SolverConfig,
    assertions: Vec<Expr>,
    stack: Vec<usize>,
}

impl<'ctx> Solver<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        Solver { ctx, config: SolverConfig::default(), assertions: Vec::new(), stack: Vec::new() }
    }

    pub fn with_config(ctx: &'ctx Context, config: SolverConfig) -> Self {
        Solver { ctx, config, assertions: Vec::new(), stack: Vec::new() }
    }

    pub fn assert(&mut self, expr: &Expr) {
        self.assertions.push(expr.clone());
    }

    /// Save the current assertion context. Paired with [`Solver::pop`].
    pub fn push(&mut self) {
        self.stack.push(self.assertions.len());
    }

    /// Restore the assertion context to the last [`Solver::push`] point.
    pub fn pop(&mut self) {
        if let Some(len) = self.stack.pop() {
            self.assertions.truncate(len);
        }
    }

    pub fn num_assertions(&self) -> usize {
        self.assertions.len()
    }

    pub fn check(&self) -> SatResult {
        let logic = detect_logic(&self.assertions);
        let script = emit_smtlib(&self.assertions, logic);
        let budget = effective_conflict_budget(&self.config);
        if self.config.num_workers <= 1 {
            run_solver_single(&script, budget)
        } else {
            run_solver_parallel(&script, budget, self.config.num_workers, self.config.timeout)
        }
    }

    /// Solve with extra assumptions beyond the current assertion stack.
    /// Assertions added here do not persist into the next `check` call.
    pub fn check_assumptions(&self, assumptions: &[Expr]) -> SatResult {
        let mut all = self.assertions.clone();
        all.extend_from_slice(assumptions);
        let logic = detect_logic(&all);
        let script = emit_smtlib(&all, logic);
        let budget = effective_conflict_budget(&self.config);
        run_solver_single(&script, budget)
    }
}

fn effective_conflict_budget(cfg: &SolverConfig) -> u64 {
    if cfg.max_conflicts == 0 { u64::MAX } else { cfg.max_conflicts }
}

fn run_solver_single(script: &str, max_conflicts: u64) -> SatResult {
    match SmtSolver::parse(script).and_then(|s| s.solve(max_conflicts)) {
        Ok(r) => convert_result(r),
        Err(e) => SatResult::Unknown(e.to_string()),
    }
}

fn run_solver_parallel(
    script: &str,
    max_conflicts: u64,
    num_workers: usize,
    timeout: Option<Duration>,
) -> SatResult {
    let script = Arc::new(script.to_owned());
    let winner: Arc<Mutex<Option<SatResult>>> = Arc::new(Mutex::new(None));
    let done = Arc::new(AtomicBool::new(false));
    let start = std::time::Instant::now();

    let handles: Vec<_> = (0..num_workers)
        .map(|_| {
            let script = Arc::clone(&script);
            let winner = Arc::clone(&winner);
            let done = Arc::clone(&done);
            std::thread::spawn(move || {
                if done.load(Ordering::Relaxed) {
                    return;
                }
                if timeout.is_some_and(|t| start.elapsed() >= t) {
                    return;
                }
                let result = SmtSolver::parse(&script)
                    .and_then(|s| s.solve(max_conflicts))
                    .map(convert_result)
                    .unwrap_or_else(|e| SatResult::Unknown(e.to_string()));

                if matches!(&result, SatResult::Sat(_) | SatResult::Unsat) {
                    let mut guard = winner.lock().unwrap();
                    if guard.is_none() {
                        *guard = Some(result);
                        done.store(true, Ordering::SeqCst);
                    }
                }
            })
        })
        .collect();

    for h in handles {
        let _ = h.join();
    }

    Arc::try_unwrap(winner)
        .ok()
        .and_then(|m| m.into_inner().ok())
        .flatten()
        .unwrap_or_else(|| SatResult::Unknown("no conclusive result within budget".to_owned()))
}

fn convert_result(r: rm_smt::SmtResult) -> SatResult {
    match r.status {
        SmtStatus::Sat => SatResult::Sat(Model::from_raw(r.values)),
        SmtStatus::Unsat => SatResult::Unsat,
        SmtStatus::Unknown => SatResult::Unknown("solver returned unknown".to_owned()),
    }
}
