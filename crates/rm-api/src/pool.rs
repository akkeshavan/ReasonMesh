//! [`SolverPool`] — concurrent dispatch of independent proof obligations
//! (Regime B: proof farm for 1000s of independent Lean subgoals).
//!
//! Each job is solved by an independent [`SmtSolver`] instance. Jobs that
//! arrive while all slots are busy queue and run as slots free up.

use crate::model::Model;
use crate::solver::{SatResult, SolverConfig};
use rm_smt::SmtSolver;
use rm_smt::SmtStatus;
use std::sync::{Arc, Mutex};

/// A queued proof obligation.
pub struct Job {
    /// SMT-LIB 2 script text.
    pub script: String,
    /// Optional label for telemetry / logging.
    pub label: Option<String>,
}

impl Job {
    pub fn new(script: impl Into<String>) -> Self {
        Job {
            script: script.into(),
            label: None,
        }
    }

    pub fn with_label(mut self, label: impl Into<String>) -> Self {
        self.label = Some(label.into());
        self
    }
}

/// The result of one [`Job`] in a pool run.
#[derive(Debug)]
pub struct JobResult {
    pub label: Option<String>,
    pub result: SatResult,
}

/// Concurrent solver pool for independent proof obligations.
///
/// `SolverPool::run_all` dispatches every job to a thread pool of size
/// `num_workers`, collects all results, and returns them in job order.
pub struct SolverPool {
    config: SolverConfig,
}

impl SolverPool {
    pub fn new(config: SolverConfig) -> Self {
        SolverPool { config }
    }

    /// Solve all jobs concurrently (up to `num_workers` at a time) and return
    /// results in submission order.
    pub fn run_all(&self, jobs: Vec<Job>) -> Vec<JobResult> {
        let max_conflicts = if self.config.max_conflicts == 0 {
            u64::MAX
        } else {
            self.config.max_conflicts
        };
        let concurrency = self.config.num_workers.max(1);
        let jobs = Arc::new(Mutex::new(jobs.into_iter().enumerate().collect::<Vec<_>>()));
        let results: Arc<Mutex<Vec<Option<JobResult>>>> = Arc::new(Mutex::new(Vec::new()));

        {
            let n = jobs.lock().unwrap().len();
            results.lock().unwrap().resize_with(n, || None);
        }

        let handles: Vec<_> = (0..concurrency)
            .map(|_| {
                let jobs = Arc::clone(&jobs);
                let results = Arc::clone(&results);
                std::thread::spawn(move || loop {
                    let job = {
                        let mut q = jobs.lock().unwrap();
                        if q.is_empty() {
                            break;
                        }
                        q.remove(0)
                    };
                    let (idx, job) = job;
                    let result = solve_job(&job.script, max_conflicts);
                    let jr = JobResult {
                        label: job.label,
                        result,
                    };
                    results.lock().unwrap()[idx] = Some(jr);
                })
            })
            .collect();

        for h in handles {
            let _ = h.join();
        }

        Arc::try_unwrap(results)
            .unwrap()
            .into_inner()
            .unwrap()
            .into_iter()
            .map(|r| {
                r.unwrap_or_else(|| JobResult {
                    label: None,
                    result: SatResult::Unknown("job did not complete".to_owned()),
                })
            })
            .collect()
    }
}

fn solve_job(script: &str, max_conflicts: u64) -> SatResult {
    match SmtSolver::parse(script).and_then(|s| s.solve(max_conflicts)) {
        Ok(r) => match r.status {
            SmtStatus::Sat => SatResult::Sat(Model::from_raw(r.values)),
            SmtStatus::Unsat => SatResult::Unsat,
            SmtStatus::Unknown => SatResult::Unknown("solver returned unknown".to_owned()),
        },
        Err(e) => SatResult::Unknown(e.to_string()),
    }
}
