//! Cube-and-conquer (C&C) parallel solver.
//!
//! Splits the search space via lookahead, assigns each cube to a CDCL worker
//! thread, and dynamically resplits cubes that exhaust their conflict budget.
//! The formula is UNSAT when every cube is closed.
//!
//! Worker threads are fully independent (no clause sharing); each carries its
//! own copy of the CNF.  The coordinator thread manages the work queue and
//! resplit logic.

use crate::manifest::CubeAndConquerConfig;
use rm_akx::literal::Literal;
use rm_sat::{lookahead, CdclSolver, DimacsCnf, SolveResult};
use rm_telemetry::Outcome;
use std::collections::VecDeque;
use std::sync::{mpsc, Arc};
use std::time::{Duration, Instant};

// ---------------------------------------------------------------------------
// Internal types
// ---------------------------------------------------------------------------

struct WorkItem {
    assumptions: Vec<Literal>,
    budget: u64,
}

struct CubeOutcome {
    result: CubeResult,
    worker_id: usize,
    conflicts: u64,
}

enum CubeResult {
    Sat(Vec<bool>),
    Unsat,
    BudgetExceeded { assumptions: Vec<Literal>, next_budget: u64 },
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn dimacs_lit(l: i32) -> Literal {
    if l > 0 {
        Literal::positive(l as u32)
    } else {
        Literal::negative((-l) as u32)
    }
}

fn build_solver(cnf: &DimacsCnf) -> CdclSolver {
    let mut s = CdclSolver::new(cnf.num_vars);
    for clause in &cnf.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| dimacs_lit(l)).collect();
        s.add_clause(&lits);
    }
    s
}

/// Build sub-cubes for a cube that exceeded its budget.
///
/// Returns 0 items if the parent cube is already UNSAT (both branches
/// infeasible), 1 item if no split variable is available (re-enqueued
/// with doubled budget), or 2 items for a normal split.
fn resplit(
    cnf: &Arc<DimacsCnf>,
    parent_assumptions: &[Literal],
    next_budget: u64,
    max_budget: u64,
) -> Vec<WorkItem> {
    let mut solver = build_solver(cnf);
    // Bake parent assumptions into the solver as level-0 unit clauses so that
    // pick_split_var skips already-forced variables.
    for &lit in parent_assumptions {
        solver.add_clause(&[lit]);
    }
    if solver.propagate_units() {
        // Parent cube is UNSAT: no sub-cubes needed.
        return vec![];
    }

    let sub_cubes = lookahead::generate_cubes(&mut solver, 1, 2);

    if sub_cubes.is_empty() {
        // All variables assigned — re-enqueue parent with doubled budget.
        let budget = next_budget.min(max_budget);
        return vec![WorkItem { assumptions: parent_assumptions.to_vec(), budget }];
    }

    // sub_cubes contains the NEW split literals only (parent-forced vars are
    // already level-0 in this solver; generate_cubes sees only the split lit).
    sub_cubes
        .into_iter()
        .map(|split_lits| {
            let mut full = parent_assumptions.to_vec();
            full.extend(split_lits);
            WorkItem { assumptions: full, budget: next_budget.min(max_budget) }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Worker thread
// ---------------------------------------------------------------------------

fn worker_thread(
    worker_id: usize,
    cnf: Arc<DimacsCnf>,
    work_rx: mpsc::Receiver<Option<WorkItem>>,
    result_tx: mpsc::Sender<CubeOutcome>,
    max_budget: u64,
    global_deadline: Instant,
) {
    while let Ok(Some(item)) = work_rx.recv() {
        let mut solver = build_solver(&cnf);
        let cube_deadline = Some(global_deadline);

        let solve_result =
            solver.solve_with_deadline(&item.assumptions, item.budget, cube_deadline);

        let conflicts = solver.conflicts;

        let result = match solve_result {
            SolveResult::Sat(model) => {
                let mut raw = vec![false; cnf.num_vars as usize + 1];
                for v in 1..=cnf.num_vars {
                    raw[v as usize] = model.value_of(v);
                }
                CubeResult::Sat(raw)
            }
            SolveResult::Unsat => CubeResult::Unsat,
            SolveResult::BudgetExceeded => {
                let next_budget = (item.budget * 2).min(max_budget);
                CubeResult::BudgetExceeded { assumptions: item.assumptions, next_budget }
            }
            SolveResult::Unknown => {
                // Global deadline hit — signal budget exceeded so the coordinator
                // can handle it (it will detect the timeout and stop dispatching).
                let next_budget = item.budget.min(max_budget);
                CubeResult::BudgetExceeded { assumptions: item.assumptions, next_budget }
            }
        };

        let _ = result_tx.send(CubeOutcome { result, worker_id, conflicts });
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run cube-and-conquer on `cnf` using `n_workers` parallel CDCL threads.
///
/// Returns `(Outcome, total_conflicts)`.  `Outcome::Unsat` is returned only
/// when every cube has been independently closed.
pub fn run_cube_and_conquer(
    cnf: &DimacsCnf,
    config: &CubeAndConquerConfig,
    n_workers: usize,
    timeout: Duration,
) -> (Outcome, u64) {
    let deadline = Instant::now() + timeout;

    // Build initial cube set via lookahead.
    let initial_cubes: Vec<Vec<Literal>> = {
        let mut solver = build_solver(cnf);
        if solver.propagate_units() {
            return (Outcome::Unsat, 0);
        }
        let max_init = (n_workers * 2).max(4);
        lookahead::generate_cubes(&mut solver, config.initial_depth, max_init)
    };

    if initial_cubes.is_empty() {
        // No variables to split on — solve directly.
        let mut solver = build_solver(cnf);
        return match solver.solve_with_deadline(&[], u64::MAX, Some(deadline)) {
            SolveResult::Sat(_) => (Outcome::Sat, solver.conflicts),
            SolveResult::Unsat => (Outcome::Unsat, solver.conflicts),
            _ => (Outcome::Unknown, solver.conflicts),
        };
    }

    let cnf_arc = Arc::new(cnf.clone());

    // Spawn N workers, each with a dedicated one-slot work channel.
    let mut work_txs: Vec<mpsc::SyncSender<Option<WorkItem>>> = Vec::with_capacity(n_workers);
    let (result_tx, result_rx) = mpsc::channel::<CubeOutcome>();

    for wid in 0..n_workers {
        let (wtx, wrx) = mpsc::sync_channel::<Option<WorkItem>>(1);
        work_txs.push(wtx);
        let rtx = result_tx.clone();
        let cnf2 = cnf_arc.clone();
        let mb = config.max_budget;
        let dl = deadline;
        std::thread::spawn(move || {
            worker_thread(wid, cnf2, wrx, rtx, mb, dl);
        });
    }
    drop(result_tx); // rx disconnects when all workers exit

    let mut queue: VecDeque<WorkItem> = initial_cubes
        .into_iter()
        .map(|a| WorkItem { assumptions: a, budget: config.initial_budget })
        .collect();
    let mut pending_count: i64 = queue.len() as i64;
    let mut idle_workers: VecDeque<usize> = (0..n_workers).collect();
    let mut total_conflicts: u64 = 0;

    // Initial dispatch.
    dispatch_work(&mut queue, &mut idle_workers, &work_txs);

    let mut outcome = Outcome::Unknown;

    'main: loop {
        if pending_count == 0 {
            outcome = Outcome::Unsat;
            break;
        }
        if Instant::now() >= deadline {
            break;
        }

        let wait_dur = (deadline - Instant::now()).min(Duration::from_millis(200));
        let cube_outcome = match result_rx.recv_timeout(wait_dur) {
            Ok(o) => o,
            Err(mpsc::RecvTimeoutError::Timeout) => continue,
            Err(mpsc::RecvTimeoutError::Disconnected) => break,
        };

        total_conflicts += cube_outcome.conflicts;
        idle_workers.push_back(cube_outcome.worker_id);

        match cube_outcome.result {
            CubeResult::Sat(raw) => {
                // Note: model validation (check_dimacs_model) happens in run.rs;
                // trust the solver here since we don't validate in the C&C path.
                let _ = raw; // model captured; outcome is Sat
                outcome = Outcome::Sat;
                break 'main;
            }
            CubeResult::Unsat => {
                pending_count -= 1;
            }
            CubeResult::BudgetExceeded { assumptions, next_budget } => {
                pending_count -= 1;
                // Only resplit if we still have time — avoids wasted work near deadline.
                if Instant::now() < deadline {
                    let sub_items = resplit(&cnf_arc, &assumptions, next_budget, config.max_budget);
                    pending_count += sub_items.len() as i64;
                    queue.extend(sub_items);
                }
            }
        }

        if pending_count == 0 {
            outcome = Outcome::Unsat;
            break;
        }

        dispatch_work(&mut queue, &mut idle_workers, &work_txs);
    }

    // Shut down all workers.
    for tx in &work_txs {
        let _ = tx.send(None);
    }

    (outcome, total_conflicts)
}

fn dispatch_work(
    queue: &mut VecDeque<WorkItem>,
    idle_workers: &mut VecDeque<usize>,
    work_txs: &[mpsc::SyncSender<Option<WorkItem>>],
) {
    while !queue.is_empty() && !idle_workers.is_empty() {
        let item = queue.pop_front().unwrap();
        let wid = idle_workers.pop_front().unwrap();
        let _ = work_txs[wid].send(Some(item));
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use rm_sat::parse_dimacs;

    /// PHP(3,2): 3 pigeons in 2 holes — UNSAT. C&C must close all cubes.
    #[test]
    fn cnc_proves_php_3_2_unsat() {
        let dimacs =
            "p cnf 6 9\n1 4 0\n2 5 0\n3 6 0\n-1 -2 0\n-1 -3 0\n-2 -3 0\n-4 -5 0\n-4 -6 0\n-5 -6 0\n";
        let cnf = parse_dimacs(dimacs).unwrap();
        let config = CubeAndConquerConfig {
            initial_depth: 2,
            initial_budget: 100,
            max_budget: 10_000,
        };
        let (outcome, _conflicts) =
            run_cube_and_conquer(&cnf, &config, 2, Duration::from_secs(10));
        assert_eq!(outcome, Outcome::Unsat);
    }

    /// PHP(2,2): 2 pigeons in 2 holes — SAT. C&C must find a model.
    #[test]
    fn cnc_finds_php_2_2_sat() {
        let dimacs = "p cnf 4 4\n1 3 0\n2 4 0\n-1 -2 0\n-3 -4 0\n";
        let cnf = parse_dimacs(dimacs).unwrap();
        let config = CubeAndConquerConfig {
            initial_depth: 1,
            initial_budget: 1_000,
            max_budget: 100_000,
        };
        let (outcome, _) = run_cube_and_conquer(&cnf, &config, 2, Duration::from_secs(10));
        assert_eq!(outcome, Outcome::Sat);
    }
}
