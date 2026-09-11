//! Lookahead variable selection for cube-and-conquer splitting.
//!
//! Implements a simplified march-style scoring: for each unassigned variable v,
//! probe v=true and v=false via BCP and score by the product of the two forced
//! unit counts.  A conflict on one side is a failed literal (force the other);
//! a conflict on both sides detects UNSAT at root.

use crate::cdcl::CdclSolver;
use rm_akx::literal::{Literal, Var};

/// Pick the best variable to split on from the current solver state (level 0).
///
/// Scores each unassigned variable by `probe_true × probe_false` where a
/// conflict probe scores 1_000_000 (very high, representing a failed literal).
/// Returns `None` when all variables are assigned.
pub fn pick_split_var(solver: &mut CdclSolver) -> Option<Var> {
    let num_vars = solver.num_vars();
    let mut best_var: Option<Var> = None;
    let mut best_score: u64 = 0;

    for v in 1..=num_vars {
        if solver.is_var_assigned(v) {
            continue;
        }
        let probe_t = solver.probe_var(v, true);
        let probe_f = solver.probe_var(v, false);

        let score_t: u64 = if probe_t == u32::MAX { 1_000_000 } else { probe_t as u64 + 1 };
        let score_f: u64 = if probe_f == u32::MAX { 1_000_000 } else { probe_f as u64 + 1 };
        let score = score_t * score_f;

        if score > best_score {
            best_score = score;
            best_var = Some(v);
        }
    }

    best_var
}

/// Generate up to `max_cubes` cubes by recursively splitting to depth `depth`.
///
/// Each returned cube is a `Vec<Literal>` — the complete assumption set a
/// worker should pass to `solve_with_deadline`.  Infeasible branches (detected
/// by BCP) are pruned automatically.
///
/// Call `solver.propagate_units()` before this function to bake in any
/// level-0 unit clauses added for parent-cube assumptions.
pub fn generate_cubes(
    solver: &mut CdclSolver,
    depth: u32,
    max_cubes: usize,
) -> Vec<Vec<Literal>> {
    let mut result = Vec::new();
    let mut path: Vec<Literal> = Vec::new();
    generate_recursive(solver, &mut path, depth, max_cubes, &mut result);
    result
}

fn generate_recursive(
    solver: &mut CdclSolver,
    path: &mut Vec<Literal>,
    remaining_depth: u32,
    max_cubes: usize,
    result: &mut Vec<Vec<Literal>>,
) {
    if result.len() >= max_cubes {
        return;
    }
    if remaining_depth == 0 {
        result.push(path.clone());
        return;
    }

    let split_var = match pick_split_var(solver) {
        Some(v) => v,
        None => {
            // All variables assigned — no further splits possible.
            result.push(path.clone());
            return;
        }
    };

    for &phase in &[true, false] {
        if result.len() >= max_cubes {
            break;
        }
        let lit = if phase {
            Literal::positive(split_var)
        } else {
            Literal::negative(split_var)
        };
        path.push(lit);
        if solver.is_feasible_under_assumptions(path) {
            generate_recursive(solver, path, remaining_depth - 1, max_cubes, result);
        }
        // infeasible branch is pruned — no cube added
        path.pop();
    }
}
