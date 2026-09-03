//! `rm-api` — high-level solver API for ReasonMesh.
//!
//! # Programmatic usage
//!
//! ```rust,ignore
//! use rm_api::{Context, Solver, SatResult};
//!
//! let ctx = Context::new();
//! let mut solver = Solver::new(&ctx);
//! let x = ctx.bitvec_const("x", 8);
//! solver.assert(&x.bvult(&ctx.bitvec_val(10, 8)));
//! match solver.check() {
//!     SatResult::Sat(model) => println!("x = {:?}", model.get_bitvec("x")),
//!     SatResult::Unsat => println!("unsat"),
//!     SatResult::Unknown(r) => println!("unknown: {r}"),
//! }
//! ```
//!
//! # SMT-LIB 2 text interface
//!
//! ```rust,ignore
//! use rm_api::solve_smtlib;
//! let result = solve_smtlib("(set-logic QF_BV)
//!   (declare-const x (_ BitVec 8))
//!   (assert (bvult x #x0a))
//!   (check-sat)");
//! ```
//!
//! # Proof farm (Regime B)
//!
//! ```rust,ignore
//! use rm_api::pool::{Job, SolverPool};
//! use rm_api::solver::SolverConfig;
//!
//! let pool = SolverPool::new(SolverConfig { num_workers: 8, ..Default::default() });
//! let jobs = obligations.into_iter().map(Job::new).collect();
//! let results = pool.run_all(jobs);
//! ```

pub mod context;
pub mod emit;
pub mod expr;
pub mod ffi;
pub mod model;
pub mod pool;
pub mod solver;
pub mod sort;

pub use context::Context;
pub use expr::Expr;
pub use model::{Model, Value};
pub use pool::{Job, JobResult, SolverPool};
pub use solver::{SatResult, Solver, SolverConfig};

pub use sort::Sort;

use rm_smt::{SmtSolver, SmtStatus};

/// Solve an SMT-LIB 2 script supplied as plain text.
pub fn solve_smtlib(text: &str) -> SatResult {
    solve_smtlib_with_budget(text, u64::MAX)
}

/// Solve an SMT-LIB 2 script with an explicit CDCL conflict budget.
pub fn solve_smtlib_with_budget(text: &str, max_conflicts: u64) -> SatResult {
    match SmtSolver::parse(text).and_then(|s| s.solve(max_conflicts)) {
        Ok(r) => match r.status {
            SmtStatus::Sat => SatResult::Sat(Model::from_raw(r.values)),
            SmtStatus::Unsat => SatResult::Unsat,
            SmtStatus::Unknown => SatResult::Unknown("solver returned unknown".to_owned()),
        },
        Err(e) => SatResult::Unknown(e.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bv_sat_programmatic() {
        let ctx = Context::new();
        let mut solver = Solver::new(&ctx);
        let x = ctx.bitvec_const("x", 8);
        solver.assert(&x.bvult(&ctx.bitvec_val(10, 8)));
        let r = solver.check();
        assert!(r.is_sat(), "expected SAT, got {r:?}");
        let (bits, width) = r.model().unwrap().get_bitvec("x").unwrap();
        assert!(bits < 10, "model value {bits} must be < 10");
        assert_eq!(width, 8);
    }

    #[test]
    fn bv_unsat_programmatic() {
        let ctx = Context::new();
        let mut solver = Solver::new(&ctx);
        let x = ctx.bitvec_const("x", 4);
        solver.assert(&x.eq(&ctx.bitvec_val(0, 4)));
        solver.assert(&x.eq(&ctx.bitvec_val(15, 4)));
        assert!(solver.check().is_unsat());
    }

    #[test]
    fn push_pop_isolates_scope() {
        let ctx = Context::new();
        let mut solver = Solver::new(&ctx);
        let x = ctx.bitvec_const("x", 8);
        solver.assert(&x.bvult(&ctx.bitvec_val(100, 8)));
        solver.push();
        solver.assert(&x.bvult(&ctx.bitvec_val(0, 8)));
        assert!(solver.check().is_unsat());
        solver.pop();
        assert!(solver.check().is_sat());
    }

    #[test]
    fn idl_sat_programmatic() {
        let ctx = Context::new();
        let mut solver = Solver::new(&ctx);
        let x = ctx.int_const("x");
        let y = ctx.int_const("y");
        let five = ctx.int_val(5);
        solver.assert(&x.sub(&y).le(&five));
        assert!(solver.check().is_sat());
    }

    #[test]
    fn solve_smtlib_text() {
        let script = "(set-logic QF_BV)
(declare-const a (_ BitVec 4))
(assert (= a #b0101))
(check-sat)";
        let r = solve_smtlib(script);
        assert!(r.is_sat());
        let (bits, _) = r.model().unwrap().get_bitvec("a").unwrap();
        assert_eq!(bits, 5);
    }

    #[test]
    fn pool_runs_independent_jobs() {
        let pool = SolverPool::new(SolverConfig { num_workers: 4, ..Default::default() });
        let jobs = vec![
            Job::new("(set-logic QF_BV)(declare-const x (_ BitVec 4))(assert (bvult x #x5))(check-sat)").with_label("j0"),
            Job::new("(set-logic QF_BV)(declare-const x (_ BitVec 4))(assert (= x #b0000))(assert (= x #b1111))(check-sat)").with_label("j1"),
        ];
        let results = pool.run_all(jobs);
        assert_eq!(results.len(), 2);
        assert!(results[0].result.is_sat());
        assert!(results[1].result.is_unsat());
    }

    #[test]
    fn parallel_workers_agree() {
        let ctx = Context::new();
        let mut solver = Solver::with_config(
            &ctx,
            SolverConfig { num_workers: 4, ..Default::default() },
        );
        let x = ctx.bitvec_const("x", 8);
        solver.assert(&x.eq(&ctx.bitvec_val(42, 8)));
        let r = solver.check();
        assert!(r.is_sat());
        let (bits, _) = r.model().unwrap().get_bitvec("x").unwrap();
        assert_eq!(bits, 42);
    }
}
