//! SMT solver facade: accepts an SMT-LIB script, selects the appropriate
//! theory path (QF_BV today), and returns a solver result plus model.

pub mod solver;

pub use solver::{SmtError, SmtResult, SmtSolver, SmtStatus};
