//! SMT solver facade: accepts an SMT-LIB script, selects the appropriate
//! theory path (QF_BV or QF_IDL), and returns a solver result plus model.

pub mod dl;
pub mod solver;

pub use dl::{solve_qf_idl, DlStatus};
pub use solver::{SmtError, SmtResult, SmtSolver, SmtStatus};
