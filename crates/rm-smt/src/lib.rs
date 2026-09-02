//! SMT solver facade: accepts an SMT-LIB script, selects the appropriate
//! theory path (QF_BV, QF_IDL, QF_UF, or QF_UFIDL), and returns a solver result plus model.

pub mod cdclt;
pub mod dl;
pub mod solver;
pub mod uf;

pub use cdclt::{solve_qf_ufidl, NoResult};
pub use dl::{solve_qf_idl, DlStatus};
pub use solver::{SmtError, SmtResult, SmtSolver, SmtStatus};
pub use uf::{solve_qf_uf, UfStatus};
