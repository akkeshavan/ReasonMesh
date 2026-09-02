//! Arithmetic theory solver (spec §11, T3 milestone).
//!
//! Currently implements **Quantifier-Free Difference Logic** (QF_IDL / QF_RDL):
//! constraints of the form `x - y ≤ c` over integers (IDL) or rationals (RDL).
//!
//! The solver uses an **incremental Bellman-Ford** algorithm on the difference
//! constraint graph. CDCL(T)-compatible:
//! - `assert_leq(x, y, c, sat_lit)` — add edge x→y with weight c.
//! - `check()` — detect negative cycles; Err(DlError::Conflict) on violation.
//! - `backtrack_to(level)` — undo assertions since level.
//!
//! Conflict explanation: the negative-cycle edge-set (sat lits) is the
//! CDCL conflict clause. Bounds are exported as AKX `BoundKnowledge`.

pub mod bound;
pub mod diff;

pub use bound::{Bound, BoundKind};
pub use diff::{ConflictCore, DiffLogicSolver, DlError, DlResult};
