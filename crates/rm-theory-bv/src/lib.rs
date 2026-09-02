//! Bit-vector theory (QF_BV): bit-blasting into CNF for the CDCL core and a
//! pure circuit-evaluation path (Milestone M4).

pub mod blaster;
pub mod solver;
pub mod tseitin;

#[cfg(test)]
pub mod differential;

pub use blaster::Blaster;
pub use solver::{BvModel, BvResult, BvSolver};
pub use tseitin::EncodedCnf;
