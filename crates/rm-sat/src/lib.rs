//! Production CDCL SAT core — Milestone M1.

pub mod assignment;
pub mod clause;
pub mod cdcl;
pub mod watched;

pub use cdcl::{CdclSolver, SolveResult};
