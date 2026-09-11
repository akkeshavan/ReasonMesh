//! Production CDCL SAT core — Milestone M1.

pub mod assignment;
pub mod bve;
pub mod cdcl;
pub mod clause;
pub mod dimacs;
pub mod lookahead;
pub mod model;
pub mod reasoner;
pub mod vmtf;
pub mod watched;

pub use cdcl::{BcpStats, CdclSolver, SolveResult};
pub use dimacs::{parse_dimacs, DimacsCnf, DimacsError};
pub use model::Model;
pub use reasoner::{make_work_unit, CdclReasoner};
