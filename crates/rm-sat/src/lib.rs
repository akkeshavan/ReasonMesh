//! Production CDCL SAT core — Milestone M1.

pub mod assignment;
pub mod bve;
pub mod cdcl;
pub mod classify;
pub mod clause;
pub mod dimacs;
pub mod lookahead;
pub mod model;
pub mod reasoner;
pub mod vmtf;
pub mod watched;
pub mod xor;

pub use cdcl::{BcpStats, CdclSolver, SolveResult};
pub use classify::{analyse as analyse_cnf, DetectedClass, InstanceProfile};
pub use dimacs::{parse_dimacs, DimacsCnf, DimacsError};
pub use model::Model;
pub use reasoner::{make_work_unit, CdclReasoner};
pub use xor::{detect_xor_clauses, xor_density_approx, GjeMatrix, GjeResult, XorClause};
