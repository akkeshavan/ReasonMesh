//! Production CDCL SAT core — Milestone M1.

pub mod amo;
pub mod assignment;
pub mod big;
pub mod bve;
pub mod cdcl;
pub mod classify;
pub mod clause;
pub mod dimacs;
pub mod lookahead;
pub mod model;
pub mod parallel;
pub mod reasoner;
pub mod vmtf;
pub mod watched;
pub mod xor;

pub use amo::{amo_preprocess, AmoPreprocessResult};
pub use big::{big_preprocess, substitute as big_substitute, BigPreprocessResult};
pub use cdcl::{BcpStats, CdclSolver, SolveResult, TheorySolver};
pub use classify::{analyse as analyse_cnf, DetectedClass, InstanceProfile};
pub use dimacs::{parse_dimacs, DimacsCnf, DimacsError};
pub use model::Model;
pub use parallel::{ParallelCdclSolver, ParallelConfig, SharedClauseDb};
pub use reasoner::{make_work_unit, CdclReasoner};
pub use xor::{detect_xor_clauses, xor_density_approx, GjeMatrix, GjeResult, XorClause};
