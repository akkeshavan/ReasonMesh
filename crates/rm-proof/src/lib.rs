//! rm-proof — independent validation and proof tooling.
//!
//! This crate is deliberately decoupled from solver internals so that SAT
//! models and (in later milestones) UNSAT certificates can be checked by code
//! that shares no logic with the solver itself.

pub mod model;

pub use model::{check_dimacs_model, ModelCheckError};
