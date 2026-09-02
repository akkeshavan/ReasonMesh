//! EUF theory solver: equality and uninterpreted functions with congruence
//! closure (spec §11, T2 milestone).
//!
//! Implements:
//! - Union-find with path compression and union-by-rank (rollback-capable)
//! - Congruence closure via pending-list / use-list propagation
//! - Conflict explanation: returns a minimal unsatisfiable set of equalities
//! - `TheoryLemma` production for AKX knowledge exchange (§7.1)
//!
//! # Soundness
//! The congruence lemma a=c produced from a=b ∧ b=c is a tautology of EUF;
//! it is exported with `assumptions = []` (unconditional) and `trust =
//! Trusted`. Conflict cores produced when the disequality literal ¬(a=b) is
//! asserted but a and b are already merged carry their triggering equality
//! assumptions.

pub mod cc;
pub mod egraph;
pub mod explain;

pub use cc::{CcError, CongruenceClosure};
pub use egraph::{EGraph, ENodeId, FuncId};
pub use explain::{Explanation, ExplanationLit};
