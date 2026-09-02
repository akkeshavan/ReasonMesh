//! Interned term DAG and Boolean/circuit intermediate representation
//! (Milestone M4). The front end lowers an `rm_syntax` AST into the word-level
//! `TermDag`; the circuit path lowers bit-level Boolean gates into a
//! `Circuit` for batching.

pub mod bitvec;
pub mod builder;
pub mod circuit;
pub mod dag;

pub use bitvec::Bv;
pub use builder::Builder;
pub use circuit::{Circuit, Gate, GateId};
pub use dag::{Node, NodeId, Op, TermDag};
