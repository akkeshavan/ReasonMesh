//! SMT-LIB 2.7 parser, sort system, and AST.
//! Milestone M4 — stub.

pub mod ast;
pub mod sort;

#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    #[error("unexpected token at offset {offset}: {message}")]
    UnexpectedToken { offset: usize, message: String },
    #[error("sort mismatch: expected {expected}, got {got}")]
    SortMismatch { expected: String, got: String },
    #[error("undefined symbol: {0}")]
    UndefinedSymbol(String),
}
