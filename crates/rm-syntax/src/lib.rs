//! SMT-LIB 2.7 parser, sort system, and AST for the QF_BV fragment — Milestone M4.

pub mod ast;
pub mod parser;
pub mod s_expr;
pub mod sort;

pub use ast::{BvOp, Term, TermInner};
pub use parser::{Command, Script};
pub use s_expr::{lex, parse_expr, parse_program, Atom, SExpr, Token};
pub use sort::SortExpr;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ParseError {
    #[error("lex error: {0}")]
    Lex(#[from] s_expr::LexError),
    #[error("s-expression error: {0}")]
    SExpr(#[from] s_expr::SExprError),
    #[error("unexpected token at offset {offset}: {message}")]
    UnexpectedToken { offset: usize, message: String },
    #[error("sort mismatch: expected {expected}, got {got}")]
    SortMismatch { expected: String, got: String },
    #[error("undefined symbol: {0}")]
    UndefinedSymbol(String),
    #[error("invalid sort: {text}")]
    InvalidSort { text: String },
    /// A bit-vector width n for `(_ BitVec n)` that cannot be represented.
    #[error("sort width too large: {0}")]
    SortWidth(u128),
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::TermInner;

    #[test]
    fn roundtrip_simple_qf_bv() {
        let script = Script::parse(concat!(
            "(set-logic QF_BV)\n",
            "(declare-const x (_ BitVec 4))\n",
            "(assert (bvult x #b0111))\n",
            "(check-sat)\n",
        ))
        .unwrap();
        assert_eq!(script.commands.len(), 4);
        assert!(matches!(script.commands[0], Command::SetLogic(_)));
        assert!(matches!(script.commands[2], Command::Assert(_)));
    }

    #[test]
    fn parse_error_on_malformed() {
        assert!(Script::parse("(assert").is_err());
        assert!(Script::parse("(assert (= x)))").is_err());
    }

    #[test]
    fn term_has_sorts() {
        let script = Script::parse("(declare-const x (_ BitVec 8)) (assert (= x #x2A))").unwrap();
        let Command::Assert(t) = &script.commands[1] else {
            panic!()
        };
        match &t.inner {
            TermInner::Eq(l, r) => {
                assert_eq!(l.sort, SortExpr::BitVec(8));
                assert_eq!(r.sort, SortExpr::BitVec(8));
            }
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn bool_constants() {
        let script = Script::parse("(assert true)").unwrap();
        let Command::Assert(t) = &script.commands[0] else {
            panic!()
        };
        assert!(matches!(t.inner, TermInner::True));
    }
}
