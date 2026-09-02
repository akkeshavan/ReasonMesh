//! SMT-LIB 2.7 AST: terms for the QF_BV fragment.
//!
//! Terms use explicit [`BvOp`] operators rather than raw symbol names so the
//! IR layer can dispatch directly on the operation. Free function symbols
//! (declared with `declare-fun`) are represented by [`Term::FunCall`].

use serde::{Deserialize, Serialize};

use super::sort::SortExpr;

/// A sort-annotated term. Sorts are assigned during parsing from declared
/// signatures and the built-in operator table.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Term {
    pub sort: SortExpr,
    pub inner: TermInner,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TermInner {
    /// The Boolean constants.
    True,
    False,
    /// A bit-vector literal. `bitvec` holds the value bits
    /// (least-significant bit first) and the declared width.
    BvLiteral { bits: Vec<bool>, width: u32 },
    /// A free symbol (declared constant or function argument).
    Variable(String),
    /// Application of a built-in bit-vector operator.
    BvOp(BvOp, Vec<Term>),
    /// Application of a user-declared function symbol.
    FunCall(String, Vec<Term>),
    /// Boolean negation.
    Not(Box<Term>),
    /// Boolean conjunction.
    And(Vec<Term>),
    /// Boolean disjunction.
    Or(Vec<Term>),
    /// Boolean if-then-else.
    Ite(Box<Term>, Box<Term>, Box<Term>),
    /// `(= a b)`. For Bool args this is Boolean iff; for BV args it is
    /// structural equality.
    Eq(Box<Term>, Box<Term>),
}

impl Term {
    /// Literal from a bit-vector value string (`#b0101` or `#x0F`).
    pub fn bv_literal(width: u32, bits: Vec<bool>) -> Term {
        debug_assert_eq!(width as usize, bits.len());
        Term {
            sort: SortExpr::BitVec(width),
            inner: TermInner::BvLiteral { bits, width },
        }
    }

    pub fn var(name: impl Into<String>, sort: SortExpr) -> Term {
        Term {
            sort,
            inner: TermInner::Variable(name.into()),
        }
    }

    pub fn true_() -> Term {
        Term { sort: SortExpr::Bool, inner: TermInner::True }
    }

    pub fn false_() -> Term {
        Term { sort: SortExpr::Bool, inner: TermInner::False }
    }
}

/// Bit-vector operators supported in the QF_BV fragment.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BvOp {
    // Unary
    BvNot,
    BvNeg,
    // Binary arithmetic
    BvAdd,
    BvSub,
    BvMul,
    BvUdiv,
    BvUrem,
    BvSdiv,
    BvSrem,
    BvSmod,
    // Bitwise
    BvAnd,
    BvOr,
    BvXor,
    // Shifts
    BvShl,
    BvLshr,
    BvAshr,
    // Comparisons (result is Bool)
    BvUlt,
    BvUle,
    BvUgt,
    BvUge,
    BvSlt,
    BvSle,
    BvSgt,
    BvSge,
    // Concatenation / extraction
    Concat,
    Extract { high: u32, low: u32 },
    ZeroExtend { amount: u32 },
    SignExtend { amount: u32 },
}

impl BvOp {
    /// Number of argument terms, or None if variadic (concat).
    pub fn arg_count(&self) -> Option<usize> {
        match self {
            BvOp::BvNot | BvOp::BvNeg => Some(1),
            BvOp::Extract { .. } | BvOp::ZeroExtend { .. } | BvOp::SignExtend { .. } => Some(1),
            _ => Some(2),
        }
    }

    pub fn returns_bool(&self) -> bool {
        matches!(
            self,
            BvOp::BvUlt
                | BvOp::BvUle
                | BvOp::BvUgt
                | BvOp::BvUge
                | BvOp::BvSlt
                | BvOp::BvSle
                | BvOp::BvSgt
                | BvOp::BvSge
        )
    }

    pub fn name(&self) -> &'static str {
        match self {
            BvOp::BvNot => "bvnot",
            BvOp::BvNeg => "bvneg",
            BvOp::BvAdd => "bvadd",
            BvOp::BvSub => "bvsub",
            BvOp::BvMul => "bvmul",
            BvOp::BvUdiv => "bvudiv",
            BvOp::BvUrem => "bvurem",
            BvOp::BvSdiv => "bvsdiv",
            BvOp::BvSrem => "bvsrem",
            BvOp::BvSmod => "bvsmod",
            BvOp::BvAnd => "bvand",
            BvOp::BvOr => "bvor",
            BvOp::BvXor => "bvxor",
            BvOp::BvShl => "bvshl",
            BvOp::BvLshr => "bvlshr",
            BvOp::BvAshr => "bvashr",
            BvOp::BvUlt => "bvult",
            BvOp::BvUle => "bvule",
            BvOp::BvUgt => "bvugt",
            BvOp::BvUge => "bvuge",
            BvOp::BvSlt => "bvslt",
            BvOp::BvSle => "bvsle",
            BvOp::BvSgt => "bvsgt",
            BvOp::BvSge => "bvsge",
            BvOp::Concat => "concat",
            BvOp::Extract { .. } => "extract",
            BvOp::ZeroExtend { .. } => "zero_extend",
            BvOp::SignExtend { .. } => "sign_extend",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_width_matches_bits() {
        let t = Term::bv_literal(4, vec![false; 4]);
        assert_eq!(t.sort, SortExpr::BitVec(4));
        match t.inner {
            TermInner::BvLiteral { bits, width } => {
                assert_eq!(bits.len(), 4);
                assert_eq!(width, 4);
            }
            _ => panic!("expected literal"),
        }
    }

    #[test]
    fn op_shape() {
        assert_eq!(BvOp::BvNot.arg_count(), Some(1));
        assert_eq!(BvOp::BvAdd.arg_count(), Some(2));
        assert!(BvOp::BvUlt.returns_bool());
        assert!(!BvOp::BvAdd.returns_bool());
        assert_eq!(BvOp::Extract { high: 3, low: 0 }.name(), "extract");
    }
}