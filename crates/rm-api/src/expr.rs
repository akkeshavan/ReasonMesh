//! Expression AST for the programmatic solver API.
//!
//! [`Expr`] wraps an `Arc<ExprNode>` so cloning is O(1) and expression sharing
//! is safe across threads.

use crate::Sort;
use std::sync::Arc;

/// A solver expression: an arc-wrapped node that can be cheaply cloned and
/// shared across threads.
#[derive(Clone, Debug)]
pub struct Expr(pub(crate) Arc<ExprNode>);

impl Expr {
    pub(crate) fn new(node: ExprNode) -> Self {
        Expr(Arc::new(node))
    }

    pub fn node(&self) -> &ExprNode {
        &self.0
    }

    pub fn not(&self) -> Self {
        Expr::new(ExprNode::Not(self.clone()))
    }

    pub fn and(&self, other: &Self) -> Self {
        Expr::new(ExprNode::And(self.clone(), other.clone()))
    }

    pub fn or(&self, other: &Self) -> Self {
        Expr::new(ExprNode::Or(self.clone(), other.clone()))
    }

    pub fn implies(&self, other: &Self) -> Self {
        Expr::new(ExprNode::Implies(self.clone(), other.clone()))
    }

    pub fn iff(&self, other: &Self) -> Self {
        Expr::new(ExprNode::Iff(self.clone(), other.clone()))
    }

    pub fn eq(&self, other: &Self) -> Self {
        Expr::new(ExprNode::Eq(self.clone(), other.clone()))
    }

    pub fn distinct(&self, other: &Self) -> Self {
        Expr::new(ExprNode::Distinct(self.clone(), other.clone()))
    }

    pub fn ite(&self, then_: &Self, else_: &Self) -> Self {
        Expr::new(ExprNode::Ite(self.clone(), then_.clone(), else_.clone()))
    }

    pub fn lt(&self, other: &Self) -> Self {
        Expr::new(ExprNode::Lt(self.clone(), other.clone()))
    }

    pub fn le(&self, other: &Self) -> Self {
        Expr::new(ExprNode::Le(self.clone(), other.clone()))
    }

    pub fn gt(&self, other: &Self) -> Self {
        Expr::new(ExprNode::Gt(self.clone(), other.clone()))
    }

    pub fn ge(&self, other: &Self) -> Self {
        Expr::new(ExprNode::Ge(self.clone(), other.clone()))
    }

    pub fn add(&self, other: &Self) -> Self {
        Expr::new(ExprNode::Add(self.clone(), other.clone()))
    }

    pub fn sub(&self, other: &Self) -> Self {
        Expr::new(ExprNode::Sub(self.clone(), other.clone()))
    }

    pub fn mul(&self, other: &Self) -> Self {
        Expr::new(ExprNode::Mul(self.clone(), other.clone()))
    }

    pub fn neg(&self) -> Self {
        Expr::new(ExprNode::Neg(self.clone()))
    }

    pub fn bvadd(&self, other: &Self) -> Self {
        Expr::new(ExprNode::BvAdd(self.clone(), other.clone()))
    }

    pub fn bvsub(&self, other: &Self) -> Self {
        Expr::new(ExprNode::BvSub(self.clone(), other.clone()))
    }

    pub fn bvmul(&self, other: &Self) -> Self {
        Expr::new(ExprNode::BvMul(self.clone(), other.clone()))
    }

    pub fn bvneg(&self) -> Self {
        Expr::new(ExprNode::BvNeg(self.clone()))
    }

    pub fn bvand(&self, other: &Self) -> Self {
        Expr::new(ExprNode::BvAnd(self.clone(), other.clone()))
    }

    pub fn bvor(&self, other: &Self) -> Self {
        Expr::new(ExprNode::BvOr(self.clone(), other.clone()))
    }

    pub fn bvxor(&self, other: &Self) -> Self {
        Expr::new(ExprNode::BvXor(self.clone(), other.clone()))
    }

    pub fn bvnot(&self) -> Self {
        Expr::new(ExprNode::BvNot(self.clone()))
    }

    pub fn bvult(&self, other: &Self) -> Self {
        Expr::new(ExprNode::BvUlt(self.clone(), other.clone()))
    }

    pub fn bvule(&self, other: &Self) -> Self {
        Expr::new(ExprNode::BvUle(self.clone(), other.clone()))
    }

    pub fn bvslt(&self, other: &Self) -> Self {
        Expr::new(ExprNode::BvSlt(self.clone(), other.clone()))
    }

    pub fn bvsle(&self, other: &Self) -> Self {
        Expr::new(ExprNode::BvSle(self.clone(), other.clone()))
    }

    pub fn bvshl(&self, other: &Self) -> Self {
        Expr::new(ExprNode::BvShl(self.clone(), other.clone()))
    }

    pub fn bvlshr(&self, other: &Self) -> Self {
        Expr::new(ExprNode::BvLshr(self.clone(), other.clone()))
    }

    pub fn bvashr(&self, other: &Self) -> Self {
        Expr::new(ExprNode::BvAshr(self.clone(), other.clone()))
    }

    pub fn concat(&self, other: &Self) -> Self {
        Expr::new(ExprNode::BvConcat(self.clone(), other.clone()))
    }

    pub fn extract(&self, hi: u32, lo: u32) -> Self {
        Expr::new(ExprNode::BvExtract(hi, lo, self.clone()))
    }

    pub fn zero_extend(&self, extra_bits: u32) -> Self {
        Expr::new(ExprNode::BvZeroExt(extra_bits, self.clone()))
    }

    pub fn sign_extend(&self, extra_bits: u32) -> Self {
        Expr::new(ExprNode::BvSignExt(extra_bits, self.clone()))
    }
}

/// The concrete expression node. All child references are [`Expr`] (arc-wrapped)
/// so the tree is DAG-safe and clone-cheap.
#[derive(Debug)]
pub enum ExprNode {
    // Leaves
    Const(String, Sort),
    BoolLit(bool),
    IntLit(i64),
    BitVecLit(u64, u32),

    // Boolean connectives
    Not(Expr),
    And(Expr, Expr),
    Or(Expr, Expr),
    Implies(Expr, Expr),
    Iff(Expr, Expr),
    Ite(Expr, Expr, Expr),

    // Polymorphic equality
    Eq(Expr, Expr),
    Distinct(Expr, Expr),

    // Integer arithmetic
    Add(Expr, Expr),
    Sub(Expr, Expr),
    Mul(Expr, Expr),
    Neg(Expr),
    Lt(Expr, Expr),
    Le(Expr, Expr),
    Gt(Expr, Expr),
    Ge(Expr, Expr),

    // Bit-vector arithmetic and bitwise ops
    BvAdd(Expr, Expr),
    BvSub(Expr, Expr),
    BvMul(Expr, Expr),
    BvNeg(Expr),
    BvAnd(Expr, Expr),
    BvOr(Expr, Expr),
    BvXor(Expr, Expr),
    BvNot(Expr),

    // Bit-vector comparisons
    BvUlt(Expr, Expr),
    BvUle(Expr, Expr),
    BvSlt(Expr, Expr),
    BvSle(Expr, Expr),

    // Bit-vector shifts and structural ops
    BvShl(Expr, Expr),
    BvLshr(Expr, Expr),
    BvAshr(Expr, Expr),
    BvConcat(Expr, Expr),
    BvExtract(u32, u32, Expr),
    BvZeroExt(u32, Expr),
    BvSignExt(u32, Expr),
}

/// Returns the direct child [`Expr`]s of a node (no allocation for 0-2 children).
pub(crate) fn children(node: &ExprNode) -> smallvec::SmallVec<[&Expr; 3]> {
    use ExprNode::*;
    match node {
        Const(..) | BoolLit(..) | IntLit(..) | BitVecLit(..) => smallvec::smallvec![],
        Not(e)
        | Neg(e)
        | BvNeg(e)
        | BvNot(e)
        | BvZeroExt(_, e)
        | BvSignExt(_, e)
        | BvExtract(_, _, e) => smallvec::smallvec![e],
        And(a, b)
        | Or(a, b)
        | Implies(a, b)
        | Iff(a, b)
        | Eq(a, b)
        | Distinct(a, b)
        | Add(a, b)
        | Sub(a, b)
        | Mul(a, b)
        | Lt(a, b)
        | Le(a, b)
        | Gt(a, b)
        | Ge(a, b)
        | BvAdd(a, b)
        | BvSub(a, b)
        | BvMul(a, b)
        | BvAnd(a, b)
        | BvOr(a, b)
        | BvXor(a, b)
        | BvUlt(a, b)
        | BvUle(a, b)
        | BvSlt(a, b)
        | BvSle(a, b)
        | BvShl(a, b)
        | BvLshr(a, b)
        | BvAshr(a, b)
        | BvConcat(a, b) => {
            smallvec::smallvec![a, b]
        }
        Ite(c, t, e) => smallvec::smallvec![c, t, e],
    }
}
