//! [`Context`] — the root factory for sorts, constants, and literals.

use crate::expr::{Expr, ExprNode};
use crate::Sort;

/// Root factory for expressions and solver sessions.
///
/// A `Context` carries no mutable state; all methods take `&self`.  Multiple
/// [`Solver`](crate::Solver) instances may share the same context.
#[derive(Default)]
pub struct Context;

impl Context {
    pub fn new() -> Self {
        Context
    }

    pub fn bool_const(&self, name: impl Into<String>) -> Expr {
        Expr::new(ExprNode::Const(name.into(), Sort::Bool))
    }

    pub fn int_const(&self, name: impl Into<String>) -> Expr {
        Expr::new(ExprNode::Const(name.into(), Sort::Int))
    }

    pub fn bitvec_const(&self, name: impl Into<String>, width: u32) -> Expr {
        Expr::new(ExprNode::Const(name.into(), Sort::BitVec(width)))
    }

    pub fn bool_val(&self, b: bool) -> Expr {
        Expr::new(ExprNode::BoolLit(b))
    }

    pub fn int_val(&self, n: i64) -> Expr {
        Expr::new(ExprNode::IntLit(n))
    }

    pub fn bitvec_val(&self, value: u64, width: u32) -> Expr {
        Expr::new(ExprNode::BitVecLit(value, width))
    }

    pub fn and(&self, a: &Expr, b: &Expr) -> Expr {
        a.and(b)
    }

    pub fn or(&self, a: &Expr, b: &Expr) -> Expr {
        a.or(b)
    }

    pub fn not(&self, a: &Expr) -> Expr {
        a.not()
    }

    pub fn implies(&self, a: &Expr, b: &Expr) -> Expr {
        a.implies(b)
    }

    pub fn ite(&self, cond: &Expr, then_: &Expr, else_: &Expr) -> Expr {
        cond.ite(then_, else_)
    }

    pub fn eq(&self, a: &Expr, b: &Expr) -> Expr {
        a.eq(b)
    }

    pub fn distinct(&self, a: &Expr, b: &Expr) -> Expr {
        a.distinct(b)
    }
}
