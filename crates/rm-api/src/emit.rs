//! Emit an SMT-LIB 2 script from a list of [`Expr`] assertions.

use crate::expr::{children, Expr, ExprNode};
use crate::Sort;
use std::collections::BTreeMap;

/// Infer the most specific SMT-LIB 2 logic for a set of assertions.
pub(crate) fn detect_logic(assertions: &[Expr]) -> &'static str {
    let mut has_bv = false;
    let mut has_int = false;
    let mut stack: Vec<&Expr> = assertions.iter().collect();
    while let Some(e) = stack.pop() {
        match e.node() {
            ExprNode::Const(_, Sort::BitVec(_))
            | ExprNode::BitVecLit(..)
            | ExprNode::BvAdd(..)
            | ExprNode::BvSub(..)
            | ExprNode::BvMul(..)
            | ExprNode::BvNeg(..)
            | ExprNode::BvAnd(..)
            | ExprNode::BvOr(..)
            | ExprNode::BvXor(..)
            | ExprNode::BvNot(..)
            | ExprNode::BvUlt(..)
            | ExprNode::BvUle(..)
            | ExprNode::BvSlt(..)
            | ExprNode::BvSle(..)
            | ExprNode::BvShl(..)
            | ExprNode::BvLshr(..)
            | ExprNode::BvAshr(..)
            | ExprNode::BvConcat(..)
            | ExprNode::BvExtract(..)
            | ExprNode::BvZeroExt(..)
            | ExprNode::BvSignExt(..) => has_bv = true,

            ExprNode::Const(_, Sort::Int)
            | ExprNode::IntLit(..)
            | ExprNode::Add(..)
            | ExprNode::Sub(..)
            | ExprNode::Mul(..)
            | ExprNode::Neg(..)
            | ExprNode::Lt(..)
            | ExprNode::Le(..)
            | ExprNode::Gt(..)
            | ExprNode::Ge(..) => {
                has_int = true;
            }
            _ => {}
        }
        for child in children(e.node()) {
            stack.push(child);
        }
    }
    if has_bv {
        "QF_BV"
    } else if has_int {
        "QF_IDL"
    } else {
        "QF_UF"
    }
}

/// Emit a complete SMT-LIB 2 script for the given assertions and logic name.
pub(crate) fn emit_smtlib(assertions: &[Expr], logic: &str) -> String {
    let decls = collect_decls(assertions);
    let mut out = String::with_capacity(512);
    out.push_str(&format!("(set-logic {logic})\n"));
    for (name, sort) in &decls {
        out.push_str(&format!("(declare-const {} {})\n", name, sort.smtlib()));
    }
    for a in assertions {
        out.push_str(&format!("(assert {})\n", emit_expr(a)));
    }
    out.push_str("(check-sat)\n(get-model)\n");
    out
}

fn collect_decls(assertions: &[Expr]) -> BTreeMap<String, Sort> {
    let mut decls = BTreeMap::new();
    let mut stack: Vec<&Expr> = assertions.iter().collect();
    while let Some(e) = stack.pop() {
        if let ExprNode::Const(name, sort) = e.node() {
            decls.entry(name.clone()).or_insert_with(|| sort.clone());
        }
        for child in children(e.node()) {
            stack.push(child);
        }
    }
    decls
}

pub(crate) fn emit_expr(expr: &Expr) -> String {
    match expr.node() {
        ExprNode::Const(name, _) => name.clone(),
        ExprNode::BoolLit(b) => if *b { "true" } else { "false" }.to_owned(),
        ExprNode::IntLit(n) => {
            if *n < 0 {
                format!("(- {})", n.unsigned_abs())
            } else {
                n.to_string()
            }
        }
        ExprNode::BitVecLit(v, w) => format!("(_ bv{v} {w})"),

        ExprNode::Not(e) => format!("(not {})", emit_expr(e)),
        ExprNode::And(a, b) => format!("(and {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::Or(a, b) => format!("(or {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::Implies(a, b) => format!("(=> {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::Iff(a, b) => format!("(= {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::Ite(c, t, e) => {
            format!("(ite {} {} {})", emit_expr(c), emit_expr(t), emit_expr(e))
        }
        ExprNode::Eq(a, b) => format!("(= {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::Distinct(a, b) => format!("(distinct {} {})", emit_expr(a), emit_expr(b)),

        ExprNode::Add(a, b) => format!("(+ {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::Sub(a, b) => format!("(- {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::Mul(a, b) => format!("(* {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::Neg(e) => format!("(- {})", emit_expr(e)),
        ExprNode::Lt(a, b) => format!("(< {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::Le(a, b) => format!("(<= {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::Gt(a, b) => format!("(> {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::Ge(a, b) => format!("(>= {} {})", emit_expr(a), emit_expr(b)),

        ExprNode::BvAdd(a, b) => format!("(bvadd {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::BvSub(a, b) => format!("(bvsub {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::BvMul(a, b) => format!("(bvmul {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::BvNeg(e) => format!("(bvneg {})", emit_expr(e)),
        ExprNode::BvAnd(a, b) => format!("(bvand {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::BvOr(a, b) => format!("(bvor {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::BvXor(a, b) => format!("(bvxor {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::BvNot(e) => format!("(bvnot {})", emit_expr(e)),

        ExprNode::BvUlt(a, b) => format!("(bvult {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::BvUle(a, b) => format!("(bvule {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::BvSlt(a, b) => format!("(bvslt {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::BvSle(a, b) => format!("(bvsle {} {})", emit_expr(a), emit_expr(b)),

        ExprNode::BvShl(a, b) => format!("(bvshl {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::BvLshr(a, b) => format!("(bvlshr {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::BvAshr(a, b) => format!("(bvashr {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::BvConcat(a, b) => format!("(concat {} {})", emit_expr(a), emit_expr(b)),
        ExprNode::BvExtract(hi, lo, e) => {
            format!("((_ extract {hi} {lo}) {})", emit_expr(e))
        }
        ExprNode::BvZeroExt(n, e) => format!("((_ zero_extend {n}) {})", emit_expr(e)),
        ExprNode::BvSignExt(n, e) => format!("((_ sign_extend {n}) {})", emit_expr(e)),
    }
}
