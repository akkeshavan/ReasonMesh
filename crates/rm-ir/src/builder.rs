//! Lower an `rm_syntax` AST into the interned [`TermDag`]. Free Boolean and
//! bit-vector constants are mapped to fresh variable ids.

use crate::bitvec::Bv;
use crate::dag::{NodeId, Op, TermDag};
use rm_syntax::ast::{BvOp, Term, TermInner};
use rustc_hash::FxHashMap;

/// A lowering context mapping symbol names to variable ids.
#[derive(Default)]
pub struct Builder {
    pub dag: TermDag,
    var_ids: FxHashMap<String, u32>,
    next_var: u32,
}

impl Builder {
    pub fn new() -> Self {
        Builder::default()
    }

    pub fn var_id(&self, name: &str) -> Option<u32> {
        self.var_ids.get(name).copied()
    }

    pub fn all_var_ids(&self) -> Vec<u32> {
        let mut ids: Vec<u32> = self.var_ids.values().copied().collect();
        ids.sort_unstable();
        ids.dedup();
        ids
    }

    fn intern_var(&mut self, name: &str, width: Option<u32>) -> NodeId {
        let id = *self.var_ids.entry(name.to_string()).or_insert_with(|| {
            let id = self.next_var;
            self.next_var += 1;
            id
        });
        match width {
            Some(w) => self.dag.intern_bv_var(id, w),
            None => self.dag.intern_bool_var(id),
        }
    }

    /// Lower a parsed term into the DAG. Returns the node id.
    pub fn lower(&mut self, term: &Term) -> NodeId {
        match &term.inner {
            TermInner::True => self.dag.intern_bool_const(true),
            TermInner::False => self.dag.intern_bool_const(false),
            TermInner::BvLiteral { bits, width } => self
                .dag
                .intern_bv_const(*width, Bv::from_bits(*width, bits.clone())),
            TermInner::Variable(name) => {
                let width = term.sort.as_bitvec();
                self.intern_var(name, width)
            }
            TermInner::BvOp(op, args) => {
                let children: Vec<NodeId> = args.iter().map(|a| self.lower(a)).collect();
                let dag_op = self.map_op(*op);
                self.dag.intern_apply(dag_op, children)
            }
            TermInner::FunCall(name, args) => {
                let children: Vec<NodeId> = args.iter().map(|a| self.lower(a)).collect();
                let width = term.sort.as_bitvec();
                let id = *self.var_ids.entry(name.clone()).or_insert_with(|| {
                    let id = self.next_var;
                    self.next_var += 1;
                    id
                });
                let _ = children;
                match width {
                    Some(w) => self.dag.intern_bv_var(id, w),
                    None => self.dag.intern_bool_var(id),
                }
            }
            TermInner::Not(inner) => {
                let c = self.lower(inner);
                self.dag.intern_apply(Op::Not, vec![c])
            }
            TermInner::And(terms) => {
                let children: Vec<NodeId> = terms.iter().map(|t| self.lower(t)).collect();
                self.dag.intern_apply(Op::And, children)
            }
            TermInner::Or(terms) => {
                let children: Vec<NodeId> = terms.iter().map(|t| self.lower(t)).collect();
                self.dag.intern_apply(Op::Or, children)
            }
            TermInner::Ite(c, t, e) => {
                let cc = self.lower(c);
                let tt = self.lower(t);
                let ee = self.lower(e);
                self.dag.intern_apply(Op::Ite, vec![cc, tt, ee])
            }
            TermInner::Eq(a, b) => {
                let la = self.lower(a);
                let lb = self.lower(b);
                self.dag.intern_apply(Op::Eq, vec![la, lb])
            }
        }
    }

    fn map_op(&self, op: BvOp) -> Op {
        use BvOp::*;
        match op {
            BvNot => Op::BvNot,
            BvNeg => Op::BvNeg,
            BvAdd => Op::BvAdd,
            BvSub => Op::BvSub,
            BvMul => Op::BvMul,
            BvUdiv => Op::BvUdiv,
            BvUrem => Op::BvUrem,
            BvSdiv => Op::BvSdiv,
            BvSrem => Op::BvSrem,
            BvSmod => Op::BvSmod,
            BvAnd => Op::BvAnd,
            BvOr => Op::BvOr,
            BvXor => Op::BvXor,
            BvShl => Op::BvShl,
            BvLshr => Op::BvLshr,
            BvAshr => Op::BvAshr,
            BvUlt => Op::BvUlt,
            BvUle => Op::BvUle,
            BvUgt => Op::BvUgt,
            BvUge => Op::BvUge,
            BvSlt => Op::BvSlt,
            BvSle => Op::BvSle,
            BvSgt => Op::BvSgt,
            BvSge => Op::BvSge,
            Concat => Op::BvConcat,
            Extract { high, low } => Op::BvExtract { hi: high, lo: low },
            ZeroExtend { amount } => Op::BvZeroExtend { amount },
            SignExtend { amount } => Op::BvSignExtend { amount },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dag::Node;
    use rm_syntax::Script;

    fn build(script: &str) -> (Builder, Vec<NodeId>) {
        let s = Script::parse(script).unwrap();
        let mut b = Builder::new();
        let mut roots = Vec::new();
        for a in s.assertions() {
            roots.push(b.lower(a));
        }
        (b, roots)
    }

    #[test]
    fn lowers_boolean_constants() {
        let (b, roots) = build("(assert true)");
        assert!(matches!(b.dag.get(roots[0]), Node::BoolConst(true)));
    }

    #[test]
    fn lower_bv_arithmetic() {
        let (b, roots) = build(
            "(declare-const a (_ BitVec 8))
             (declare-const b (_ BitVec 8))
             (assert (bvult (bvadd a b) #x05))",
        );
        let root = roots[0];
        match b.dag.get(root) {
            Node::Apply { op: Op::BvUlt, .. } => {}
            other => panic!("expected bvult, got {other:?}"),
        }
    }

    #[test]
    fn variables_are_interned() {
        let (b, _) = build("(declare-const a (_ BitVec 8)) (assert (= a #x00))");
        assert!(b.var_id("a").is_some());
        assert!(b.var_id("missing").is_none());
    }

    #[test]
    fn structural_sharing_through_builder() {
        let (b, roots) = build(
            "(declare-const a (_ BitVec 4))
             (declare-const b (_ BitVec 4))
             (assert (= (bvadd a b) (bvadd a b)))",
        );
        let root = roots[0];
        if let Node::Apply {
            op: Op::Eq,
            children,
        } = b.dag.get(root)
        {
            assert_eq!(children[0], children[1]);
        } else {
            panic!("expected Eq");
        }
    }
}
