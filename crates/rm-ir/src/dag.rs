//! Interned term DAG: the word-level intermediate representation shared by
//! the front end, bit-blaster, and circuit path. Structurally identical
//! subterms are interned to a single [`NodeId`].

use crate::bitvec::Bv;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};

/// Identifier into a `TermDag`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct NodeId(pub u32);

/// A node in the term DAG.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Node {
    BoolConst(bool),
    BvConst {
        width: u32,
        value: Bv,
    },
    /// A Boolean variable. `width: None`.
    BoolVar {
        id: u32,
    },
    /// A bit-vector variable of `width` bits.
    BvVar {
        id: u32,
        width: u32,
    },
    Apply {
        op: Op,
        children: Vec<NodeId>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Op {
    /// Boolean operators.
    And,
    Or,
    Not,
    Xor,
    /// Bit-vector equality (structural, per-bit).
    Eq,
    /// Word-level bit-vector operators.
    BvNot,
    BvNeg,
    BvAdd,
    BvSub,
    BvMul,
    BvUdiv,
    BvUrem,
    BvSdiv,
    BvSrem,
    BvSmod,
    BvAnd,
    BvOr,
    BvXor,
    BvShl,
    BvLshr,
    BvAshr,
    /// Comparisons (result is Bool).
    BvUlt,
    BvUle,
    BvUgt,
    BvUge,
    BvSlt,
    BvSle,
    BvSgt,
    BvSge,
    /// `(concat a b)` — result width is the sum of operand widths.
    BvConcat,
    /// `(extract hi lo x)`.
    BvExtract {
        hi: u32,
        lo: u32,
    },
    /// `(zero_extend n x)` / `(sign_extend n x)`.
    BvZeroExtend {
        amount: u32,
    },
    BvSignExtend {
        amount: u32,
    },
    /// `(ite c t e)` — result width matches the then/else branches.
    Ite,
}

/// Interning DAG: structurally identical nodes share the same `NodeId`.
#[derive(Default)]
pub struct TermDag {
    nodes: Vec<Node>,
    intern: FxHashMap<Node, NodeId>,
}

impl TermDag {
    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn get(&self, id: NodeId) -> &Node {
        &self.nodes[id.0 as usize]
    }

    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }

    /// Intern any node, returning its canonical id.
    pub fn intern(&mut self, node: Node) -> NodeId {
        if let Some(&id) = self.intern.get(&node) {
            return id;
        }
        let id = NodeId(self.nodes.len() as u32);
        self.nodes.push(node.clone());
        self.intern.insert(node, id);
        id
    }

    pub fn intern_bool_const(&mut self, v: bool) -> NodeId {
        self.intern(Node::BoolConst(v))
    }

    pub fn intern_bv_const(&mut self, width: u32, value: Bv) -> NodeId {
        debug_assert_eq!(width as usize, value.len());
        self.intern(Node::BvConst { width, value })
    }

    pub fn intern_bool_var(&mut self, id: u32) -> NodeId {
        self.intern(Node::BoolVar { id })
    }

    pub fn intern_bv_var(&mut self, id: u32, width: u32) -> NodeId {
        self.intern(Node::BvVar { id, width })
    }

    pub fn intern_apply(&mut self, op: Op, children: Vec<NodeId>) -> NodeId {
        self.intern(Node::Apply { op, children })
    }

    /// Structural sharing test: interning the same node twice yields one id.
    pub fn assert_canonical(&self, a: NodeId, b: NodeId) -> bool {
        a == b
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interning_shares_bool_consts() {
        let mut dag = TermDag::default();
        let a = dag.intern_bool_const(true);
        let b = dag.intern_bool_const(true);
        let c = dag.intern_bool_const(false);
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(dag.len(), 2);
    }

    #[test]
    fn interning_shares_apply() {
        let mut dag = TermDag::default();
        let x = dag.intern_bool_var(1);
        let y = dag.intern_bool_var(2);
        let n1 = dag.intern_apply(Op::And, vec![x, y]);
        let n2 = dag.intern_apply(Op::And, vec![x, y]);
        let n3 = dag.intern_apply(Op::Or, vec![x, y]);
        assert_eq!(n1, n2);
        assert_ne!(n1, n3);
    }

    #[test]
    fn bv_var_and_const() {
        let mut dag = TermDag::default();
        let v = dag.intern_bv_var(7, 4);
        assert_eq!(dag.get(v), &Node::BvVar { id: 7, width: 4 });
        let c = dag.intern_bv_const(4, Bv::from_u64(10, 4));
        assert!(matches!(dag.get(c), Node::BvConst { width: 4, .. }));
    }
}
