use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};

/// Identifier into a `TermDag`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct NodeId(pub u32);

/// A node in the term DAG.
#[derive(Clone, Debug)]
pub enum Node {
    BoolConst(bool),
    BvConst { width: u32, value: u64 },
    Var { name: u32, width: Option<u32> },
    Apply { op: Op, children: Vec<NodeId> },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    And, Or, Not, Xor, Eq,
    BvAnd, BvOr, BvXor, BvNot, BvAdd, BvSub, BvMul,
    BvUlt, BvSlt, BvConcat, BvExtract { hi: u32, lo: u32 },
}

/// Interning DAG: structurally identical nodes share the same `NodeId`.
#[derive(Default)]
pub struct TermDag {
    nodes: Vec<Node>,
    intern: FxHashMap<u64, NodeId>,
}

impl TermDag {
    pub fn len(&self) -> usize { self.nodes.len() }
    pub fn is_empty(&self) -> bool { self.nodes.is_empty() }

    pub fn get(&self, id: NodeId) -> &Node {
        &self.nodes[id.0 as usize]
    }

    pub fn intern_bool_const(&mut self, v: bool) -> NodeId {
        let key = if v { u64::MAX } else { u64::MAX - 1 };
        if let Some(&id) = self.intern.get(&key) { return id; }
        let id = NodeId(self.nodes.len() as u32);
        self.nodes.push(Node::BoolConst(v));
        self.intern.insert(key, id);
        id
    }
}
