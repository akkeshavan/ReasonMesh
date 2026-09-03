//! E-graph: term storage for EUF.
//!
//! Terms are represented as e-nodes: a function symbol applied to a list of
//! e-class IDs. Each e-class is identified by an [`ENodeId`]; the union-find
//! in [`CongruenceClosure`] maps IDs to their canonical representative.

use rustc_hash::FxHashMap;
use smallvec::SmallVec;

/// Opaque identifier for an e-node (and, initially, for its e-class).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct ENodeId(pub u32);

/// Opaque identifier for a function/constant symbol.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FuncId(pub u32);

/// An e-node: function symbol + argument e-classes.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct ENode {
    pub func: FuncId,
    /// Canonical argument IDs at the time of insertion (may become stale as
    /// merges happen; the cc updates them via the use-list).
    pub args: SmallVec<[ENodeId; 4]>,
}

/// The e-graph: term storage and interning.
///
/// Terms are interned: two syntactically identical terms (same function,
/// same argument IDs after canonicalization) share one [`ENodeId`].
pub struct EGraph {
    nodes: Vec<ENode>,
    /// Signature (ENode) → existing id. Used for interning and congruence.
    intern: FxHashMap<ENode, ENodeId>,
    /// Symbol name → FuncId (for building terms from strings).
    sym_table: FxHashMap<String, FuncId>,
    /// Reverse: FuncId → name.
    sym_names: Vec<String>,
}

impl EGraph {
    pub fn new() -> Self {
        EGraph {
            nodes: Vec::new(),
            intern: FxHashMap::default(),
            sym_table: FxHashMap::default(),
            sym_names: Vec::new(),
        }
    }

    /// Look up or create a function/constant symbol.
    pub fn intern_func(&mut self, name: &str) -> FuncId {
        if let Some(&id) = self.sym_table.get(name) {
            return id;
        }
        let id = FuncId(self.sym_names.len() as u32);
        self.sym_names.push(name.to_string());
        self.sym_table.insert(name.to_string(), id);
        id
    }

    pub fn func_name(&self, id: FuncId) -> &str {
        &self.sym_names[id.0 as usize]
    }

    /// Add a term. Returns the existing id if already interned.
    pub fn add(&mut self, func: FuncId, args: SmallVec<[ENodeId; 4]>) -> ENodeId {
        let node = ENode { func, args };
        if let Some(&id) = self.intern.get(&node) {
            return id;
        }
        let id = ENodeId(self.nodes.len() as u32);
        self.intern.insert(node.clone(), id);
        self.nodes.push(node);
        id
    }

    /// Add a constant (0-arity function).
    pub fn constant(&mut self, name: &str) -> ENodeId {
        let fid = self.intern_func(name);
        self.add(fid, SmallVec::new())
    }

    /// Add a function application.
    pub fn apply(&mut self, func: &str, args: &[ENodeId]) -> ENodeId {
        let fid = self.intern_func(func);
        let sv: SmallVec<[ENodeId; 4]> = args.iter().copied().collect();
        self.add(fid, sv)
    }

    pub fn node(&self, id: ENodeId) -> &ENode {
        &self.nodes[id.0 as usize]
    }

    pub fn num_nodes(&self) -> usize {
        self.nodes.len()
    }

    /// All e-node IDs (useful for iterating over all terms).
    pub fn all_ids(&self) -> impl Iterator<Item = ENodeId> {
        (0..self.nodes.len() as u32).map(ENodeId)
    }
}

impl Default for EGraph {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intern_constants() {
        let mut g = EGraph::new();
        let a1 = g.constant("a");
        let a2 = g.constant("a");
        let b = g.constant("b");
        assert_eq!(a1, a2);
        assert_ne!(a1, b);
    }

    #[test]
    fn intern_applications() {
        let mut g = EGraph::new();
        let a = g.constant("a");
        let b = g.constant("b");
        let fab1 = g.apply("f", &[a, b]);
        let fab2 = g.apply("f", &[a, b]);
        let fba = g.apply("f", &[b, a]);
        assert_eq!(fab1, fab2);
        assert_ne!(fab1, fba);
    }
}
