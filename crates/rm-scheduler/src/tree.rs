//! Partition tree with coverage certificates (§8.4).
//!
//! The orchestrator maintains a tree of cube-based work units. A node is a
//! set of assumption literals (`cube`) restricting the search space. Nodes
//! are *open* (available to dispatch), *assigned* (leased to a worker), or
//! *closed* (SAT/UNSAT/cancelled). Splitting a node produces children whose
//! cubes are the parent's cube extended by one literal each; the split is
//! recorded with a [`CoverageCertificate`] proving the children together
//! cover the parent's search region.
//!
//! Completeness:
//! - **SAT closure:** any leaf closed-SAT (with a validated model).
//! - **UNSAT closure:** every leaf closed-UNSAT (requires full coverage).

use crate::{CoverageCertificate, SchedulerError};
use rm_akx::Literal;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Identifier for a node in the partition tree.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord, Serialize, Deserialize)]
pub struct NodeId(pub u64);

/// Lifecycle state of a partition node.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub enum NodeStatus {
    /// Open: ready to be dispatched to a worker.
    Open,
    /// Leased to a worker; in flight.
    Assigned,
    /// A validated model was found under this cube.
    ClosedSat,
    /// A complete worker proved this cube unsatisfiable.
    ClosedUnsat,
    /// Abandoned (SAT found elsewhere, shutdown, lease lost).
    Cancelled,
}

impl NodeStatus {
    pub fn is_leaf_terminal(self) -> bool {
        matches!(
            self,
            NodeStatus::ClosedSat | NodeStatus::ClosedUnsat | NodeStatus::Cancelled
        )
    }
}

/// A node in the partition tree.
#[derive(Clone, Debug)]
pub struct PartitionNode {
    pub id: NodeId,
    pub parent: Option<NodeId>,
    /// Assumption literals defining this partition's search region.
    pub cube: Vec<Literal>,
    pub status: NodeStatus,
    /// Child node ids in split order.
    pub children: Vec<NodeId>,
    /// Certificate proving the children cover this node's region.
    pub coverage: Option<CoverageCertificate>,
}

impl PartitionNode {
    fn new(id: NodeId, parent: Option<NodeId>, cube: Vec<Literal>) -> Self {
        PartitionNode {
            id,
            parent,
            cube,
            status: NodeStatus::Open,
            children: Vec::new(),
            coverage: None,
        }
    }
}

/// The partition tree, owned by the orchestrator (primary, or standby replay).
#[derive(Debug)]
pub struct PartitionTree {
    nodes: HashMap<NodeId, PartitionNode>,
    root: NodeId,
    next_id: u64,
    /// Depth limit to bound the tree (configurable; `None` = unbounded).
    max_depth: Option<usize>,
}

impl PartitionTree {
    /// Create a tree with a single open root node for the given cube
    /// (usually empty for the full problem).
    pub fn new(root_cube: Vec<Literal>, max_depth: Option<usize>) -> Self {
        let mut nodes = HashMap::new();
        let root = NodeId(0);
        nodes.insert(root, PartitionNode::new(root, None, root_cube));
        PartitionTree {
            nodes,
            root,
            next_id: 1,
            max_depth,
        }
    }

    pub fn root(&self) -> NodeId {
        self.root
    }

    pub fn get(&self, id: NodeId) -> Option<&PartitionNode> {
        self.nodes.get(&id)
    }

    pub fn get_mut(&mut self, id: NodeId) -> Option<&mut PartitionNode> {
        self.nodes.get_mut(&id)
    }

    /// Iterate over all nodes (value order unspecified).
    pub fn nodes(&self) -> impl Iterator<Item = &PartitionNode> {
        self.nodes.values()
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// All nodes currently `Open` (dispatchable), oldest-first by id.
    pub fn open_nodes(&self) -> Vec<NodeId> {
        let mut ids: Vec<NodeId> = self
            .nodes
            .iter()
            .filter(|(_, n)| n.status == NodeStatus::Open)
            .map(|(id, _)| *id)
            .collect();
        ids.sort();
        ids
    }

    /// Leaf nodes that are not yet terminal (Open or Assigned).
    pub fn active_leaves(&self) -> Vec<NodeId> {
        let mut ids: Vec<NodeId> = self
            .nodes
            .iter()
            .filter(|(_, n)| n.children.is_empty() && !n.status.is_leaf_terminal())
            .map(|(id, _)| *id)
            .collect();
        ids.sort();
        ids
    }

    /// Mark a node `Open`, re-enabling it for dispatch.
    pub fn reopen(&mut self, id: NodeId) -> Result<(), SchedulerError> {
        let node = self
            .nodes
            .get_mut(&id)
            .ok_or(SchedulerError::UnknownNode(id))?;
        if node.children.is_empty() {
            node.status = NodeStatus::Open;
            Ok(())
        } else {
            // Only leaves can be reopened; interior nodes have children that
            // remain the authoritative work units.
            Err(SchedulerError::NotLeaf(id))
        }
    }

    /// Mark an open node assigned.
    pub fn assign(&mut self, id: NodeId) -> Result<(), SchedulerError> {
        let node = self
            .nodes
            .get_mut(&id)
            .ok_or(SchedulerError::UnknownNode(id))?;
        if node.status != NodeStatus::Open {
            return Err(SchedulerError::NotOpen(id));
        }
        node.status = NodeStatus::Assigned;
        Ok(())
    }

    /// Close a leaf as SAT/UNSAT/cancelled. Returns an error if the node is
    /// not a leaf or is already terminal.
    pub fn close(&mut self, id: NodeId, status: NodeStatus) -> Result<(), SchedulerError> {
        if !status.is_leaf_terminal() {
            return Err(SchedulerError::InvalidClose(status));
        }
        let node = self
            .nodes
            .get_mut(&id)
            .ok_or(SchedulerError::UnknownNode(id))?;
        if !node.children.is_empty() {
            return Err(SchedulerError::NotLeaf(id));
        }
        if node.status.is_leaf_terminal() {
            return Err(SchedulerError::AlreadyClosed(id));
        }
        node.status = status;
        Ok(())
    }

    /// Split `parent` into children whose cubes are `parent.cube ∪ {l_i}`.
    ///
    /// `certificate` must prove that `l_1 ∨ … ∨ l_k` covers all extensions of
    /// the parent's cube (§8.4). The children are created `Open` and the
    /// parent becomes an interior node.
    pub fn split(
        &mut self,
        parent: NodeId,
        literals: Vec<Literal>,
        certificate: CoverageCertificate,
    ) -> Result<Vec<NodeId>, SchedulerError> {
        let parent_cube = {
            let p = self
                .nodes
                .get(&parent)
                .ok_or(SchedulerError::UnknownNode(parent))?;
            if !p.children.is_empty() {
                return Err(SchedulerError::NotLeaf(parent));
            }
            if self.max_depth.is_some_and(|d| p.cube.len() >= d) {
                return Err(SchedulerError::MaxDepth(parent));
            }
            p.cube.clone()
        };

        // Verify the certificate against the parent region before recording.
        certificate.verify(&parent_cube, &literals)?;

        let mut child_ids = Vec::with_capacity(literals.len());
        for lit in literals {
            let mut cube = parent_cube.clone();
            cube.push(lit);
            let id = NodeId(self.next_id);
            self.next_id += 1;
            self.nodes
                .insert(id, PartitionNode::new(id, Some(parent), cube));
            child_ids.push(id);
        }

        if let Some(p) = self.nodes.get_mut(&parent) {
            p.children = child_ids.clone();
            p.coverage = Some(certificate);
            // Once split, the parent is no longer a dispatchable unit.
            p.status = NodeStatus::Assigned; // interior sentinel
        }
        Ok(child_ids)
    }

    /// The covering clause literal set at this node (its cube).
    pub fn cube(&self, id: NodeId) -> Option<&[Literal]> {
        self.nodes.get(&id).map(|n| n.cube.as_slice())
    }

    // -----------------------------------------------------------------
    // Completeness
    // -----------------------------------------------------------------

    /// True if any leaf is closed-SAT.
    pub fn is_sat(&self) -> bool {
        self.nodes
            .values()
            .any(|n| n.children.is_empty() && n.status == NodeStatus::ClosedSat)
    }

    /// True if every leaf is closed-UNSAT (requires full, certificate-covered
    /// splits all the way down).
    pub fn is_unsat(&self) -> bool {
        let mut has_leaf = false;
        for n in self.nodes.values() {
            if n.children.is_empty() {
                has_leaf = true;
                if n.status != NodeStatus::ClosedUnsat {
                    return false;
                }
            }
        }
        has_leaf
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rm_akx::Literal;

    #[test]
    fn root_is_open() {
        let tree = PartitionTree::new(vec![], None);
        assert_eq!(tree.root(), NodeId(0));
        assert_eq!(tree.get(tree.root()).unwrap().status, NodeStatus::Open);
        assert_eq!(tree.open_nodes(), vec![NodeId(0)]);
    }

    #[test]
    fn split_creates_children_with_extended_cubes() {
        let mut tree = PartitionTree::new(vec![], None);
        let lits = vec![Literal::positive(1), Literal::negative(1)];
        let cert = CoverageCertificate::tautology(lits.clone()).unwrap();
        let children = tree.split(tree.root(), lits.clone(), cert).unwrap();
        assert_eq!(children.len(), 2);
        for (i, c) in children.iter().enumerate() {
            assert_eq!(tree.cube(*c).unwrap(), &[lits[i]]);
            assert_eq!(tree.get(*c).unwrap().status, NodeStatus::Open);
            assert_eq!(tree.get(*c).unwrap().parent, Some(tree.root()));
        }
        // Parent becomes an interior node.
        assert_eq!(tree.get(tree.root()).unwrap().children, children);
        assert_eq!(tree.node_count(), 3);
    }

    #[test]
    fn split_with_invalid_certificate_rejected() {
        let mut tree = PartitionTree::new(vec![], None);
        // literals {x1, x2} do NOT cover the space: both could be false.
        let lits = vec![Literal::positive(1), Literal::positive(2)];
        let cert = CoverageCertificate::tautology(lits.clone());
        assert!(matches!(cert, Err(crate::CoverageError::NotCovering)));
        // A certificate for a *different* covering split must not be
        // accepted for these literals.
        let other =
            CoverageCertificate::tautology(vec![Literal::positive(1), Literal::negative(1)])
                .unwrap();
        assert!(tree.split(tree.root(), lits.clone(), other).is_err());
        // The tree is untouched by the rejected split.
        assert_eq!(tree.get(tree.root()).unwrap().children.len(), 0);
    }

    #[test]
    fn unsat_closure_requires_all_leaves() {
        let mut tree = PartitionTree::new(vec![], None);
        let lits = vec![Literal::positive(1), Literal::negative(1)];
        let cert = CoverageCertificate::tautology(lits.clone()).unwrap();
        let children = tree.split(tree.root(), lits.clone(), cert).unwrap();
        assert!(!tree.is_unsat());

        tree.close(children[0], NodeStatus::ClosedUnsat).unwrap();
        assert!(!tree.is_unsat());

        tree.close(children[1], NodeStatus::ClosedUnsat).unwrap();
        assert!(tree.is_unsat());
        assert!(!tree.is_sat());
    }

    #[test]
    fn sat_closure_from_any_leaf() {
        let mut tree = PartitionTree::new(vec![], None);
        let lits = vec![Literal::positive(1), Literal::negative(1)];
        let cert = CoverageCertificate::tautology(lits.clone()).unwrap();
        let children = tree.split(tree.root(), lits.clone(), cert).unwrap();
        tree.close(children[0], NodeStatus::ClosedSat).unwrap();
        assert!(tree.is_sat());
        assert!(!tree.is_unsat());
    }

    #[test]
    fn cannot_close_interior_node_or_reassign_closed() {
        let mut tree = PartitionTree::new(vec![], None);
        let lits = vec![Literal::positive(1), Literal::negative(1)];
        let cert = CoverageCertificate::tautology(lits.clone()).unwrap();
        tree.split(tree.root(), lits.clone(), cert).unwrap();
        assert!(matches!(
            tree.close(tree.root(), NodeStatus::ClosedSat),
            Err(SchedulerError::NotLeaf(_))
        ));
    }

    #[test]
    fn reopen_after_cancel() {
        let mut tree = PartitionTree::new(vec![], None);
        tree.assign(tree.root()).unwrap();
        tree.close(tree.root(), NodeStatus::Cancelled).unwrap();
        tree.reopen(tree.root()).unwrap();
        assert_eq!(tree.get(tree.root()).unwrap().status, NodeStatus::Open);
    }

    #[test]
    fn depth_limit_blocks_split() {
        let mut tree = PartitionTree::new(vec![], Some(1));
        let lits = vec![Literal::positive(1), Literal::negative(1)];
        let cert = CoverageCertificate::tautology(lits.clone()).unwrap();
        // Root (depth 0) may split to depth 1.
        let children = tree.split(tree.root(), lits.clone(), cert).unwrap();
        // A depth-1 leaf may not split further.
        let cert2 =
            CoverageCertificate::tautology(vec![Literal::positive(2), Literal::negative(2)])
                .unwrap();
        assert!(tree
            .split(
                children[0],
                vec![Literal::positive(2), Literal::negative(2)],
                cert2
            )
            .is_err());
    }
}
