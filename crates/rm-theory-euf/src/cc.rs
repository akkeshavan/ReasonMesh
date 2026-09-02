//! Congruence closure for EUF.
//!
//! Implements the Downey-Sethi-Tarjan (DST) / Nieuwenhuis-Oliveras approach:
//! - Union-find with path compression and union-by-rank
//! - Rollback via a timestamped undo log (for CDCL backtracking)
//! - Congruence propagation via pending-list and use-lists
//! - Explanation / proof tree for conflict clause extraction
//! - `TheoryLemma` production for AKX sharing
//!
//! # Interface to CDCL(T)
//! The SAT solver asserts equalities as Boolean literals are propagated:
//!   `cc.assert_eq(a, b, sat_lit_idx)` — merge e-classes of a and b.
//!   `cc.assert_neq(a, b, sat_lit_idx)` — record a disequality; returns
//!      `Err(CcError::Conflict{..})` if a and b are already in the same class.
//!
//! On conflict, the CDCL solver learns the negation of the explanation lits.
//! On backtrack to level L, call `cc.backtrack_to(L)`.

use crate::egraph::{EGraph, ENode, ENodeId};
use crate::explain::{Explanation, ExplanationLit};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use thiserror::Error;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

#[derive(Debug, Error)]
pub enum CcError {
    #[error("EUF conflict: {lhs:?} and {rhs:?} are equal but declared distinct")]
    Conflict {
        lhs: ENodeId,
        rhs: ENodeId,
        explanation: Explanation,
    },
    #[error("unknown term id {0:?}")]
    UnknownTerm(ENodeId),
}

// ---------------------------------------------------------------------------
// Union-find node
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct UfNode {
    parent: ENodeId,
    rank: u32,
    /// The e-node representative's canonical children (updated on merge).
    /// Used for congruence: two nodes with the same func and same canonical
    /// children should be in the same class.
    size: u32,
}

// ---------------------------------------------------------------------------
// Undo log entry (for CDCL backtracking)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum UndoEntry {
    /// A union operation: remember which node became a child so we can split.
    Union {
        child: ENodeId,
        old_parent: ENodeId,
        old_rank: u32,
        old_size_root: u32,
    },
    /// A disequality was added.
    Diseq { lhs: ENodeId, rhs: ENodeId },
    /// A use-list entry was appended.
    UseListPush { class: ENodeId },
    /// An explanation-forest edge was set.
    ExplEdge { node: ENodeId },
}

// ---------------------------------------------------------------------------
// Reason for a merge (for explanation)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum MergeReason {
    /// A SAT literal `eq(lhs, rhs)` was asserted directly.
    Asserted { lhs: ENodeId, rhs: ENodeId, sat_lit: u32 },
    /// Two nodes merged by congruence (same func, args already equal).
    Congruence { n1: ENodeId, n2: ENodeId },
}

// ---------------------------------------------------------------------------
// Congruence closure
// ---------------------------------------------------------------------------

pub struct CongruenceClosure {
    /// E-graph (term storage).  CC takes shared ownership via borrow.
    uf: Vec<UfNode>,
    /// Explanation forest: `explain_parent[n]` = Some((neighbour, reason)).
    explain_parent: Vec<Option<(ENodeId, MergeReason)>>,
    /// Use lists: `use_list[rep]` = all e-nodes whose arguments contain `rep`.
    use_list: Vec<Vec<ENodeId>>,
    /// Signature table: (func, canonical args) → e-node.
    sig_table: FxHashMap<(u32, SmallVec<[ENodeId; 4]>), ENodeId>,
    /// Disequalities: set of (rep_a, rep_b) pairs.
    diseqs: Vec<(ENodeId, ENodeId, u32)>, // (lhs_rep, rhs_rep, sat_lit)
    /// Undo log stack; `level_lim[d]` = undo-log index at start of level d+1.
    undo: Vec<UndoEntry>,
    level_lim: Vec<usize>,
    /// Pending merges (congruence propagation queue).
    pending: Vec<(ENodeId, ENodeId, MergeReason)>,
}

impl CongruenceClosure {
    pub fn new(size_hint: usize) -> Self {
        CongruenceClosure {
            uf: Vec::with_capacity(size_hint),
            explain_parent: Vec::with_capacity(size_hint),
            use_list: Vec::with_capacity(size_hint),
            sig_table: FxHashMap::default(),
            diseqs: Vec::new(),
            undo: Vec::new(),
            level_lim: Vec::new(),
            pending: Vec::new(),
        }
    }

    // -----------------------------------------------------------------------
    // Term registration
    // -----------------------------------------------------------------------

    /// Register a new e-node. Must be called in topological order (children
    /// before parents).
    pub fn add_term(&mut self, id: ENodeId, node: &ENode) {
        let idx = id.0 as usize;
        while self.uf.len() <= idx {
            let next = ENodeId(self.uf.len() as u32);
            self.uf.push(UfNode { parent: next, rank: 0, size: 1 });
            self.explain_parent.push(None);
            self.use_list.push(Vec::new());
        }
        for &arg in &node.args {
            let rep = self.find(arg);
            self.use_list[rep.0 as usize].push(id);
        }
        let canon_args: SmallVec<[ENodeId; 4]> = node.args.iter().map(|&a| self.find(a)).collect();
        self.sig_table.insert((node.func.0, canon_args), id);
    }

    // -----------------------------------------------------------------------
    // Union-find with path compression
    // -----------------------------------------------------------------------

    pub fn find(&mut self, id: ENodeId) -> ENodeId {
        let mut cur = id;
        loop {
            let parent = self.uf[cur.0 as usize].parent;
            if parent == cur { return cur; }
            let grandparent = self.uf[parent.0 as usize].parent;
            self.uf[cur.0 as usize].parent = grandparent;
            cur = grandparent;
        }
    }

    /// Are `a` and `b` in the same equivalence class?
    pub fn are_equal(&mut self, a: ENodeId, b: ENodeId) -> bool {
        self.find(a) == self.find(b)
    }

    // -----------------------------------------------------------------------
    // Decision-level management (CDCL backtracking)
    // -----------------------------------------------------------------------

    pub fn new_decision_level(&mut self) {
        self.level_lim.push(self.undo.len());
    }

    pub fn current_level(&self) -> u32 {
        self.level_lim.len() as u32
    }

    pub fn backtrack_to(&mut self, level: u32) {
        let target = if (level as usize) < self.level_lim.len() {
            self.level_lim[level as usize]
        } else {
            return;
        };
        while self.undo.len() > target {
            match self.undo.pop().unwrap() {
                UndoEntry::Union { child, old_parent, old_rank, old_size_root } => {
                    let root = self.uf[child.0 as usize].parent;
                    self.uf[child.0 as usize].parent = old_parent;
                    self.uf[child.0 as usize].rank = old_rank;
                    self.uf[root.0 as usize].size = old_size_root;
                }
                UndoEntry::Diseq { lhs, rhs } => {
                    self.diseqs.retain(|(a, b, _)| !(*a == lhs && *b == rhs));
                }
                UndoEntry::UseListPush { class } => {
                    self.use_list[class.0 as usize].pop();
                }
                UndoEntry::ExplEdge { node } => {
                    self.explain_parent[node.0 as usize] = None;
                }
            }
        }
        self.level_lim.truncate(level as usize);
    }

    // -----------------------------------------------------------------------
    // Asserting equalities
    // -----------------------------------------------------------------------

    /// Assert `lhs = rhs` because of SAT literal `sat_lit`.
    /// Runs congruence closure to a fixed point.
    /// Returns `Err(CcError::Conflict{..})` if a disequality is violated.
    pub fn assert_eq(
        &mut self,
        egraph: &EGraph,
        lhs: ENodeId,
        rhs: ENodeId,
        sat_lit: u32,
    ) -> Result<(), CcError> {
        let rep_l = self.find(lhs);
        let rep_r = self.find(rhs);
        if rep_l == rep_r {
            return Ok(()); // already equal
        }
        self.pending.push((lhs, rhs, MergeReason::Asserted { lhs, rhs, sat_lit }));
        self.propagate(egraph)
    }

    /// Assert `lhs ≠ rhs`.
    /// Returns `Err(CcError::Conflict{..})` if lhs and rhs are already equal.
    pub fn assert_neq(
        &mut self,
        egraph: &EGraph,
        lhs: ENodeId,
        rhs: ENodeId,
        sat_lit: u32,
    ) -> Result<(), CcError> {
        let rep_l = self.find(lhs);
        let rep_r = self.find(rhs);
        if rep_l == rep_r {
            let expl = self.explain_equality(egraph, lhs, rhs);
            return Err(CcError::Conflict {
                lhs,
                rhs,
                explanation: expl,
            });
        }
        let (a, b) = if rep_l < rep_r { (rep_l, rep_r) } else { (rep_r, rep_l) };
        self.diseqs.push((a, b, sat_lit));
        self.undo.push(UndoEntry::Diseq { lhs: a, rhs: b });
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Congruence propagation
    // -----------------------------------------------------------------------

    fn propagate(&mut self, egraph: &EGraph) -> Result<(), CcError> {
        while let Some((a, b, reason)) = self.pending.pop() {
            let rep_a = self.find(a);
            let rep_b = self.find(b);
            if rep_a == rep_b { continue; }

            let (child, root) = if self.uf[rep_a.0 as usize].rank <= self.uf[rep_b.0 as usize].rank {
                (rep_a, rep_b)
            } else {
                (rep_b, rep_a)
            };

            self.undo.push(UndoEntry::Union {
                child,
                old_parent: child,
                old_rank: self.uf[child.0 as usize].rank,
                old_size_root: self.uf[root.0 as usize].size,
            });

            let (expl_from, expl_to) = (child, root);
            self.undo.push(UndoEntry::ExplEdge { node: expl_from });
            self.explain_parent[expl_from.0 as usize] = Some((expl_to, reason));

            self.uf[child.0 as usize].parent = root;
            self.uf[root.0 as usize].size += self.uf[child.0 as usize].size;
            if self.uf[child.0 as usize].rank == self.uf[root.0 as usize].rank {
                self.uf[root.0 as usize].rank += 1;
            }

            let child_use: Vec<ENodeId> = std::mem::take(&mut self.use_list[child.0 as usize]);
            for &node_id in &child_use {
                // Look up current canonical signature.
                let node = egraph.node(node_id);
                let canon: SmallVec<[ENodeId; 4]> = node.args.iter().map(|&a| self.find(a)).collect();
                let sig_key = (node.func.0, canon.clone());

                if let Some(&other) = self.sig_table.get(&sig_key) {
                    if other != node_id {
                        let rep_other = self.find(other);
                        let rep_node = self.find(node_id);
                        if rep_other != rep_node {
                            self.pending.push((
                                node_id,
                                other,
                                MergeReason::Congruence { n1: node_id, n2: other },
                            ));
                        }
                    }
                } else {
                    self.sig_table.insert(sig_key, node_id);
                }

                self.use_list[root.0 as usize].push(node_id);
                self.undo.push(UndoEntry::UseListPush { class: root });
            }

            let diseqs_snap: Vec<(ENodeId, ENodeId, u32)> = self.diseqs.clone();
            for (a_rep, b_rep, _sat_lit) in diseqs_snap {
                let cur_a = self.find(a_rep);
                let cur_b = self.find(b_rep);
                if cur_a == cur_b {
                    let expl = self.explain_equality(egraph, a_rep, b_rep);
                    return Err(CcError::Conflict {
                        lhs: a_rep,
                        rhs: b_rep,
                        explanation: expl,
                    });
                }
            }
        }
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Explanation (proof reconstruction)
    // -----------------------------------------------------------------------

    /// Reconstruct the set of asserted equalities that imply `lhs = rhs`.
    /// Uses the explanation forest built during merges.
    pub fn explain_equality(&self, _egraph: &EGraph, lhs: ENodeId, rhs: ENodeId) -> Explanation {
        // Collect path from lhs to LCA and rhs to LCA in the explanation forest.
        let mut premises = Vec::new();
        self.collect_path(lhs, rhs, &mut premises);
        Explanation { lhs, rhs, premises }
    }

    fn collect_path(
        &self,
        mut a: ENodeId,
        mut b: ENodeId,
        premises: &mut Vec<ExplanationLit>,
    ) {
        let mut path_a = vec![a];
        let mut path_b = vec![b];

        while let Some((next, _)) = self.explain_parent[a.0 as usize].as_ref() {
            a = *next;
            path_a.push(a);
        }
        while let Some((next, _)) = self.explain_parent[b.0 as usize].as_ref() {
            b = *next;
            path_b.push(b);
        }

        let set_a: rustc_hash::FxHashSet<ENodeId> = path_a.iter().copied().collect();
        let lca = path_b.iter().find(|n| set_a.contains(n)).copied().unwrap_or(path_a[0]);

        let mut cur = path_a[0];
        while cur != lca {
            if let Some((next, reason)) = &self.explain_parent[cur.0 as usize] {
                Self::add_reason_to_premises(reason, premises);
                cur = *next;
            } else { break; }
        }
        let mut cur = path_b[0];
        while cur != lca {
            if let Some((next, reason)) = &self.explain_parent[cur.0 as usize] {
                Self::add_reason_to_premises(reason, premises);
                cur = *next;
            } else { break; }
        }

        premises.sort_by_key(|l| (l.lhs, l.rhs, l.sat_lit));
        premises.dedup();
    }

    fn add_reason_to_premises(reason: &MergeReason, premises: &mut Vec<ExplanationLit>) {
        match reason {
            MergeReason::Asserted { lhs, rhs, sat_lit } => {
                premises.push(ExplanationLit::eq(*lhs, *rhs, Some(*sat_lit)));
            }
            MergeReason::Congruence { n1, n2 } => {
                premises.push(ExplanationLit::eq(*n1, *n2, None));
            }
        }
    }

    // -----------------------------------------------------------------------
    // Theory lemma generation for AKX
    // -----------------------------------------------------------------------

    /// Generate a `TheoryLemma` knowledge object for the derived equality
    /// `lhs = rhs` under the given explanation. The lemma is unconditional
    /// (asserted = true for the whole problem) when all premises are axioms.
    pub fn to_akx_lemma(
        &self,
        egraph: &EGraph,
        lhs: ENodeId,
        rhs: ENodeId,
        explanation: &Explanation,
    ) -> rm_akx::knowledge::TheoryLemma {
        let conclusion = format!(
            "{}={}",
            egraph.node(lhs).func.0,
            egraph.node(rhs).func.0
        );
        let theory_tag = "euf_congruence".to_string();
        rm_akx::knowledge::TheoryLemma {
            conclusion_bytes: conclusion.into_bytes(),
            theory_tag,
        }
    }

    // -----------------------------------------------------------------------
    // Queries
    // -----------------------------------------------------------------------

    /// Return the canonical representative of `id`.
    pub fn repr(&mut self, id: ENodeId) -> ENodeId {
        self.find(id)
    }

    /// How many distinct equivalence classes are there?
    pub fn num_classes(&mut self) -> usize {
        let n = self.uf.len();
        (0..n).filter(|&i| self.find(ENodeId(i as u32)) == ENodeId(i as u32)).count()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::EGraph;

    fn setup() -> (EGraph, CongruenceClosure) {
        let eg = EGraph::new();
        let cc = CongruenceClosure::new(16);
        (eg, cc)
    }

    #[test]
    fn reflexivity() {
        let (mut eg, mut cc) = setup();
        let a = eg.constant("a");
        cc.add_term(a, eg.node(a));
        assert!(cc.are_equal(a, a));
    }

    #[test]
    fn symmetry_and_transitivity() {
        let (mut eg, mut cc) = setup();
        let a = eg.constant("a");
        let b = eg.constant("b");
        let c = eg.constant("c");
        cc.add_term(a, eg.node(a));
        cc.add_term(b, eg.node(b));
        cc.add_term(c, eg.node(c));

        cc.assert_eq(&eg, a, b, 0).unwrap();
        cc.assert_eq(&eg, b, c, 1).unwrap();

        assert!(cc.are_equal(a, c));
        assert!(cc.are_equal(c, a));
    }

    #[test]
    fn congruence() {
        let (mut eg, mut cc) = setup();
        let a = eg.constant("a");
        let b = eg.constant("b");
        let fa = eg.apply("f", &[a]);
        let fb = eg.apply("f", &[b]);

        cc.add_term(a, eg.node(a));
        cc.add_term(b, eg.node(b));
        cc.add_term(fa, eg.node(fa));
        cc.add_term(fb, eg.node(fb));

        // a = b → f(a) = f(b)
        cc.assert_eq(&eg, a, b, 0).unwrap();
        assert!(cc.are_equal(fa, fb), "congruence: f(a)=f(b) should follow from a=b");
    }

    #[test]
    fn disequality_conflict() {
        let (mut eg, mut cc) = setup();
        let a = eg.constant("a");
        let b = eg.constant("b");
        cc.add_term(a, eg.node(a));
        cc.add_term(b, eg.node(b));

        cc.assert_eq(&eg, a, b, 0).unwrap();
        let result = cc.assert_neq(&eg, a, b, 1);
        assert!(matches!(result, Err(CcError::Conflict { .. })));
    }

    #[test]
    fn backtrack_restores_state() {
        let (mut eg, mut cc) = setup();
        let a = eg.constant("a");
        let b = eg.constant("b");
        cc.add_term(a, eg.node(a));
        cc.add_term(b, eg.node(b));

        cc.new_decision_level();
        cc.assert_eq(&eg, a, b, 0).unwrap();
        assert!(cc.are_equal(a, b));

        cc.backtrack_to(0);
        assert!(!cc.are_equal(a, b), "backtrack should undo the merge");
    }

    #[test]
    fn congruence_conflict_via_transitivity() {
        // a=b, f(a)≠f(b) → conflict via congruence
        let (mut eg, mut cc) = setup();
        let a = eg.constant("a");
        let b = eg.constant("b");
        let fa = eg.apply("f", &[a]);
        let fb = eg.apply("f", &[b]);
        cc.add_term(a, eg.node(a));
        cc.add_term(b, eg.node(b));
        cc.add_term(fa, eg.node(fa));
        cc.add_term(fb, eg.node(fb));

        // Assert f(a) ≠ f(b) first.
        cc.assert_neq(&eg, fa, fb, 1).unwrap();
        // Then assert a = b → congruence should derive f(a)=f(b) → conflict.
        let result = cc.assert_eq(&eg, a, b, 0);
        assert!(
            matches!(result, Err(CcError::Conflict { .. })),
            "should detect conflict: a=b and f(a)≠f(b)"
        );
    }

    #[test]
    fn explanation_contains_sat_lit() {
        let (mut eg, mut cc) = setup();
        let a = eg.constant("a");
        let b = eg.constant("b");
        let c = eg.constant("c");
        cc.add_term(a, eg.node(a));
        cc.add_term(b, eg.node(b));
        cc.add_term(c, eg.node(c));

        cc.assert_eq(&eg, a, b, 10).unwrap();
        cc.assert_eq(&eg, b, c, 11).unwrap();

        let expl = cc.explain_equality(&eg, a, c);
        let lits = expl.sat_lits();
        assert!(lits.contains(&10) || lits.contains(&11),
            "explanation should reference the asserted sat lits, got: {lits:?}");
    }

    #[test]
    fn num_classes_decreases_on_merge() {
        let (mut eg, mut cc) = setup();
        let a = eg.constant("a");
        let b = eg.constant("b");
        let c = eg.constant("c");
        cc.add_term(a, eg.node(a));
        cc.add_term(b, eg.node(b));
        cc.add_term(c, eg.node(c));

        assert_eq!(cc.num_classes(), 3);
        cc.assert_eq(&eg, a, b, 0).unwrap();
        assert_eq!(cc.num_classes(), 2);
        cc.assert_eq(&eg, b, c, 1).unwrap();
        assert_eq!(cc.num_classes(), 1);
    }
}
