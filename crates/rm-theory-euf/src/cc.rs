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
        /// Raw SAT literal for the disequality assertion that triggered this conflict.
        /// Must be negated and included in the conflict clause alongside the eq-chain lits.
        diseq_lit: u32,
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
    /// The child's use-list was cleared (items moved to root). Restore on backtrack.
    UseListClear { node: ENodeId, items: Vec<ENodeId> },
    /// An explanation-forest edge was changed (set or cleared during path reversal).
    /// Stores the OLD value so backtrack can restore it exactly.
    ExplEdgeChange { node: ENodeId, old: Option<(ENodeId, MergeReason)> },
}

// ---------------------------------------------------------------------------
// Reason for a merge (for explanation)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum MergeReason {
    /// A SAT literal `eq(lhs, rhs)` was asserted directly.
    Asserted {
        lhs: ENodeId,
        rhs: ENodeId,
        sat_lit: u32,
    },
    /// Two nodes merged by congruence (same func, args already equal).
    Congruence { n1: ENodeId, n2: ENodeId },
}

// ---------------------------------------------------------------------------
// Congruence closure
// ---------------------------------------------------------------------------

#[derive(Clone)]
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
            self.uf.push(UfNode {
                parent: next,
                rank: 0,
                size: 1,
            });
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
        // No path compression: backtrack_to only restores the single child.parent
        // edge changed per merge.  Path compression skips nodes and leaves stale
        // pointers after backtracking, causing find to return wrong representatives.
        // Union-by-rank alone keeps this O(log n) which is fine for solver sizes.
        let mut cur = id;
        loop {
            let parent = self.uf[cur.0 as usize].parent;
            if parent == cur {
                return cur;
            }
            cur = parent;
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
        // Discard any pending merges left over from a conflict return mid-propagate.
        // Stale entries carry MergeReasons from the now-undone union-find state; if
        // kept they would trigger spurious merges with wrong explain_parent edges in
        // the next theory_check call, producing incomplete conflict clauses.
        self.pending.clear();
        while self.undo.len() > target {
            match self.undo.pop().unwrap() {
                UndoEntry::Union {
                    child,
                    old_parent,
                    old_rank,
                    old_size_root,
                } => {
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
                UndoEntry::UseListClear { node, items } => {
                    self.use_list[node.0 as usize] = items;
                }
                UndoEntry::ExplEdgeChange { node, old } => {
                    self.explain_parent[node.0 as usize] = old;
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
        self.pending
            .push((lhs, rhs, MergeReason::Asserted { lhs, rhs, sat_lit }));
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
                diseq_lit: sat_lit,
            });
        }
        // Store the ORIGINAL nodes (not their representatives) so that
        // explain_equality called on a later conflict traces the full equality
        // chain from lhs to rhs.  Using representatives would truncate the
        // explanation to the last merge step only, producing unsound conflict
        // clauses (too short → rule out more assignments than the conflict
        // actually justifies → false UNSAT).
        self.diseqs.push((lhs, rhs, sat_lit));
        self.undo.push(UndoEntry::Diseq { lhs, rhs });
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Congruence propagation
    // -----------------------------------------------------------------------

    fn propagate(&mut self, egraph: &EGraph) -> Result<(), CcError> {
        while let Some((a, b, reason)) = self.pending.pop() {
            let rep_a = self.find(a);
            let rep_b = self.find(b);
            if rep_a == rep_b {
                continue;
            }

            let (child, root) = if self.uf[rep_a.0 as usize].rank <= self.uf[rep_b.0 as usize].rank
            {
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

            // Redirect the explain forest using path reversal (standard DPLL(T) algorithm).
            //
            // Goal: after merging, explain_equality(any node in child's class, any node
            // in root's class) must return ALL equalities in the derivation chain.
            //
            // Simple "explain_parent[child_rep] = (orig_other, reason)" is wrong when
            // orig_child ≠ child_rep: the child rep's class already has an explain path
            // child_rep→...→orig_child, and jumping directly to orig_other skips those
            // edges in the explanation.
            //
            // Correct algorithm (Nieuwenhuis-Oliveras):
            //   1. Walk from orig_child toward its explain root (child_rep), collecting
            //      the path.
            //   2. Reverse every edge on that path (so child_rep now leads toward orig_child).
            //   3. Set explain_parent[orig_child] = (orig_other, reason) — the new edge.
            //
            // After this the path from child_rep is:
            //   child_rep → ... → orig_child → orig_other → ... → root_rep
            // which encodes the complete derivation.
            let orig_child = if child == rep_a { a } else { b };
            let orig_other = if child == rep_a { b } else { a };
            self.redirect_explain_path(orig_child, orig_other, reason);

            self.uf[child.0 as usize].parent = root;
            self.uf[root.0 as usize].size += self.uf[child.0 as usize].size;
            if self.uf[child.0 as usize].rank == self.uf[root.0 as usize].rank {
                self.uf[root.0 as usize].rank += 1;
            }

            let child_use: Vec<ENodeId> = std::mem::take(&mut self.use_list[child.0 as usize]);
            // UseListClear is pushed BEFORE the UseListPush entries so that LIFO undo
            // processes the pushes (restoring root's list) before restoring child's list.
            self.undo.push(UndoEntry::UseListClear { node: child, items: child_use.clone() });
            for &node_id in &child_use {
                // Look up current canonical signature.
                let node = egraph.node(node_id);
                let canon: SmallVec<[ENodeId; 4]> =
                    node.args.iter().map(|&a| self.find(a)).collect();
                let sig_key = (node.func.0, canon.clone());

                if let Some(&other) = self.sig_table.get(&sig_key) {
                    if other != node_id {
                        let rep_other = self.find(other);
                        let rep_node = self.find(node_id);
                        if rep_other != rep_node {
                            // Guard against stale sig_table entries from previous
                            // theory_check iterations (sig_table is never rolled back).
                            // Verify `other`'s current canonical signature still matches
                            // before triggering a congruence; if stale, update the table.
                            let other_node = egraph.node(other);
                            let other_canon: SmallVec<[ENodeId; 4]> =
                                other_node.args.iter().map(|&a| self.find(a)).collect();
                            if other_node.func.0 == node.func.0 && other_canon == canon {
                                self.pending.push((
                                    node_id,
                                    other,
                                    MergeReason::Congruence {
                                        n1: node_id,
                                        n2: other,
                                    },
                                ));
                            } else {
                                self.sig_table.insert(sig_key, node_id);
                            }
                        }
                    }
                } else {
                    self.sig_table.insert(sig_key, node_id);
                }

                self.use_list[root.0 as usize].push(node_id);
                self.undo.push(UndoEntry::UseListPush { class: root });
            }

            // Check all recorded disequalities for a conflict. Use an index loop
            // instead of cloning diseqs: ENodeId is Copy so self.diseqs[i] copies
            // three words, avoiding an O(N) allocation on every merge.
            let n_diseqs = self.diseqs.len();
            for i in 0..n_diseqs {
                let (a_orig, b_orig, diseq_sat_lit) = self.diseqs[i];
                let cur_a = self.find(a_orig);
                let cur_b = self.find(b_orig);
                if cur_a == cur_b {
                    // Explain using original nodes — not their current representatives —
                    // so the full equality chain (a_orig…root…b_orig) is reconstructed.
                    let expl = self.explain_equality(egraph, a_orig, b_orig);
                    return Err(CcError::Conflict {
                        lhs: a_orig,
                        rhs: b_orig,
                        explanation: expl,
                        diseq_lit: diseq_sat_lit,
                    });
                }
            }
        }
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Explain-forest path redirection
    // -----------------------------------------------------------------------

    /// Redirect the explain forest so that after the call, the explain path
    /// from `from` leads to `to` via `reason`, with all prior edges from `from`
    /// to the old explain root reversed.
    ///
    /// Called during merges instead of the naive `explain_parent[child_rep] = (orig_other, reason)`.
    /// The naive version shortcuts across the within-class path and produces incomplete
    /// conflict clauses; this version preserves all intermediate steps.
    fn redirect_explain_path(&mut self, from: ENodeId, to: ENodeId, reason: MergeReason) {
        // Collect the path from `from` to the current explain root of its class.
        // (The root is the first node with explain_parent == None.)
        let mut path: Vec<(ENodeId, Option<(ENodeId, MergeReason)>)> = Vec::new();
        let mut cur = from;
        loop {
            let ep = self.explain_parent[cur.0 as usize].clone();
            let done = ep.is_none();
            path.push((cur, ep));
            if done {
                break;
            }
            let next = match &path.last().unwrap().1 {
                Some((n, _)) => *n,
                None => unreachable!(),
            };
            cur = next;
        }

        // path = [(from, ep_from), (p1, ep_p1), ..., (root, None)]
        // where ep_from = (p1, r1), ep_p1 = (p2, r2), ..., ep_pn-1 = (root, rn).
        //
        // Reverse every edge: root→...→p1→from (same reason on each reversed edge).
        // For i in 1..path.len(): path[i].node should now point to path[i-1].node.
        for i in 1..path.len() {
            let (parent_node, _parent_old_ep) = &path[i];
            let (child_node, child_old_ep) = &path[i - 1];
            // The original edge was child_node → parent_node with reason from child_old_ep.
            // Reverse: parent_node → child_node with the same reason.
            let rev_reason = match child_old_ep {
                Some((_, r)) => r.clone(),
                None => unreachable!("path[0] has no explain_parent but is not the root"),
            };
            let old = self.explain_parent[parent_node.0 as usize].take();
            self.undo.push(UndoEntry::ExplEdgeChange { node: *parent_node, old });
            self.explain_parent[parent_node.0 as usize] = Some((*child_node, rev_reason));
        }

        // Set the new edge: from → to.
        let old = self.explain_parent[from.0 as usize].take();
        self.undo.push(UndoEntry::ExplEdgeChange { node: from, old });
        self.explain_parent[from.0 as usize] = Some((to, reason));
    }

    // -----------------------------------------------------------------------
    // Explanation (proof reconstruction)
    // -----------------------------------------------------------------------

    /// Reconstruct the set of asserted equalities that imply `lhs = rhs`.
    /// Uses the explanation forest built during merges. Congruence steps are
    /// expanded recursively so every leaf premise has a concrete SAT literal.
    pub fn explain_equality(&self, egraph: &EGraph, lhs: ENodeId, rhs: ENodeId) -> Explanation {
        let mut premises = Vec::new();
        self.collect_explanation(egraph, lhs, rhs, &mut premises);
        premises.sort_by_key(|l| (l.lhs, l.rhs, l.sat_lit));
        premises.dedup();
        Explanation { lhs, rhs, premises }
    }

    /// Iterative worklist expansion of the congruence-closure explanation forest.
    /// Avoids stack overflow on deep congruence chains by using an explicit stack
    /// instead of mutual recursion between collect_explanation and expand_reason.
    fn collect_explanation(
        &self,
        egraph: &EGraph,
        a: ENodeId,
        b: ENodeId,
        premises: &mut Vec<ExplanationLit>,
    ) {
        let mut worklist: Vec<(ENodeId, ENodeId)> = vec![(a, b)];
        while let Some((a, b)) = worklist.pop() {
            if a == b {
                continue;
            }
            // Find LCA of a and b in the explain_parent forest.
            let mut path_a = vec![a];
            let mut cur = a;
            while let Some((next, _)) = self.explain_parent[cur.0 as usize].as_ref() {
                cur = *next;
                path_a.push(cur);
            }
            let mut path_b = vec![b];
            let mut cur = b;
            while let Some((next, _)) = self.explain_parent[cur.0 as usize].as_ref() {
                cur = *next;
                path_b.push(cur);
            }

            let set_a: rustc_hash::FxHashSet<ENodeId> = path_a.iter().copied().collect();
            let lca = match path_b.iter().find(|n| set_a.contains(n)).copied() {
                Some(n) => n,
                None => {
                    // a and b are claimed equal but their explain-forest paths share
                    // no common ancestor — indicates a bug in explain_parent construction.
                    // Skip rather than fabricate a wrong premise (in debug builds this
                    // will panic to surface the underlying issue).
                    debug_assert!(
                        false,
                        "no LCA in explain forest for {a:?} and {b:?}: \
                         path_a={path_a:?} path_b={path_b:?}"
                    );
                    continue;
                }
            };

            // Walk from a to LCA and b to LCA, processing each edge reason.
            let mut cur = a;
            while cur != lca {
                if let Some((next, reason)) = &self.explain_parent[cur.0 as usize] {
                    Self::process_reason(egraph, reason, premises, &mut worklist);
                    cur = *next;
                } else {
                    break;
                }
            }
            let mut cur = b;
            while cur != lca {
                if let Some((next, reason)) = &self.explain_parent[cur.0 as usize] {
                    Self::process_reason(egraph, reason, premises, &mut worklist);
                    cur = *next;
                } else {
                    break;
                }
            }
        }
    }

    /// Process one edge reason: Asserted edges add a premise directly; Congruence
    /// edges push the argument pairs onto the worklist for later processing.
    fn process_reason(
        egraph: &EGraph,
        reason: &MergeReason,
        premises: &mut Vec<ExplanationLit>,
        worklist: &mut Vec<(ENodeId, ENodeId)>,
    ) {
        match reason {
            MergeReason::Asserted { lhs, rhs, sat_lit } => {
                premises.push(ExplanationLit::eq(*lhs, *rhs, Some(*sat_lit)));
            }
            MergeReason::Congruence { n1, n2 } => {
                let node1 = egraph.node(*n1);
                let node2 = egraph.node(*n2);
                for (&a1, &a2) in node1.args.iter().zip(node2.args.iter()) {
                    if a1 != a2 {
                        worklist.push((a1, a2));
                    }
                }
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
        _explanation: &Explanation,
    ) -> rm_akx::knowledge::TheoryLemma {
        let conclusion = format!("{}={}", egraph.node(lhs).func.0, egraph.node(rhs).func.0);
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
        (0..n)
            .filter(|&i| self.find(ENodeId(i as u32)) == ENodeId(i as u32))
            .count()
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
        assert!(
            cc.are_equal(fa, fb),
            "congruence: f(a)=f(b) should follow from a=b"
        );
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
        assert!(
            lits.contains(&10) || lits.contains(&11),
            "explanation should reference the asserted sat lits, got: {lits:?}"
        );
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
