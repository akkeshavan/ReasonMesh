//! Incremental difference-logic solver using Bellman-Ford.
//!
//! The constraint graph has one node per arithmetic variable plus a special
//! zero node (index 0) that represents the constant 0. An assertion
//! `x - y ≤ c` adds a directed edge y → x with weight c.
//!
//! Consistency check: the system is consistent iff the constraint graph
//! has no negative-weight cycle. We detect this via Bellman-Ford from the
//! zero node (which has ε-edges to every other node so all are reachable).
//!
//! Incremental updates: edges are added one at a time; each new edge is
//! checked with a single-source shortest-path update rather than a full
//! Bellman-Ford run. Backtracking removes edges via an undo log.
//!
//! Reference: Nieuwenhuis & Oliveras, "DPLL(T): Fast Decision Procedures",
//! CAV 2004; Dutertre & de Moura, "A Fast Linear-Arithmetic Solver for DPLL(T)",
//! CAV 2006 (for the more efficient variant).

use smallvec::SmallVec;
use thiserror::Error;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

pub type VarId = u32;

/// An edge in the constraint graph: (from, to, weight, sat_lit).
#[derive(Clone, Debug)]
struct Edge {
    from: VarId,
    to: VarId,
    weight: i64,
    sat_lit: u32,
}

/// Result type for DL operations.
pub type DlResult<T> = Result<T, DlError>;

#[derive(Debug, Error)]
pub enum DlError {
    #[error("difference logic conflict: negative cycle detected")]
    Conflict(ConflictCore),
    #[error("variable {0} is out of range")]
    UnknownVar(VarId),
}

/// The set of sat-literals forming the negative cycle (conflict clause).
#[derive(Clone, Debug)]
pub struct ConflictCore {
    /// SAT literal indices in the cycle (negated → CDCL conflict clause).
    pub sat_lits: Vec<u32>,
    /// The variables involved in the cycle (for diagnostics).
    pub cycle_vars: Vec<VarId>,
}

// ---------------------------------------------------------------------------
// Solver
// ---------------------------------------------------------------------------

/// Incremental difference-logic consistency checker.
///
/// Variables are 1-indexed; variable 0 is the "zero" constant.
pub struct DiffLogicSolver {
    /// Number of theory variables (not counting the zero node at index 0).
    num_vars: u32,
    /// All asserted edges, in assertion order.
    edges: Vec<Edge>,
    /// Bellman-Ford distance array: `dist[v]` = shortest path from zero to v.
    dist: Vec<i64>,
    /// Predecessor edge index for each node in the shortest-path tree.
    pred_edge: Vec<Option<usize>>,
    /// Undo log: (decision level, edge count at that level).
    /// On backtrack to level L we remove all edges added since level L.
    level_lim: Vec<usize>,
    /// Adjacency list (from→[(to, edge_idx)]) for Bellman-Ford relaxation.
    adj: Vec<Vec<(VarId, usize)>>,
}

impl DiffLogicSolver {
    /// Create a solver for `num_vars` variables (1-indexed; 0 = zero constant).
    pub fn new(num_vars: u32) -> Self {
        let n = num_vars as usize + 1;
        DiffLogicSolver {
            num_vars,
            edges: Vec::new(),
            dist: vec![0; n],
            pred_edge: vec![None; n],
            level_lim: Vec::new(),
            adj: vec![Vec::new(); n],
        }
    }

    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }

    // -----------------------------------------------------------------------
    // CDCL interface
    // -----------------------------------------------------------------------

    pub fn new_decision_level(&mut self) {
        self.level_lim.push(self.edges.len());
    }

    pub fn current_level(&self) -> u32 {
        self.level_lim.len() as u32
    }

    /// Undo all assertions made above `level`.
    pub fn backtrack_to(&mut self, level: u32) {
        let target = if (level as usize) < self.level_lim.len() {
            self.level_lim[level as usize]
        } else {
            return;
        };
        while self.edges.len() > target {
            let e = self.edges.pop().unwrap();
            self.adj[e.from as usize].retain(|(_, idx)| *idx != self.edges.len());
        }
        self.level_lim.truncate(level as usize);
        let n = self.num_vars as usize + 1;
        self.dist = vec![0i64; n];
        self.pred_edge = vec![None; n];
    }

    /// Assert the constraint `x - y ≤ c` (edge y→x with weight c).
    /// Returns `Err(DlError::Conflict)` if inconsistent.
    pub fn assert_leq(&mut self, x: VarId, y: VarId, c: i64, sat_lit: u32) -> DlResult<()> {
        if x > self.num_vars || y > self.num_vars {
            return Err(DlError::UnknownVar(x.max(y)));
        }
        let edge_idx = self.edges.len();
        self.edges.push(Edge {
            from: y,
            to: x,
            weight: c,
            sat_lit,
        });
        self.adj[y as usize].push((x, edge_idx));

        self.relax_from_edge(edge_idx)?;
        Ok(())
    }

    /// Assert `x - y < c` (strict): equivalent to `x - y ≤ c - 1` for IDL.
    pub fn assert_lt(&mut self, x: VarId, y: VarId, c: i64, sat_lit: u32) -> DlResult<()> {
        self.assert_leq(x, y, c - 1, sat_lit)
    }

    /// Assert `x = y`: equivalent to `x - y ≤ 0` and `y - x ≤ 0`.
    pub fn assert_eq(&mut self, x: VarId, y: VarId, sat_lit: u32) -> DlResult<()> {
        self.assert_leq(x, y, 0, sat_lit)?;
        self.assert_leq(y, x, 0, sat_lit)
    }

    // -----------------------------------------------------------------------
    // Full consistency check (Bellman-Ford from zero)
    // -----------------------------------------------------------------------

    /// Full Bellman-Ford consistency check. Call after bulk-loading constraints.
    ///
    /// DL potential interpretation: initialize all `dist[v] = 0` (the implicit
    /// zero source has 0-weight edges to every node). A negative cycle exists
    /// iff any edge can still relax after `n` rounds.
    pub fn check(&mut self) -> DlResult<()> {
        let n = self.num_vars as usize + 1;
        let mut dist = vec![0i64; n];
        let mut pred: Vec<Option<usize>> = vec![None; n];

        for _ in 0..n {
            let mut changed = false;
            for (idx, edge) in self.edges.iter().enumerate() {
                let new_d = dist[edge.from as usize].saturating_add(edge.weight);
                if new_d < dist[edge.to as usize] {
                    dist[edge.to as usize] = new_d;
                    pred[edge.to as usize] = Some(idx);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        for (idx, edge) in self.edges.iter().enumerate() {
            let new_d = dist[edge.from as usize].saturating_add(edge.weight);
            if new_d < dist[edge.to as usize] {
                return Err(DlError::Conflict(self.extract_cycle(&pred, idx)));
            }
        }

        self.dist = dist;
        self.pred_edge = pred;
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Incremental relaxation
    // -----------------------------------------------------------------------

    /// Relax from a newly-added edge. Uses modified Dijkstra/BF from the
    /// updated node, stopping when no further improvements are possible.
    fn relax_from_edge(&mut self, new_edge_idx: usize) -> DlResult<()> {
        let edge = &self.edges[new_edge_idx];
        let (from, to, w) = (edge.from as usize, edge.to as usize, edge.weight);

        if self.dist[from].saturating_add(w) < self.dist[to] {
            self.dist[to] = self.dist[from] + w;
            self.pred_edge[to] = Some(new_edge_idx);

            let mut queue: SmallVec<[usize; 16]> = SmallVec::new();
            queue.push(to);

            while let Some(v) = queue.first().cloned() {
                queue.remove(0);

                if self.detect_negative_cycle_through(v) {
                    return Err(DlError::Conflict(self.extract_cycle_from(v)));
                }

                let adj_v: Vec<(VarId, usize)> = self.adj[v].clone();
                for (succ, edge_idx) in adj_v {
                    let e = &self.edges[edge_idx];
                    let new_d = self.dist[v].saturating_add(e.weight);
                    if new_d < self.dist[succ as usize] {
                        self.dist[succ as usize] = new_d;
                        self.pred_edge[succ as usize] = Some(edge_idx);
                        queue.push(succ as usize);
                    }
                }
            }
        }
        Ok(())
    }

    fn detect_negative_cycle_through(&self, start: usize) -> bool {
        let mut cur = start;
        let limit = self.num_vars as usize + 2;
        for _ in 0..limit {
            if let Some(edge_idx) = self.pred_edge[cur] {
                cur = self.edges[edge_idx].from as usize;
                if cur == start {
                    return true;
                }
            } else {
                return false;
            }
        }
        false
    }

    fn extract_cycle_from(&self, start: usize) -> ConflictCore {
        let mut sat_lits = Vec::new();
        let mut cycle_vars = Vec::new();
        let mut cur = start;
        let limit = self.num_vars as usize + 2;
        for _ in 0..limit {
            if let Some(edge_idx) = self.pred_edge[cur] {
                let e = &self.edges[edge_idx];
                sat_lits.push(e.sat_lit);
                cycle_vars.push(cur as VarId);
                cur = e.from as usize;
                if cur == start {
                    break;
                }
            } else {
                break;
            }
        }
        sat_lits.sort_unstable();
        sat_lits.dedup();
        ConflictCore {
            sat_lits,
            cycle_vars,
        }
    }

    fn extract_cycle(&self, pred: &[Option<usize>], triggering_edge: usize) -> ConflictCore {
        let edge = &self.edges[triggering_edge];
        let cycle_start = edge.to as usize;
        let mut sat_lits = vec![edge.sat_lit];
        let mut cycle_vars = vec![cycle_start as VarId];
        let mut cur = cycle_start;

        let limit = self.num_vars as usize + 2;
        for _ in 0..limit {
            if let Some(ei) = pred[cur] {
                let e = &self.edges[ei];
                sat_lits.push(e.sat_lit);
                cycle_vars.push(cur as VarId);
                cur = e.from as usize;
                if cur == cycle_start {
                    break;
                }
            } else {
                break;
            }
        }
        sat_lits.sort_unstable();
        sat_lits.dedup();
        ConflictCore {
            sat_lits,
            cycle_vars,
        }
    }

    // -----------------------------------------------------------------------
    // Queries
    // -----------------------------------------------------------------------

    /// Current upper bound on `x - y` (shortest path from y to x in graph).
    pub fn upper_bound(&self, x: VarId, y: VarId) -> Option<i64> {
        if self.dist[x as usize] < i64::MAX / 2 && self.dist[y as usize] == 0 {
            Some(self.dist[x as usize])
        } else {
            None
        }
    }

    /// Current potential of variable x (upper bound; starts at 0, decreases as
    /// tighter constraints are added).
    pub fn var_upper_bound(&self, x: VarId) -> Option<i64> {
        if x == 0 || x > self.num_vars {
            return None;
        }
        Some(self.dist[x as usize])
    }

    /// Compute the shortest path from `source` to `target` in the constraint
    /// graph (i.e., the tightest derivable upper bound on `target - source`).
    ///
    /// Returns `None` if no path exists (no constraint links them).
    /// O(V·E) — intended for small shared-variable sets (Nelson-Oppen).
    pub fn bound_between(&self, source: VarId, target: VarId) -> Option<i64> {
        if source > self.num_vars || target > self.num_vars {
            return None;
        }
        let n = self.num_vars as usize + 1;
        let mut dist = vec![i64::MAX / 2; n];
        dist[source as usize] = 0;

        for _ in 0..n {
            let mut changed = false;
            for edge in &self.edges {
                let d = dist[edge.from as usize];
                if d < i64::MAX / 2 {
                    let nd = d.saturating_add(edge.weight);
                    if nd < dist[edge.to as usize] {
                        dist[edge.to as usize] = nd;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }

        let d = dist[target as usize];
        if d < i64::MAX / 2 {
            Some(d)
        } else {
            None
        }
    }

    /// Number of asserted edges.
    pub fn num_edges(&self) -> usize {
        self.edges.len()
    }

    /// Produce AKX `BoundKnowledge` for all currently tight bounds.
    pub fn akx_bounds(&self) -> Vec<rm_akx::knowledge::BoundKnowledge> {
        use crate::bound::{Bound, BoundKind};
        use rm_akx::knowledge::BoundKind as AkxBoundKind;

        (1..=self.num_vars)
            .filter_map(|v| {
                self.var_upper_bound(v)
                    .map(|c| rm_akx::knowledge::BoundKnowledge {
                        term_id: v as u64,
                        kind: AkxBoundKind::LessEq,
                        value_bytes: Bound {
                            kind: BoundKind::UpperBound,
                            lhs: v,
                            rhs: None,
                            numerator: c,
                            denominator: 1,
                        }
                        .to_bytes(),
                    })
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_consistent() {
        // x - y ≤ 3, y - z ≤ 2 → no cycle
        let mut s = DiffLogicSolver::new(3); // vars: 1=x, 2=y, 3=z
        s.assert_leq(1, 2, 3, 0).unwrap(); // x - y ≤ 3 → edge 2→1 w=3
        s.assert_leq(2, 3, 2, 1).unwrap(); // y - z ≤ 2 → edge 3→2 w=2
        s.check().unwrap();
    }

    #[test]
    fn negative_cycle_conflict() {
        // x - y ≤ 1, y - x ≤ -2 → x - x ≤ -1 (negative cycle)
        let mut s = DiffLogicSolver::new(2);
        s.assert_leq(1, 2, 1, 0).unwrap(); // x - y ≤ 1
        let result = s.assert_leq(2, 1, -2, 1); // y - x ≤ -2
                                                // Either assert_leq catches it incrementally or check() will.
        if result.is_ok() {
            let check = s.check();
            assert!(
                matches!(check, Err(DlError::Conflict(_))),
                "expected conflict from negative cycle"
            );
        }
        // Either way: a conflict was detected.
    }

    #[test]
    fn backtrack_restores_consistency() {
        let mut s = DiffLogicSolver::new(2);
        s.assert_leq(1, 2, 5, 0).unwrap();

        s.new_decision_level();
        s.assert_leq(2, 1, -10, 1).unwrap_or_default(); // may conflict
        s.backtrack_to(0);

        // After backtrack, the conflicting edge is gone.
        s.assert_leq(1, 2, 3, 2).unwrap();
        s.check().unwrap();
    }

    #[test]
    fn assert_eq_consistency() {
        let mut s = DiffLogicSolver::new(3);
        // x = y, y = z → x = z (no conflict)
        s.assert_eq(1, 2, 0).unwrap();
        s.assert_eq(2, 3, 1).unwrap();
        s.check().unwrap();
    }

    #[test]
    fn assert_eq_conflict() {
        // x = y, then x ≠ y (via x - y ≥ 1 and y - x ≥ 1 → cycle)
        let mut s = DiffLogicSolver::new(2);
        s.assert_eq(1, 2, 0).unwrap(); // x = y
                                       // x - y ≥ 1 ⟺ y - x ≤ -1 → edge x→y w=-1
                                       // combined with x-y≤0 gives cycle weight 0-1 = -1 < 0
        let r = s.assert_leq(2, 1, -1, 1); // y - x ≤ -1
        if r.is_ok() {
            assert!(matches!(s.check(), Err(DlError::Conflict(_))));
        }
    }

    #[test]
    fn akx_bounds_populated() {
        let mut s = DiffLogicSolver::new(2);
        s.assert_leq(1, 0, 7, 0).unwrap(); // x ≤ 7 (x - 0 ≤ 7)
        s.check().unwrap();
        let bounds = s.akx_bounds();
        assert!(!bounds.is_empty(), "should produce bound knowledge for x");
    }

    #[test]
    fn level_tracking() {
        let mut s = DiffLogicSolver::new(3);
        assert_eq!(s.current_level(), 0);
        s.new_decision_level();
        assert_eq!(s.current_level(), 1);
        s.assert_leq(1, 2, 5, 0).unwrap();
        assert_eq!(s.num_edges(), 1);
        s.backtrack_to(0);
        assert_eq!(s.num_edges(), 0);
        assert_eq!(s.current_level(), 0);
    }

    #[test]
    fn strict_lt() {
        // x - y < 3 (IDL: x - y ≤ 2), then x - y ≤ 3 — no conflict
        let mut s = DiffLogicSolver::new(2);
        s.assert_lt(1, 2, 3, 0).unwrap();
        s.assert_leq(1, 2, 3, 1).unwrap();
        s.check().unwrap();
    }
}
