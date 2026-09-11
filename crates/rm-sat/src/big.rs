//! Binary Implication Graph (BIG) preprocessing — Phase 4.
//!
//! Builds the directed implication graph from all binary clauses and runs
//! Strongly Connected Component (SCC) analysis via iterative Kosaraju's.
//!
//! Two results are extracted:
//!
//! 1. **UNSAT detection**: if a positive literal and its negation land in the
//!    same SCC there is a circular contradiction that BCP at level 0 cannot
//!    detect on its own (no unit clause seeds the chain).  The formula is
//!    immediately UNSAT.
//!
//! 2. **Equivalency merging**: all literals in the same SCC are mutually
//!    implied (they are logically equivalent).  Each variable is mapped to the
//!    canonical representative of its SCC (the literal with the smallest
//!    variable index in the SCC).  Merging duplicate variables reduces clause
//!    count, watch-list pressure, and removes tautological clauses outright.
//!
//! # Literal encoding
//!
//! BIG node for DIMACS literal `l`:
//! - `l > 0`: node = `2 * (l - 1)`       (positive literal)
//! - `l < 0`: node = `2 * (-l - 1) + 1`  (negative literal)
//!
//! Negation of a BIG node: `node ^ 1`.
//!
//! # Integration
//!
//! `big_preprocess` returns a flat `equiv_map[v]` (1-indexed by variable).
//! Applying it to a DIMACS literal `l`:
//! ```text
//! substituted = if l > 0 { equiv_map[|l|] } else { -equiv_map[|l|] }
//! ```
//! Variables that are already their own representative have `equiv_map[v] = v`.

use crate::dimacs::DimacsCnf;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Result of the BIG/SCC analysis.
#[derive(Debug)]
pub struct BigPreprocessResult {
    /// For each variable v (1-indexed): the canonical representative DIMACS
    /// literal.  Positive means same polarity (v ↔ rep); negative means
    /// opposite polarity (v ↔ ¬|rep|).
    /// Variables that are their own representative have `equiv_map[v] = v`.
    pub equiv_map: Vec<i32>,
    /// Number of variables that were merged (equiv_map[v] != ±v).
    pub n_merged: usize,
    /// True when a literal and its negation are in the same SCC → UNSAT.
    pub unsat: bool,
}

impl Default for BigPreprocessResult {
    fn default() -> Self {
        BigPreprocessResult { equiv_map: Vec::new(), n_merged: 0, unsat: false }
    }
}

/// Substitute DIMACS literal `l` using the equivalency map.
#[inline]
pub fn substitute(l: i32, equiv_map: &[i32]) -> i32 {
    let var = l.unsigned_abs() as usize;
    let rep = equiv_map.get(var).copied().unwrap_or(l);
    if l > 0 { rep } else { -rep }
}

/// Run BIG/SCC analysis and return the preprocessing result.
pub fn big_preprocess(cnf: &DimacsCnf) -> BigPreprocessResult {
    let n = cnf.num_vars as usize;
    if n == 0 {
        return BigPreprocessResult::default();
    }

    let n_lits = 2 * n;

    // Build BIG adjacency.
    // For binary clause (l1 ∨ l2): edges ¬l1 → l2 and ¬l2 → l1.
    let mut adj: Vec<Vec<u32>> = vec![Vec::new(); n_lits];
    for clause in &cnf.clauses {
        if clause.len() != 2 {
            continue;
        }
        let a = clause[0];
        let b = clause[1];
        let node_a = dimacs_to_node(a);
        let node_b = dimacs_to_node(b);
        // ¬a → b
        adj[node_a ^ 1].push(node_b as u32);
        // ¬b → a
        adj[node_b ^ 1].push(node_a as u32);
    }

    let comp = kosaraju(&adj, n_lits);

    // Check UNSAT and build equiv_map.
    let mut equiv_map = vec![0i32; n + 1];

    // For each SCC, find the representative: the literal with the smallest
    // variable (prefer the positive literal on ties).
    let n_scc = *comp.iter().max().unwrap_or(&0) + 1;
    let mut scc_rep: Vec<u32> = vec![u32::MAX; n_scc];

    for lit in 0..n_lits as u32 {
        let scc = comp[lit as usize];
        let cur = scc_rep[scc];
        if cur == u32::MAX {
            scc_rep[scc] = lit;
        } else {
            // Prefer literal with smaller variable; on tie prefer positive (even node).
            let var_cur = cur / 2;
            let var_lit = lit / 2;
            if var_lit < var_cur || (var_lit == var_cur && lit % 2 == 0) {
                scc_rep[scc] = lit;
            }
        }
    }

    let mut n_merged = 0usize;

    for v in 1..=n {
        let pos = (2 * (v - 1)) as u32;
        let neg = pos + 1;

        if comp[pos as usize] == comp[neg as usize] {
            return BigPreprocessResult { equiv_map: vec![0; n + 1], n_merged: 0, unsat: true };
        }

        let scc = comp[pos as usize];
        let rep_node = scc_rep[scc];
        let rep_var = (rep_node / 2 + 1) as i32;
        let rep_is_pos = rep_node % 2 == 0;

        // pos_lit(v) is in the same SCC as rep_node.
        // If rep_node is positive: v ↔ rep_var  → equiv_map[v] = +rep_var.
        // If rep_node is negative: v ↔ ¬rep_var → equiv_map[v] = -rep_var.
        let mapped = if rep_is_pos { rep_var } else { -rep_var };
        equiv_map[v] = mapped;
        if mapped.unsigned_abs() != v as u32 {
            n_merged += 1;
        }
    }

    BigPreprocessResult { equiv_map, n_merged, unsat: false }
}

// ---------------------------------------------------------------------------
// Kosaraju's SCC (fully iterative)
// ---------------------------------------------------------------------------

fn kosaraju(adj: &[Vec<u32>], n: usize) -> Vec<usize> {
    // Pass 1: DFS on original graph — record finish order.
    let mut visited = vec![false; n];
    let mut order = Vec::with_capacity(n);

    for start in 0..n {
        if visited[start] {
            continue;
        }
        // Iterative DFS with (node, edge_index) stack.
        let mut stack: Vec<(usize, usize)> = vec![(start, 0)];
        visited[start] = true;
        while let Some((v, ei)) = stack.last_mut() {
            let v = *v;
            if *ei < adj[v].len() {
                let u = adj[v][*ei] as usize;
                *ei += 1;
                if !visited[u] {
                    visited[u] = true;
                    stack.push((u, 0));
                }
            } else {
                stack.pop();
                order.push(v);
            }
        }
    }

    // Build transposed graph.
    let mut radj: Vec<Vec<u32>> = vec![Vec::new(); n];
    for u in 0..n {
        for &v in &adj[u] {
            radj[v as usize].push(u as u32);
        }
    }

    // Pass 2: DFS on transpose in reverse finish order — assign components.
    let mut comp = vec![usize::MAX; n];
    let mut n_comp = 0usize;

    for &start in order.iter().rev() {
        if comp[start] != usize::MAX {
            continue;
        }
        let mut stack = vec![start];
        comp[start] = n_comp;
        while let Some(v) = stack.pop() {
            for &u in &radj[v] {
                if comp[u as usize] == usize::MAX {
                    comp[u as usize] = n_comp;
                    stack.push(u as usize);
                }
            }
        }
        n_comp += 1;
    }

    comp
}

// ---------------------------------------------------------------------------
// Helper: DIMACS literal → BIG node
// ---------------------------------------------------------------------------

#[inline]
fn dimacs_to_node(l: i32) -> usize {
    if l > 0 {
        2 * (l as usize - 1)
    } else {
        2 * (-l as usize - 1) + 1
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dimacs::parse_dimacs;

    /// (¬a ∨ b) and (¬b ∨ a) — bidirectional implication: a ↔ b.
    #[test]
    fn equivalency_same_polarity() {
        // p cnf 2 2 / -1 2 0 / -2 1 0
        let cnf = parse_dimacs("p cnf 2 2\n-1 2 0\n-2 1 0\n").unwrap();
        let r = big_preprocess(&cnf);
        assert!(!r.unsat, "should not be UNSAT");
        // var 2 should be merged into var 1
        assert_eq!(r.n_merged, 1);
        assert_eq!(r.equiv_map[1], 1);  // var 1 is its own rep
        assert_eq!(r.equiv_map[2], 1);  // var 2 → +var1 (a ↔ b)
    }

    /// (a ∨ b) and (¬a ∨ ¬b) — a ↔ ¬b (anti-equivalency).
    #[test]
    fn equivalency_opposite_polarity() {
        let cnf = parse_dimacs("p cnf 2 2\n1 2 0\n-1 -2 0\n").unwrap();
        let r = big_preprocess(&cnf);
        assert!(!r.unsat, "should not be UNSAT");
        assert_eq!(r.n_merged, 1);
        assert_eq!(r.equiv_map[1], 1);   // var 1 is its own rep
        assert_eq!(r.equiv_map[2], -1);  // var 2 → -var1 (b ↔ ¬a)
    }

    /// Circular binary contradiction: formula is UNSAT but has no unit clauses.
    /// Clauses: (¬x∨y), (¬y∨¬x), (x∨¬y), (y∨x) — x and ¬x in same SCC.
    #[test]
    fn circular_contradiction_detected() {
        let cnf = parse_dimacs("p cnf 2 4\n-1 2 0\n-2 -1 0\n1 -2 0\n2 1 0\n").unwrap();
        let r = big_preprocess(&cnf);
        assert!(r.unsat, "circular binary contradiction should be detected UNSAT");
    }

    /// Random 3-SAT has no binary clauses → no SCC merging, no UNSAT.
    #[test]
    fn random_3sat_no_merging() {
        let mut s = "p cnf 10 20\n".to_string();
        for i in 0..20usize {
            let a = (i % 10 + 1) as i32;
            let b = ((i * 3 + 1) % 10 + 1) as i32;
            let c = ((i * 7 + 5) % 10 + 1) as i32;
            s.push_str(&format!("{} {} {} 0\n", a, -b, c));
        }
        let cnf = parse_dimacs(&s).unwrap();
        let r = big_preprocess(&cnf);
        assert!(!r.unsat);
        assert_eq!(r.n_merged, 0, "ternary-only formula should merge nothing");
    }

    /// Transitive chain: a ↔ b ↔ c. All three should map to a.
    #[test]
    fn transitive_equivalency_chain() {
        // a↔b: (-1 2 0), (-2 1 0)
        // b↔c: (-2 3 0), (-3 2 0)
        let cnf = parse_dimacs("p cnf 3 4\n-1 2 0\n-2 1 0\n-2 3 0\n-3 2 0\n").unwrap();
        let r = big_preprocess(&cnf);
        assert!(!r.unsat);
        assert_eq!(r.n_merged, 2);
        assert_eq!(r.equiv_map[1], 1); // a is its own rep
        assert_eq!(r.equiv_map[2], 1); // b → a
        assert_eq!(r.equiv_map[3], 1); // c → a
    }

    /// Substitution helper: positive and negative literal substitution.
    #[test]
    fn substitute_fn_correct() {
        // equiv: var 2 → -var 1 (b ↔ ¬a)
        let equiv = vec![0i32, 1, -1]; // index 0 unused, index 1 = +1, index 2 = -1
        assert_eq!(substitute(2, &equiv), -1);  // +b → -a
        assert_eq!(substitute(-2, &equiv), 1);  // -b → +a
        assert_eq!(substitute(1, &equiv), 1);   // +a → +a (identity)
        assert_eq!(substitute(-1, &equiv), -1); // -a → -a (identity)
    }
}
