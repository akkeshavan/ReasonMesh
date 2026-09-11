//! AMO (at-most-one) group detection and pseudo-Boolean counting preprocessing.
//!
//! Phase 3 of algorithm selection.  A single O(n+m) pass extracts two kinds of
//! cardinality structure from a CNF:
//!
//! * **AMO groups**: maximal cliques in the "conflict graph" — the undirected
//!   graph whose edges are the binary clauses of the form ¬xi ∨ ¬xj.  A clique
//!   of size k encodes AMO(x1,…,xk): at most one of those variables can be True.
//!
//! * **ALO groups**: all-positive clauses (x1 ∨ … ∨ xk, k ≥ 2).  Each encodes
//!   ALO(x1,…,xk): at least one must be True.
//!
//! After detection a *counting contradiction check* is run on the bipartite
//! (ALO, AMO) structure: if a connected component has more fully-constrained ALO
//! groups than AMO groups, the formula is UNSAT by a counting argument — no
//! assignment can satisfy all the "at least one" demands within the "at most
//! one" capacity.  This cracks Pigeon-Hole Problem instances in O(n+m) time
//! without any CDCL search.
//!
//! The Pigeon-Hole argument in a sentence: n+1 pigeons need ≥ n+1 True
//! variables (one per ALO), but n holes allow ≤ n True variables (one per AMO).

use crate::dimacs::DimacsCnf;
use smallvec::SmallVec;
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Result of the AMO/ALO structural analysis.
#[derive(Debug, Default)]
pub struct AmoPreprocessResult {
    /// Detected AMO groups (each is a clique in the conflict graph, size ≥ 3).
    pub amo_groups: Vec<SmallVec<[u32; 8]>>,
    /// All-positive clauses extracted as ALO groups.
    pub alo_groups: Vec<Vec<u32>>,
    /// True when the bipartite counting argument proves the formula UNSAT.
    pub counting_unsat: bool,
}

/// Run AMO/ALO detection and the counting UNSAT check.
pub fn amo_preprocess(cnf: &DimacsCnf) -> AmoPreprocessResult {
    let amo_groups = detect_amo_groups(cnf);
    let alo_groups = extract_alo_groups(cnf);
    let counting_unsat =
        pb_counting_check(&alo_groups, &amo_groups, cnf.num_vars as usize);
    AmoPreprocessResult { amo_groups, alo_groups, counting_unsat }
}

// ---------------------------------------------------------------------------
// AMO detection: maximal cliques in the conflict graph
// ---------------------------------------------------------------------------

/// Build AMO groups by running a greedy maximal-clique algorithm on the
/// undirected conflict graph (edge u–v iff ¬u ∨ ¬v is a clause).  Only groups
/// of size ≥ 3 are returned (pairs are already handled by binary BCP).
pub fn detect_amo_groups(cnf: &DimacsCnf) -> Vec<SmallVec<[u32; 8]>> {
    let n = cnf.num_vars as usize;
    if n == 0 {
        return Vec::new();
    }

    // Build sorted adjacency lists from negative-negative binary clauses.
    let mut adj: Vec<Vec<u32>> = vec![Vec::new(); n + 1];
    for clause in &cnf.clauses {
        if clause.len() == 2 && clause[0] < 0 && clause[1] < 0 {
            let u = clause[0].unsigned_abs() as usize;
            let v = clause[1].unsigned_abs() as usize;
            if u <= n && v <= n {
                adj[u].push(v as u32);
                adj[v].push(u as u32);
            }
        }
    }
    for a in adj.iter_mut() {
        a.sort_unstable();
        a.dedup();
    }

    let mut in_group = vec![false; n + 1];
    let mut groups: Vec<SmallVec<[u32; 8]>> = Vec::new();

    for start in 1..=(n as u32) {
        let s = start as usize;
        if in_group[s] || adj[s].is_empty() {
            continue;
        }

        let mut clique: SmallVec<[u32; 8]> = SmallVec::new();
        clique.push(start);

        // Candidate set: neighbours of `start` not yet in a group.
        let mut cands: Vec<u32> = adj[s]
            .iter()
            .filter(|&&x| !in_group[x as usize])
            .cloned()
            .collect();

        // Greedily extend: for each candidate, add it if it conflicts with
        // every current clique member, then intersect the candidate set with
        // the new member's neighbours so future candidates are compatible too.
        let mut ci = 0;
        while ci < cands.len() {
            let cand = cands[ci];
            let adj_cand = &adj[cand as usize];
            let fits = clique
                .iter()
                .all(|&c| adj_cand.binary_search(&c).is_ok());
            if fits {
                clique.push(cand);
                // Restrict remaining candidates to those also adjacent to cand.
                let tail: Vec<u32> = cands[ci + 1..]
                    .iter()
                    .filter(|&&x| adj_cand.binary_search(&x).is_ok())
                    .cloned()
                    .collect();
                cands = tail;
                ci = 0;
            } else {
                ci += 1;
            }
        }

        if clique.len() >= 3 {
            for &c in &clique {
                in_group[c as usize] = true;
            }
            groups.push(clique);
        }
    }

    groups
}

// ---------------------------------------------------------------------------
// ALO extraction: all-positive clauses
// ---------------------------------------------------------------------------

fn extract_alo_groups(cnf: &DimacsCnf) -> Vec<Vec<u32>> {
    cnf.clauses
        .iter()
        .filter(|c| c.len() >= 2 && c.iter().all(|&l| l > 0))
        .map(|c| c.iter().map(|&l| l as u32).collect())
        .collect()
}

// ---------------------------------------------------------------------------
// Union-Find (path-halving)
// ---------------------------------------------------------------------------

struct Uf(Vec<usize>);

impl Uf {
    fn new(n: usize) -> Self {
        Uf((0..n).collect())
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.0[x] != x {
            self.0[x] = self.0[self.0[x]]; // path halving
            x = self.0[x];
        }
        x
    }

    fn union(&mut self, x: usize, y: usize) {
        let rx = self.find(x);
        let ry = self.find(y);
        if rx != ry {
            self.0[rx] = ry;
        }
    }
}

// ---------------------------------------------------------------------------
// PB counting check
// ---------------------------------------------------------------------------

/// Return `true` if the ALO / AMO bipartite structure implies a counting
/// contradiction.
///
/// A connected component with `a` fully-constrained ALO groups and `b` AMO
/// groups where `a > b` is UNSAT: we need ≥ a True variables (one per ALO)
/// but the AMO constraints allow ≤ b True variables (one per AMO).
///
/// An ALO group is "fully constrained" when every one of its variables belongs
/// to a unique AMO group.  If any variable is free (no AMO) or appears in
/// multiple AMOs it might be assigned True without violating any AMO — making
/// that ALO trivially satisfiable; those ALOs are excluded from the count.
fn pb_counting_check(
    alo_groups: &[Vec<u32>],
    amo_groups: &[SmallVec<[u32; 8]>],
    n_vars: usize,
) -> bool {
    let n_alo = alo_groups.len();
    let n_amo = amo_groups.len();
    if n_alo == 0 || n_amo == 0 {
        return false;
    }

    // var → unique ALO group index.  usize::MAX = appears in ≥ 2 (ambiguous).
    let mut var_alo: Vec<Option<usize>> = vec![None; n_vars + 1];
    for (i, grp) in alo_groups.iter().enumerate() {
        for &v in grp {
            if (v as usize) <= n_vars {
                var_alo[v as usize] = match var_alo[v as usize] {
                    None => Some(i),
                    Some(_) => Some(usize::MAX),
                };
            }
        }
    }

    // var → unique AMO group index.
    let mut var_amo: Vec<Option<usize>> = vec![None; n_vars + 1];
    for (i, grp) in amo_groups.iter().enumerate() {
        for &v in grp {
            if (v as usize) <= n_vars {
                var_amo[v as usize] = match var_amo[v as usize] {
                    None => Some(i),
                    Some(_) => Some(usize::MAX),
                };
            }
        }
    }

    // An ALO group is fully constrained when every variable in it is uniquely
    // covered by exactly one AMO group.
    let mut alo_constrained = vec![true; n_alo];
    for (i, grp) in alo_groups.iter().enumerate() {
        for &v in grp {
            let in_amo = (v as usize) <= n_vars
                && matches!(var_amo[v as usize], Some(id) if id != usize::MAX);
            if !in_amo {
                alo_constrained[i] = false;
                break;
            }
        }
    }

    // Build bipartite UF: nodes 0..n_alo for ALO groups, n_alo.. for AMO groups.
    let mut uf = Uf::new(n_alo + n_amo);

    for v in 1..=n_vars {
        let a = var_alo[v];
        let b = var_amo[v];
        if let (Some(ai), Some(bi)) = (a, b) {
            if ai != usize::MAX && bi != usize::MAX {
                uf.union(ai, n_alo + bi);
            }
        }
    }

    // Count constrained-ALO and AMO groups per component.
    let mut comp_alo: HashMap<usize, usize> = HashMap::new();
    let mut comp_amo: HashMap<usize, usize> = HashMap::new();

    for (i, _) in alo_groups.iter().enumerate() {
        if alo_constrained[i] {
            let root = uf.find(i);
            *comp_alo.entry(root).or_default() += 1;
        }
    }
    for i in 0..n_amo {
        let root = uf.find(n_alo + i);
        *comp_amo.entry(root).or_default() += 1;
    }

    // UNSAT when any component has more constrained ALOs than AMO slots.
    for (&root, &alo_cnt) in &comp_alo {
        let amo_cnt = comp_amo.get(&root).copied().unwrap_or(0);
        if alo_cnt > amo_cnt {
            return true;
        }
    }

    false
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dimacs::DimacsCnf;

    /// Build PHP(pigeons, holes): pigeons > holes → UNSAT.
    fn php(pigeons: u32, holes: u32) -> DimacsCnf {
        let n = pigeons * holes;
        let mut clauses: Vec<Vec<i32>> = Vec::new();
        let var = |p: u32, h: u32| -> i32 { (p * holes + h + 1) as i32 };
        // ALO: each pigeon goes somewhere
        for p in 0..pigeons {
            clauses.push((0..holes).map(|h| var(p, h)).collect());
        }
        // AMO: at most one pigeon per hole
        for h in 0..holes {
            for p1 in 0..pigeons {
                for p2 in (p1 + 1)..pigeons {
                    clauses.push(vec![-var(p1, h), -var(p2, h)]);
                }
            }
        }
        DimacsCnf { num_vars: n, clauses }
    }

    #[test]
    fn php_5_4_amo_groups_detected() {
        let cnf = php(5, 4);
        let groups = detect_amo_groups(&cnf);
        // 4 holes → 4 AMO groups, each of size 5
        assert_eq!(groups.len(), 4, "expected 4 AMO groups (one per hole)");
        for g in &groups {
            assert_eq!(g.len(), 5, "each AMO group should have 5 members");
        }
    }

    #[test]
    fn php_5_4_counting_unsat() {
        let cnf = php(5, 4);
        let r = amo_preprocess(&cnf);
        assert!(r.counting_unsat, "PHP(5,4) should be detected UNSAT by counting");
        assert_eq!(r.alo_groups.len(), 5);
        assert_eq!(r.amo_groups.len(), 4);
    }

    #[test]
    fn php_12_11_counting_unsat() {
        let cnf = php(12, 11);
        let r = amo_preprocess(&cnf);
        assert!(
            r.counting_unsat,
            "PHP(12,11) must be detected UNSAT by counting"
        );
    }

    #[test]
    fn sat_bipartite_2_2_not_unsat() {
        // PHP(2,2) is satisfiable: 2 pigeons, 2 holes.
        // 2 ALO groups, 2 AMO groups → not a contradiction.
        let cnf = php(2, 2);
        let r = amo_preprocess(&cnf);
        assert!(
            !r.counting_unsat,
            "PHP(2,2) is SAT — counting should not flag it"
        );
    }

    #[test]
    fn random_3sat_no_counting_unsat() {
        // All-ternary formula: no all-positive clauses, no AMO pairs → nothing detected.
        let mut dimacs = "p cnf 20 80\n".to_string();
        for i in 0..80usize {
            let a = (i % 20 + 1) as i32;
            let b = ((i * 7 + 3) % 20 + 1) as i32;
            let c = ((i * 13 + 7) % 20 + 1) as i32;
            let sa = if i % 3 == 0 { -1 } else { 1 };
            let sb = if i % 5 == 0 { -1 } else { 1 };
            let sc = if i % 7 == 0 { -1 } else { 1 };
            dimacs.push_str(&format!("{} {} {} 0\n", sa * a, sb * b, sc * c));
        }
        let cnf = crate::dimacs::parse_dimacs(&dimacs).unwrap();
        let r = amo_preprocess(&cnf);
        assert!(!r.counting_unsat, "random 3-SAT should not trigger counting UNSAT");
    }

    #[test]
    fn php_3_2_counting_unsat() {
        let cnf = php(3, 2);
        let r = amo_preprocess(&cnf);
        assert!(r.counting_unsat, "PHP(3,2) must be detected UNSAT");
    }
}
