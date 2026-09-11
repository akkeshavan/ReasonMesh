//! XOR clause detection and GF(2) Gaussian elimination (GJE).
//!
//! Phase 2 of algorithm selection: detect XOR constraints hidden in the CNF's
//! clause set, run Gaussian elimination over GF(2), and emit implied unit
//! literals. This preprocessing pass runs in O(m log m + k² × n/64) time
//! where m = clauses, k = detected XOR constraints, n = variables.
//!
//! XOR encoding: XOR(v1,...,vk) = r is encoded as 2^(k-1) clauses — one for
//! each assignment that violates the constraint.  Detection works by grouping
//! clauses by their sorted variable set and checking that the sign patterns
//! cover the required XOR-inconsistent assignments.
//!
//! Supported: k = 2 and k = 3. k ≥ 4 is skipped (rare; 2^(k-1) clauses grow
//! exponentially so false positives from coincidence become negligible, but
//! detection cost also grows).

use crate::dimacs::DimacsCnf;
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// XOR constraint representation
// ---------------------------------------------------------------------------

/// An XOR constraint: XOR(vars) = rhs, with variables sorted ascending.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct XorClause {
    /// 1-indexed variable IDs, sorted ascending.
    pub vars: SmallVec<[u32; 8]>,
    /// RHS: XOR(vars) must equal this value.
    pub rhs: bool,
}

impl XorClause {
    /// Count unassigned variables under `assignment[v] = Some(bool) | None`.
    pub fn free_count(&self, assignment: &[Option<bool>]) -> usize {
        self.vars
            .iter()
            .filter(|&&v| assignment.get(v as usize).map(|a| a.is_none()).unwrap_or(true))
            .count()
    }

    /// When exactly one variable is unassigned, return `(var, forced_value)`.
    pub fn forced_literal(&self, assignment: &[Option<bool>]) -> Option<(u32, bool)> {
        let mut free = None;
        let mut partial_xor = self.rhs;
        for &v in &self.vars {
            match assignment.get(v as usize).and_then(|&a| a) {
                Some(val) => partial_xor ^= val,
                None => {
                    if free.is_some() {
                        return None; // more than one free
                    }
                    free = Some(v);
                }
            }
        }
        free.map(|v| (v, partial_xor))
    }

    /// Whether this constraint is satisfied under a complete assignment.
    pub fn is_satisfied(&self, assignment: &[Option<bool>]) -> bool {
        let xor = self
            .vars
            .iter()
            .fold(false, |acc, &v| acc ^ assignment[v as usize].unwrap_or(false));
        xor == self.rhs
    }
}

// ---------------------------------------------------------------------------
// Detection
// ---------------------------------------------------------------------------

/// Scan a CNF for XOR-encodable groups of clauses (k = 2, 3).
///
/// Returns `(xor_clauses, consumed_indices)` where `consumed_indices` are the
/// original clause indices that are fully covered by the detected XOR constraints.
/// A caller may choose to remove those clauses from the CDCL clause database
/// (safe because the XOR constraint is semantically equivalent).
pub fn detect_xor_clauses(cnf: &DimacsCnf) -> (Vec<XorClause>, Vec<usize>) {
    // Group clause indices by sorted variable set.
    // Value: list of (clause_index, neg_parity) where neg_parity = (count_neg % 2 == 1).
    let mut groups: HashMap<SmallVec<[u32; 8]>, SmallVec<[(usize, bool); 8]>> = HashMap::new();

    for (idx, clause) in cnf.clauses.iter().enumerate() {
        let k = clause.len();
        if k < 2 || k > 3 {
            continue;
        }

        // Build sorted variable list and check for repeated variables.
        let mut vars: SmallVec<[u32; 8]> = clause.iter().map(|&l| l.unsigned_abs()).collect();
        vars.sort_unstable();
        if vars.windows(2).any(|w| w[0] == w[1]) {
            continue;
        }

        // Parity of negative literal count.
        let neg_parity = clause.iter().filter(|&&l| l < 0).count() % 2 == 1;
        groups.entry(vars).or_default().push((idx, neg_parity));
    }

    let mut xor_clauses = Vec::new();
    let mut consumed = Vec::new();

    for (vars, entries) in groups {
        let k = vars.len();
        let expected = 1usize << (k - 1); // 2 for k=2, 4 for k=3
        if entries.len() != expected {
            continue;
        }

        // All parities must agree: all EVEN (neg_parity=false → rhs=1)
        // or all ODD (neg_parity=true → rhs=0).
        let first_parity = entries[0].1;
        if !entries.iter().all(|(_, p)| *p == first_parity) {
            continue;
        }

        // rhs = NOT first_parity:
        //   neg_parity=false (all EVEN neg counts) → each clause forbids an
        //   even-parity assignment → XOR = 1 (odd-parity assignments satisfy the constraint)
        //   neg_parity=true (all ODD) → XOR = 0
        let rhs = !first_parity;
        xor_clauses.push(XorClause { vars, rhs });
        consumed.extend(entries.iter().map(|(i, _)| *i));
    }

    consumed.sort_unstable();
    (xor_clauses, consumed)
}

/// Fast approximation of XOR density for the classifier: scan binary clauses only
/// and count variable pairs that appear in both complementary sign forms.
///
/// Returns (xor_pair_count * 2) / total_clauses — the fraction of clauses
/// participating in binary XOR constraints.
pub fn xor_density_approx(cnf: &DimacsCnf) -> f32 {
    if cnf.clauses.is_empty() {
        return 0.0;
    }

    // For each ordered variable pair (v1 < v2), track which sign combinations appear.
    // Bit 0 = (+,+), bit 1 = (+,−), bit 2 = (−,+), bit 3 = (−,−)
    // XOR pair: bits {0,3} both set OR bits {1,2} both set.
    let mut pair_signs: HashMap<(u32, u32), u8> = HashMap::new();
    let mut binary_count = 0usize;

    for clause in &cnf.clauses {
        if clause.len() != 2 {
            continue;
        }
        binary_count += 1;
        let la = clause[0];
        let lb = clause[1];
        let va = la.unsigned_abs();
        let vb = lb.unsigned_abs();
        let (v1, v2, a_neg, b_neg) = if va < vb {
            (va, vb, la < 0, lb < 0)
        } else {
            (vb, va, lb < 0, la < 0)
        };
        let bit = ((a_neg as u8) << 1) | (b_neg as u8);
        *pair_signs.entry((v1, v2)).or_insert(0) |= 1 << bit;
    }

    if binary_count == 0 {
        return 0.0;
    }

    let xor_pairs = pair_signs
        .values()
        .filter(|&&s| (s & 0b1001) == 0b1001 || (s & 0b0110) == 0b0110)
        .count();

    // Each XOR pair consumes 2 clauses.
    (xor_pairs * 2) as f32 / cnf.clauses.len() as f32
}

// ---------------------------------------------------------------------------
// GF(2) Gaussian-Jordan Elimination
// ---------------------------------------------------------------------------

/// A bit-packed row in the GJE matrix. Bit i (0-indexed) corresponds to
/// variable (i+1).
#[derive(Clone)]
struct GjeRow {
    words: Vec<u64>,
    rhs: bool,
}

impl GjeRow {
    fn new(n_words: usize) -> Self {
        GjeRow {
            words: vec![0u64; n_words],
            rhs: false,
        }
    }

    #[inline]
    fn get_bit(&self, col: usize) -> bool {
        let (w, b) = (col / 64, col % 64);
        w < self.words.len() && self.words[w] & (1u64 << b) != 0
    }

    #[inline]
    fn set_bit(&mut self, col: usize) {
        self.words[col / 64] |= 1u64 << (col % 64);
    }

    #[inline]
    fn clear_bit(&mut self, col: usize) {
        self.words[col / 64] &= !(1u64 << (col % 64));
    }

    fn xor_assign(&mut self, other: &GjeRow) {
        for (w, &ow) in self.words.iter_mut().zip(&other.words) {
            *w ^= ow;
        }
        self.rhs ^= other.rhs;
    }

    fn is_all_zero(&self) -> bool {
        self.words.iter().all(|&w| w == 0)
    }

    fn count_ones(&self) -> u32 {
        self.words.iter().map(|w| w.count_ones()).sum()
    }

    /// Return the column index (0-based) of the first set bit, or None.
    fn first_set_col(&self) -> Option<usize> {
        for (i, &w) in self.words.iter().enumerate() {
            if w != 0 {
                return Some(i * 64 + w.trailing_zeros() as usize);
            }
        }
        None
    }
}

/// Result of GJE reduction.
pub struct GjeResult {
    /// Variables that are uniquely forced by the XOR system, with their values.
    pub forced: Vec<(u32, bool)>,
    /// True if the system contains a contradiction (empty row with rhs = 1).
    pub unsat: bool,
}

/// GF(2) matrix for Gaussian-Jordan elimination over an XOR constraint system.
pub struct GjeMatrix {
    rows: Vec<GjeRow>,
    n_vars: usize,
    n_words: usize,
}

impl GjeMatrix {
    /// Build a matrix from a list of XOR constraints and the variable count.
    pub fn new(xor_clauses: &[XorClause], n_vars: u32) -> Self {
        let n_vars = n_vars as usize;
        let n_words = (n_vars + 63) / 64;
        let mut rows = Vec::with_capacity(xor_clauses.len());
        for xc in xor_clauses {
            let mut row = GjeRow::new(n_words);
            for &v in &xc.vars {
                row.set_bit((v - 1) as usize);
            }
            row.rhs = xc.rhs;
            rows.push(row);
        }
        GjeMatrix {
            rows,
            n_vars,
            n_words,
        }
    }

    /// Run full Gauss-Jordan elimination and return forced literals and
    /// contradiction status.
    pub fn eliminate(&mut self) -> GjeResult {
        let mut pivot_idx = 0;

        for col in 0..self.n_vars {
            // Find a pivot row at or below the current frontier.
            let mut found = None;
            for r in pivot_idx..self.rows.len() {
                if self.rows[r].get_bit(col) {
                    found = Some(r);
                    break;
                }
            }
            let Some(p) = found else { continue };

            self.rows.swap(p, pivot_idx);

            // Eliminate column from all other rows.
            let pivot = self.rows[pivot_idx].clone();
            for r in 0..self.rows.len() {
                if r != pivot_idx && self.rows[r].get_bit(col) {
                    self.rows[r].xor_assign(&pivot);
                }
            }
            pivot_idx += 1;
        }

        self.collect_results()
    }

    /// Substitute known variable assignments into the matrix, then re-eliminate.
    /// Each pair `(var, value)` in `assignments` is a 1-indexed variable with its
    /// known value. Rows that become unit after substitution yield new forced literals.
    pub fn assign_and_eliminate(&mut self, assignments: &[(u32, bool)]) -> GjeResult {
        for &(var, val) in assignments {
            let col = (var - 1) as usize;
            for row in &mut self.rows {
                if row.get_bit(col) {
                    row.clear_bit(col);
                    if val {
                        row.rhs ^= true;
                    }
                }
            }
        }
        self.eliminate()
    }

    fn collect_results(&self) -> GjeResult {
        let mut forced = Vec::new();
        let mut unsat = false;
        for row in &self.rows {
            if row.is_all_zero() {
                if row.rhs {
                    unsat = true;
                }
            } else if row.count_ones() == 1 {
                let col = row.first_set_col().unwrap();
                forced.push((col as u32 + 1, row.rhs));
            }
        }
        GjeResult { forced, unsat }
    }

    /// Number of XOR constraints currently in the matrix.
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dimacs::parse_dimacs;

    fn xor2_cnf(a: u32, b: u32, rhs: bool) -> DimacsCnf {
        // XOR(a, b) = rhs encoded as 2 binary clauses
        let n = a.max(b);
        let clauses = if rhs {
            // XOR=1: forbid (0,0) and (1,1)
            vec![vec![a as i32, b as i32], vec![-(a as i32), -(b as i32)]]
        } else {
            // XOR=0: forbid (0,1) and (1,0)
            vec![vec![a as i32, -(b as i32)], vec![-(a as i32), b as i32]]
        };
        DimacsCnf {
            num_vars: n,
            clauses,
        }
    }

    fn xor3_cnf(a: u32, b: u32, c: u32, rhs: bool) -> DimacsCnf {
        let n = a.max(b).max(c);
        let a = a as i32;
        let b = b as i32;
        let c = c as i32;
        let clauses = if rhs {
            // XOR=1: even neg-count clauses
            vec![
                vec![a, b, c],
                vec![a, -b, -c],
                vec![-a, b, -c],
                vec![-a, -b, c],
            ]
        } else {
            // XOR=0: odd neg-count clauses
            vec![
                vec![a, b, -c],
                vec![a, -b, c],
                vec![-a, b, c],
                vec![-a, -b, -c],
            ]
        };
        DimacsCnf {
            num_vars: n,
            clauses,
        }
    }

    #[test]
    fn detects_k2_xor1() {
        let cnf = xor2_cnf(1, 2, true);
        let (xors, consumed) = detect_xor_clauses(&cnf);
        assert_eq!(xors.len(), 1);
        assert_eq!(xors[0].vars.as_slice(), &[1, 2]);
        assert!(xors[0].rhs);
        assert_eq!(consumed.len(), 2);
    }

    #[test]
    fn detects_k2_xor0() {
        let cnf = xor2_cnf(3, 5, false);
        let (xors, _) = detect_xor_clauses(&cnf);
        assert_eq!(xors.len(), 1);
        assert_eq!(xors[0].vars.as_slice(), &[3, 5]);
        assert!(!xors[0].rhs);
    }

    #[test]
    fn detects_k3_xor1() {
        let cnf = xor3_cnf(1, 2, 3, true);
        let (xors, consumed) = detect_xor_clauses(&cnf);
        assert_eq!(xors.len(), 1);
        assert!(xors[0].rhs);
        assert_eq!(consumed.len(), 4);
    }

    #[test]
    fn detects_k3_xor0() {
        let cnf = xor3_cnf(2, 4, 6, false);
        let (xors, _) = detect_xor_clauses(&cnf);
        assert_eq!(xors.len(), 1);
        assert!(!xors[0].rhs);
    }

    #[test]
    fn no_xor_in_random_3sat() {
        let dimacs = "p cnf 10 5\n1 2 3 0\n-1 -2 4 0\n3 -4 5 0\n-2 3 -5 0\n1 -3 5 0\n";
        let cnf = parse_dimacs(dimacs).unwrap();
        let (xors, _) = detect_xor_clauses(&cnf);
        assert!(xors.is_empty());
    }

    #[test]
    fn gje_forces_unit_from_two_xor() {
        // XOR(1,2)=1 and XOR(2,3)=0 → combined: XOR(1,3)=1 (derived)
        // After assigning var3=true: XOR(1,3)=1 → var1=false
        let xors = vec![
            XorClause {
                vars: SmallVec::from_slice(&[1, 2]),
                rhs: true,
            },
            XorClause {
                vars: SmallVec::from_slice(&[2, 3]),
                rhs: false,
            },
        ];
        let mut mat = GjeMatrix::new(&xors, 3);
        // Assign var3 = true
        let result = mat.assign_and_eliminate(&[(3, true)]);
        assert!(!result.unsat);
        // With var3=true and XOR(2,3)=0 → var2=true
        // With var2=true and XOR(1,2)=1 → var1=false
        let forced: std::collections::HashMap<u32, bool> = result.forced.into_iter().collect();
        assert_eq!(forced.get(&1), Some(&false));
        assert_eq!(forced.get(&2), Some(&true));
    }

    #[test]
    fn gje_detects_contradiction() {
        // XOR(1,2)=1 and XOR(1,2)=0 → contradiction
        let xors = vec![
            XorClause {
                vars: SmallVec::from_slice(&[1, 2]),
                rhs: true,
            },
            XorClause {
                vars: SmallVec::from_slice(&[1, 2]),
                rhs: false,
            },
        ];
        let mut mat = GjeMatrix::new(&xors, 2);
        let result = mat.eliminate();
        assert!(result.unsat);
    }

    #[test]
    fn gje_no_force_two_free() {
        // XOR(1,2)=1 alone — neither variable forced.
        let xors = vec![XorClause {
            vars: SmallVec::from_slice(&[1, 2]),
            rhs: true,
        }];
        let mut mat = GjeMatrix::new(&xors, 2);
        let result = mat.eliminate();
        assert!(!result.unsat);
        assert!(result.forced.is_empty());
    }

    #[test]
    fn xor_density_approx_detects_pairs() {
        let cnf = xor2_cnf(1, 2, true);
        let d = xor_density_approx(&cnf);
        assert!(d > 0.9, "expected density near 1.0, got {d}");
    }
}
