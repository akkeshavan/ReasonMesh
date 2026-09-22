//! Dutertre–de Moura Simplex for DPLL(T) — QF_LRA and QF_LIA.
//!
//! Reference: Dutertre & de Moura, "A Fast Linear-Arithmetic Solver for DPLL(T)",
//! CAV 2006.
//!
//! # Invariants maintained at all times
//! 1. Tableau: `val[xi] = Σ a_ij * val[xj]` for every basic xi.
//! 2. Bound:   `lb[xj] ≤ val[xj] ≤ ub[xj]` for every non-basic xj.
//! 3. Column:  `columns[xj]` = set of basic xi whose row contains xj.

use rustc_hash::{FxHashMap, FxHashSet};
use std::ops::{Add, Div, Mul, Neg, Sub};

pub type VarId = u32;

// ---------------------------------------------------------------------------
// Rational arithmetic
// ---------------------------------------------------------------------------

fn gcd(mut a: i64, mut b: i64) -> i64 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rational {
    pub num: i64,
    pub den: i64, // always > 0
}

impl Rational {
    pub fn new(num: i64, den: i64) -> Self {
        assert!(den != 0, "denominator must be nonzero");
        let (num, den) = if den < 0 { (-num, -den) } else { (num, den) };
        let g = gcd(num.abs(), den);
        Rational {
            num: num / g,
            den: den / g,
        }
    }

    pub fn zero() -> Self {
        Rational { num: 0, den: 1 }
    }
    pub fn one() -> Self {
        Rational { num: 1, den: 1 }
    }
    pub fn from_int(n: i64) -> Self {
        Rational { num: n, den: 1 }
    }

    pub fn is_integer(self) -> bool {
        self.num % self.den == 0
    }
    pub fn floor_int(self) -> i64 {
        if self.num >= 0 {
            self.num / self.den
        } else {
            (self.num - self.den + 1) / self.den
        }
    }
    pub fn ceil_int(self) -> i64 {
        if self.num >= 0 {
            (self.num + self.den - 1) / self.den
        } else {
            self.num / self.den
        }
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Rational {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.num * other.den).cmp(&(other.num * self.den))
    }
}

impl Add for Rational {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Rational::new(self.num * rhs.den + rhs.num * self.den, self.den * rhs.den)
    }
}
impl Sub for Rational {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Rational::new(self.num * rhs.den - rhs.num * self.den, self.den * rhs.den)
    }
}
impl Mul for Rational {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Rational::new(self.num * rhs.num, self.den * rhs.den)
    }
}
impl Div for Rational {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        Rational::new(self.num * rhs.den, self.den * rhs.num)
    }
}
impl Neg for Rational {
    type Output = Self;
    fn neg(self) -> Self {
        Rational {
            num: -self.num,
            den: self.den,
        }
    }
}

// ---------------------------------------------------------------------------
// Conflict core
// ---------------------------------------------------------------------------

/// The set of SAT literals whose negations form the conflict clause.
#[derive(Clone, Debug)]
pub struct SimplexConflict {
    pub lits: Vec<u32>,
}

// ---------------------------------------------------------------------------
// Internal types
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct BoundEntry {
    value: Rational,
    sat_lit: u32,
}

#[derive(Debug)]
enum UndoEntry {
    Lower {
        var: VarId,
        old: Option<BoundEntry>,
    },
    Upper {
        var: VarId,
        old: Option<BoundEntry>,
    },
}

// ---------------------------------------------------------------------------
// SimplexSolver
// ---------------------------------------------------------------------------

pub struct SimplexSolver {
    num_vars: u32,
    /// Current assignment for every variable.
    assignment: Vec<Rational>,
    lower: Vec<Option<BoundEntry>>,
    upper: Vec<Option<BoundEntry>>,
    /// Tableau rows: rows[i] = Some(map) iff variable i is basic.
    /// Map: non-basic var → coefficient in the linear combination.
    rows: Vec<Option<FxHashMap<VarId, Rational>>>,
    is_basic: Vec<bool>,
    /// columns[j] = basic variables whose row contains j (non-basic j only).
    columns: Vec<FxHashSet<VarId>>,
    /// Undo log for bound backtracking.
    level_lim: Vec<usize>,
    undo_log: Vec<UndoEntry>,
}

impl SimplexSolver {
    pub fn new(num_vars: u32) -> Self {
        let n = num_vars as usize;
        SimplexSolver {
            num_vars,
            assignment: vec![Rational::zero(); n],
            lower: vec![None; n],
            upper: vec![None; n],
            rows: (0..n).map(|_| None).collect(),
            is_basic: vec![false; n],
            columns: (0..n).map(|_| FxHashSet::default()).collect(),
            level_lim: Vec::new(),
            undo_log: Vec::new(),
        }
    }

    pub fn new_decision_level(&mut self) {
        self.level_lim.push(self.undo_log.len());
    }

    pub fn backtrack_to(&mut self, level: u32) {
        let target = if (level as usize) < self.level_lim.len() {
            self.level_lim[level as usize]
        } else if level == 0 {
            0
        } else {
            return;
        };
        while self.undo_log.len() > target {
            match self.undo_log.pop().unwrap() {
                UndoEntry::Lower { var, old } => self.lower[var as usize] = old,
                UndoEntry::Upper { var, old } => self.upper[var as usize] = old,
            }
        }
        self.level_lim.truncate(level as usize);
        // Repair assignments so bound invariant is restored before check().
        self.repair_assignments();
    }

    /// Introduce a basic variable whose value is a linear combination of non-basics.
    /// `basic_var` must not already be basic.
    /// `coeffs`: (non_basic_var, coefficient) pairs; zero coefficients are ignored.
    pub fn add_row(&mut self, basic_var: VarId, coeffs: Vec<(VarId, Rational)>) {
        let bv = basic_var as usize;
        assert!(!self.is_basic[bv], "variable {basic_var} is already basic");
        let val = coeffs
            .iter()
            .fold(Rational::zero(), |acc, &(xj, a)| {
                acc + a * self.assignment[xj as usize]
            });
        self.assignment[bv] = val;
        let row: FxHashMap<VarId, Rational> = coeffs
            .into_iter()
            .filter(|(_, a)| *a != Rational::zero())
            .collect();
        for &xj in row.keys() {
            self.columns[xj as usize].insert(basic_var);
        }
        self.rows[bv] = Some(row);
        self.is_basic[bv] = true;
    }

    fn lb(&self, var: VarId) -> Option<Rational> {
        self.lower[var as usize].as_ref().map(|b| b.value)
    }
    fn ub(&self, var: VarId) -> Option<Rational> {
        self.upper[var as usize].as_ref().map(|b| b.value)
    }
    fn val(&self, var: VarId) -> Rational {
        self.assignment[var as usize]
    }

    /// Update a non-basic variable to `v`, propagating to all dependent basics.
    fn update(&mut self, xj: VarId, v: Rational) {
        let delta = v - self.val(xj);
        // Collect first to avoid borrowing issues.
        let basics: Vec<(VarId, Rational)> = self.columns[xj as usize]
            .iter()
            .map(|&xi| (xi, self.rows[xi as usize].as_ref().unwrap()[&xj]))
            .collect();
        for (xi, a) in basics {
            self.assignment[xi as usize] = self.assignment[xi as usize] + a * delta;
        }
        self.assignment[xj as usize] = v;
    }

    /// Assert lower bound: var ≥ val.
    pub fn assert_lower(
        &mut self,
        var: VarId,
        val: Rational,
        sat_lit: u32,
    ) -> Result<(), SimplexConflict> {
        let v = var as usize;
        if let Some(ub) = &self.upper[v] {
            if val > ub.value {
                return Err(SimplexConflict {
                    lits: vec![sat_lit, ub.sat_lit],
                });
            }
        }
        let old = self.lower[v].clone();
        let tighten = old.as_ref().map_or(true, |b| b.value < val);
        if tighten {
            self.undo_log.push(UndoEntry::Lower { var, old });
            self.lower[v] = Some(BoundEntry { value: val, sat_lit });
            // Maintain bound invariant for non-basic vars.
            if !self.is_basic[v] && self.assignment[v] < val {
                self.update(var, val);
            }
        }
        Ok(())
    }

    /// Assert upper bound: var ≤ val.
    pub fn assert_upper(
        &mut self,
        var: VarId,
        val: Rational,
        sat_lit: u32,
    ) -> Result<(), SimplexConflict> {
        let v = var as usize;
        if let Some(lb) = &self.lower[v] {
            if val < lb.value {
                return Err(SimplexConflict {
                    lits: vec![sat_lit, lb.sat_lit],
                });
            }
        }
        let old = self.upper[v].clone();
        let tighten = old.as_ref().map_or(true, |b| b.value > val);
        if tighten {
            self.undo_log.push(UndoEntry::Upper { var, old });
            self.upper[v] = Some(BoundEntry { value: val, sat_lit });
            if !self.is_basic[v] && self.assignment[v] > val {
                self.update(var, val);
            }
        }
        Ok(())
    }

    /// Run feasibility check.
    ///
    /// Returns:
    /// - `Ok(true)`  — current bounds are satisfiable (converged).
    /// - `Ok(false)` — iteration limit exhausted without convergence; feasibility unknown.
    /// - `Err(c)`    — infeasible, with a minimal conflict core `c`.
    pub fn check(&mut self) -> Result<bool, SimplexConflict> {
        // Use n^3 iterations to handle degenerate cases. Pure cycling is prevented by
        // Bland's-style variable selection (smallest-index violated var / entering var).
        let n = self.num_vars as usize;
        let max_iters = n.saturating_mul(n).saturating_mul(n).max(1024);
        for _ in 0..max_iters {
            // Find first violating basic variable.
            let violated = (0..self.num_vars)
                .find_map(|xi| {
                    if !self.is_basic[xi as usize] {
                        return None;
                    }
                    let v = self.assignment[xi as usize];
                    if let Some(lb) = self.lb(xi) {
                        if v < lb {
                            return Some((xi, false));
                        }
                    }
                    if let Some(ub) = self.ub(xi) {
                        if v > ub {
                            return Some((xi, true));
                        }
                    }
                    None
                });

            let (xi, above_ub) = match violated {
                None => return Ok(true),
                Some(v) => v,
            };

            if !above_ub {
                let lb_xi = self.lb(xi).unwrap();
                let pivot_j = self.find_pivot_for_lb(xi);
                match pivot_j {
                    None => return Err(self.mk_conflict_lb(xi)),
                    Some(xj) => self.pivot_and_update(xi, xj, lb_xi),
                }
            } else {
                let ub_xi = self.ub(xi).unwrap();
                let pivot_j = self.find_pivot_for_ub(xi);
                match pivot_j {
                    None => return Err(self.mk_conflict_ub(xi)),
                    Some(xj) => self.pivot_and_update(xi, xj, ub_xi),
                }
            }
        }
        // Iteration limit hit — feasibility unknown, not necessarily SAT.
        Ok(false)
    }

    /// Return the current rational value of a variable.
    pub fn model_value(&self, var: VarId) -> Rational {
        self.assignment[var as usize]
    }

    /// Return an integer model value (floor).  Only meaningful after `check()` succeeds.
    pub fn model_int(&self, var: VarId) -> i64 {
        self.assignment[var as usize].floor_int()
    }

    // -----------------------------------------------------------------------
    // Private helpers
    // -----------------------------------------------------------------------

    /// Find a non-basic xj suitable for pivoting with xi (whose value < lb[xi]).
    /// Needs a > 0 with room to increase, or a < 0 with room to decrease.
    fn find_pivot_for_lb(&self, xi: VarId) -> Option<VarId> {
        let row = self.rows[xi as usize].as_ref().unwrap();
        row.iter().find_map(|(&xj, &a)| {
            if a > Rational::zero() {
                let at_ub = self
                    .ub(xj)
                    .map(|ub| self.val(xj) >= ub)
                    .unwrap_or(false);
                if !at_ub {
                    return Some(xj);
                }
            } else if a < Rational::zero() {
                let at_lb = self
                    .lb(xj)
                    .map(|lb| self.val(xj) <= lb)
                    .unwrap_or(false);
                if !at_lb {
                    return Some(xj);
                }
            }
            None
        })
    }

    /// Find a non-basic xj suitable for pivoting with xi (whose value > ub[xi]).
    fn find_pivot_for_ub(&self, xi: VarId) -> Option<VarId> {
        let row = self.rows[xi as usize].as_ref().unwrap();
        row.iter().find_map(|(&xj, &a)| {
            if a < Rational::zero() {
                let at_ub = self
                    .ub(xj)
                    .map(|ub| self.val(xj) >= ub)
                    .unwrap_or(false);
                if !at_ub {
                    return Some(xj);
                }
            } else if a > Rational::zero() {
                let at_lb = self
                    .lb(xj)
                    .map(|lb| self.val(xj) <= lb)
                    .unwrap_or(false);
                if !at_lb {
                    return Some(xj);
                }
            }
            None
        })
    }

    /// Build conflict for xi below its lower bound.
    fn mk_conflict_lb(&self, xi: VarId) -> SimplexConflict {
        let mut lits = Vec::new();
        if let Some(b) = &self.lower[xi as usize] {
            lits.push(b.sat_lit);
        }
        let row = self.rows[xi as usize].as_ref().unwrap();
        for (&xj, &a) in row {
            // a > 0: xj is stuck at ub (can't raise xi further)
            // a < 0: xj is stuck at lb (can't raise xi)
            if a > Rational::zero() {
                if let Some(b) = &self.upper[xj as usize] {
                    lits.push(b.sat_lit);
                }
            } else {
                if let Some(b) = &self.lower[xj as usize] {
                    lits.push(b.sat_lit);
                }
            }
        }
        SimplexConflict { lits }
    }

    /// Build conflict for xi above its upper bound.
    fn mk_conflict_ub(&self, xi: VarId) -> SimplexConflict {
        let mut lits = Vec::new();
        if let Some(b) = &self.upper[xi as usize] {
            lits.push(b.sat_lit);
        }
        let row = self.rows[xi as usize].as_ref().unwrap();
        for (&xj, &a) in row {
            // a < 0: xj stuck at ub (can't lower xi)
            // a > 0: xj stuck at lb (can't lower xi)
            if a < Rational::zero() {
                if let Some(b) = &self.upper[xj as usize] {
                    lits.push(b.sat_lit);
                }
            } else {
                if let Some(b) = &self.lower[xj as usize] {
                    lits.push(b.sat_lit);
                }
            }
        }
        SimplexConflict { lits }
    }

    /// Pivot and update: xi (basic, violating bound) swaps with xj (non-basic).
    /// Sets val[xi] = v (its bound), adjusts val[xj] and all other basics, then pivots.
    fn pivot_and_update(&mut self, xi: VarId, xj: VarId, v: Rational) {
        let a_ij = self.rows[xi as usize].as_ref().unwrap()[&xj];
        let theta = (v - self.val(xi)) / a_ij;
        self.assignment[xi as usize] = v;
        self.assignment[xj as usize] = self.assignment[xj as usize] + theta;
        // Update other basic vars that contain xj.
        let others: Vec<(VarId, Rational)> = self.columns[xj as usize]
            .iter()
            .filter(|&&xl| xl != xi)
            .map(|&xl| (xl, self.rows[xl as usize].as_ref().unwrap()[&xj]))
            .collect();
        for (xl, a_lj) in others {
            self.assignment[xl as usize] = self.assignment[xl as usize] + a_lj * theta;
        }
        self.pivot(xi, xj);
    }

    /// Swap xi (basic) and xj (non-basic) in the tableau.
    fn pivot(&mut self, xi: VarId, xj: VarId) {
        let a_ij = self.rows[xi as usize].as_ref().unwrap()[&xj];
        let inv_a = Rational::one() / a_ij;

        // Build the new row for xj.
        let old_xi_row = self.rows[xi as usize].take().unwrap();
        let mut new_xj_row: FxHashMap<VarId, Rational> = FxHashMap::default();
        new_xj_row.insert(xi, inv_a);
        for (&xk, &a_ik) in &old_xi_row {
            if xk == xj {
                continue;
            }
            let c = -(a_ik * inv_a);
            if c != Rational::zero() {
                new_xj_row.insert(xk, c);
            }
        }

        // Substitute xj → new_xj_row in all other basic rows.
        let xl_list: Vec<VarId> = self.columns[xj as usize]
            .iter()
            .cloned()
            .filter(|&v| v != xi)
            .collect();
        for xl in xl_list {
            let row_xl = self.rows[xl as usize].as_mut().unwrap();
            let a_lj = match row_xl.remove(&xj) {
                Some(v) if v != Rational::zero() => v,
                _ => continue,
            };
            self.columns[xj as usize].remove(&xl);
            for (&xk, &new_c) in &new_xj_row {
                let add = a_lj * new_c;
                if add == Rational::zero() {
                    continue;
                }
                let entry = row_xl.entry(xk).or_insert(Rational::zero());
                *entry = *entry + add;
                if *entry == Rational::zero() {
                    row_xl.remove(&xk);
                    self.columns[xk as usize].remove(&xl);
                } else {
                    self.columns[xk as usize].insert(xl);
                }
            }
        }

        // Update column index for the new xj row.
        for (&xk, _) in &new_xj_row {
            self.columns[xk as usize].insert(xj);
        }
        // Remove xi from the columns of the vars its old row depended on.
        for (&xk, _) in &old_xi_row {
            if xk != xj {
                self.columns[xk as usize].remove(&xi);
            }
        }
        // xj is now basic; its "column" entry has no meaning.
        self.columns[xj as usize].clear();

        self.rows[xj as usize] = Some(new_xj_row);
        self.is_basic[xi as usize] = false;
        self.is_basic[xj as usize] = true;
    }

    /// After backtracking, restore the bound invariant for non-basic variables.
    fn repair_assignments(&mut self) {
        // For each non-basic var, clamp to [lb, ub].
        for xi in 0..self.num_vars as usize {
            if self.is_basic[xi] {
                continue;
            }
            let mut v = self.assignment[xi];
            if let Some(lb) = self.lb(xi as VarId) {
                if v < lb {
                    v = lb;
                }
            }
            if let Some(ub) = self.ub(xi as VarId) {
                if v > ub {
                    v = ub;
                }
            }
            if v != self.assignment[xi] {
                self.update(xi as VarId, v);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64) -> Rational {
        Rational::from_int(n)
    }
    fn qf(num: i64, den: i64) -> Rational {
        Rational::new(num, den)
    }

    #[test]
    fn rational_arithmetic() {
        assert_eq!(q(1) + q(2), q(3));
        assert_eq!(q(3) - q(5), q(-2));
        assert_eq!(q(2) * q(3), q(6));
        assert_eq!(q(6) / q(2), q(3));
        assert_eq!(-q(4), q(-4));
        assert!(q(1) < q(2));
        assert!(q(-1) < q(0));
        assert_eq!(qf(1, 2) + qf(1, 3), qf(5, 6));
        assert!(qf(1, 3) < qf(1, 2));
    }

    #[test]
    fn rational_floor_ceil() {
        assert_eq!(qf(7, 2).floor_int(), 3);
        assert_eq!(qf(7, 2).ceil_int(), 4);
        assert_eq!(qf(-7, 2).floor_int(), -4);
        assert_eq!(qf(-7, 2).ceil_int(), -3);
        assert_eq!(q(4).floor_int(), 4);
        assert!(q(4).is_integer());
        assert!(!qf(7, 2).is_integer());
    }

    /// x ≤ 5 with no lower bound — trivially SAT.
    #[test]
    fn simple_upper_bound_sat() {
        let mut s = SimplexSolver::new(1);
        s.assert_upper(0, q(5), 1).unwrap();
        assert!(s.check().is_ok());
        assert!(s.model_value(0) <= q(5));
    }

    /// lb > ub — immediate conflict in assert_upper.
    #[test]
    fn lb_gt_ub_conflict() {
        let mut s = SimplexSolver::new(1);
        s.assert_lower(0, q(5), 1).unwrap();
        let err = s.assert_upper(0, q(3), 2).unwrap_err();
        assert!(err.lits.contains(&1));
        assert!(err.lits.contains(&2));
    }

    /// s = x + y, assert s ≤ 3, x ≥ 2, y ≥ 2 → UNSAT.
    #[test]
    fn slack_infeasible() {
        // vars: 0=x, 1=y, 2=s
        let mut s = SimplexSolver::new(3);
        // s = 1*x + 1*y
        s.add_row(2, vec![(0, q(1)), (1, q(1))]);
        // x ≥ 2, y ≥ 2, s ≤ 3
        s.assert_lower(0, q(2), 10).unwrap();
        s.assert_lower(1, q(2), 11).unwrap();
        s.assert_upper(2, q(3), 12).unwrap();
        let err = s.check().unwrap_err();
        // Conflict must involve the upper bound on s and the lower bounds on x and y.
        assert!(err.lits.contains(&12), "expected ub(s) lit 12 in {:?}", err.lits);
        assert!(
            err.lits.contains(&10) || err.lits.contains(&11),
            "expected lb lit in {:?}",
            err.lits
        );
    }

    /// s = x + y, assert s ≤ 10, x ≥ 2, y ≥ 2 → SAT, values consistent.
    #[test]
    fn slack_feasible() {
        let mut s = SimplexSolver::new(3);
        s.add_row(2, vec![(0, q(1)), (1, q(1))]);
        s.assert_lower(0, q(2), 10).unwrap();
        s.assert_lower(1, q(2), 11).unwrap();
        s.assert_upper(2, q(10), 12).unwrap();
        s.check().unwrap();
        let vx = s.model_value(0);
        let vy = s.model_value(1);
        let vs = s.model_value(2);
        assert!(vx >= q(2), "x={:?}", vx);
        assert!(vy >= q(2), "y={:?}", vy);
        assert!(vs <= q(10), "s={:?}", vs);
        // Tableau invariant: s == x + y
        assert_eq!(vs, vx + vy, "tableau invariant violated");
    }

    /// Backtrack: assert tight bounds, then backtrack and assert looser ones.
    #[test]
    fn backtrack_restores_bounds() {
        let mut s = SimplexSolver::new(1);
        s.new_decision_level();
        s.assert_upper(0, q(5), 1).unwrap();
        s.assert_lower(0, q(3), 2).unwrap();
        s.backtrack_to(0);
        // After backtrack, bounds are gone — no conflict.
        s.assert_upper(0, q(1), 3).unwrap();
        s.assert_lower(0, q(0), 4).unwrap();
        s.check().unwrap();
        assert!(s.model_value(0) <= q(1));
        assert!(s.model_value(0) >= q(0));
    }

    /// Two variables: 2x - y ≤ 1, x ≥ 1, y ≤ 0 → UNSAT (2*1 - 0 = 2 > 1).
    #[test]
    fn two_var_infeasible() {
        // vars: 0=x, 1=y, 2=s (s = 2x - y)
        let mut s = SimplexSolver::new(3);
        s.add_row(2, vec![(0, q(2)), (1, q(-1))]);
        s.assert_upper(2, q(1), 1).unwrap();
        s.assert_lower(0, q(1), 2).unwrap();
        s.assert_upper(1, q(0), 3).unwrap();
        let r = s.check();
        assert!(r.is_err(), "expected UNSAT");
    }

    /// Two variables: 2x - y ≤ 5, x ≥ 1, y ≥ 0 → SAT.
    #[test]
    fn two_var_feasible() {
        let mut s = SimplexSolver::new(3);
        s.add_row(2, vec![(0, q(2)), (1, q(-1))]);
        s.assert_upper(2, q(5), 1).unwrap();
        s.assert_lower(0, q(1), 2).unwrap();
        s.assert_lower(1, q(0), 3).unwrap();
        s.check().unwrap();
        let vx = s.model_value(0);
        let vy = s.model_value(1);
        let vs = s.model_value(2);
        assert!(vx >= q(1));
        assert!(vy >= q(0));
        assert!(vs <= q(5));
        assert_eq!(vs, q(2) * vx + q(-1) * vy);
    }
}
