//! QF_LIA / QF_LRA solver: CDCL(T) with Dutertre–de Moura Simplex as the
//! theory oracle.
//!
//! # Pipeline
//! 1. Parse the SMT-LIB script via `rm_syntax::Script` (Term-based AST).
//! 2. Map each `(declare-fun x () Int/Real)` to a Simplex variable.
//! 3. Walk each asserted Term, Tseitin-encode Boolean structure, and build
//!    Simplex atoms for arithmetic comparisons.
//! 4. Run the CDCL(T) loop: SAT assigns backbone atoms, theory_check asserts
//!    those bounds into Simplex and calls `simplex.check()`.
//! 5. On conflict, emit a theory lemma (negated conflict core) and continue.
//!
//! # Integer feasibility
//! After Simplex reports SAT over the rationals we verify that every Int-sorted
//! variable has an integer model value. If not, we emit a branch-and-bound
//! disjunction: `x ≤ floor(v) ∨ x ≥ ceil(v)` as a SAT clause, and continue.

use rm_akx::literal::Literal;
use rm_sat::{CdclSolver, SolveResult, TheorySolver};
use rm_syntax::ast::{ArithCmpKind, ArithOpKind, Term, TermInner};
use rm_syntax::{Script, SortExpr};
use rm_theory_arith::{Rational, SimplexSolver};
use std::sync::{Arc, atomic::{AtomicBool, Ordering}};
use rustc_hash::{FxHashMap, FxHashSet};

// ---------------------------------------------------------------------------
// Public result type
// ---------------------------------------------------------------------------

#[derive(Debug, PartialEq, Eq)]
pub enum LiaStatus {
    Sat,
    Unsat,
    Unknown,
}

pub struct LiaResult {
    pub status: LiaStatus,
    /// (variable_name, integer_value) on Sat.
    pub model: Vec<(String, i64)>,
}

// ---------------------------------------------------------------------------
// UF application record (for Ackermann encoding)
// ---------------------------------------------------------------------------

/// One uninterpreted-function application site, used to generate Ackermann
/// congruence constraints between pairs of applications of the same function.
struct UfApp {
    func: String,
    /// Simplex var IDs for each argument (after reducing any linear form to a
    /// single variable; complex forms get a dedicated slack).
    arg_vars: Vec<u32>,
    /// Simplex var ID for the application result.
    result_var: u32,
}

// ---------------------------------------------------------------------------
// Linear form
// ---------------------------------------------------------------------------

/// A linear combination: Σ coeff[v] * v + constant.
#[derive(Default, Clone)]
struct LinearForm {
    coeffs: FxHashMap<u32, i64>, // simplex_var_id → coefficient
    constant: i64,
}

impl LinearForm {
    fn add_scaled(&mut self, other: &LinearForm, scale: i64) {
        for (&var, &c) in &other.coeffs {
            *self.coeffs.entry(var).or_insert(0) += scale * c;
        }
        self.constant += scale * other.constant;
    }

    fn negate(&mut self) {
        for c in self.coeffs.values_mut() {
            *c = -*c;
        }
        self.constant = -self.constant;
    }

    fn is_constant(&self) -> bool {
        self.coeffs.iter().all(|(_, &c)| c == 0)
    }
}

// ---------------------------------------------------------------------------
// Simplex atom
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum SimplexAtom {
    /// atom ↔ simplex_var ≤ bound
    Upper { var: u32, bound: i64 },
    /// atom ↔ simplex_var ≥ bound
    Lower { var: u32, bound: i64 },
}

// ---------------------------------------------------------------------------
// CDCL(T) state for LIA
// ---------------------------------------------------------------------------

struct LiaCdclT {
    next_sat_var: u32,
    simplex: SimplexSolver,
    /// Name → Simplex VarId for user-declared variables.
    var_ids: FxHashMap<String, u32>,
    /// Name → SAT variable for Bool-sorted declared constants.
    bool_var_ids: FxHashMap<String, u32>,
    /// Whether a Simplex var is originally Int-sorted (needs integer check).
    is_int: Vec<bool>,
    /// Next Simplex VarId to allocate (user vars + slacks share the space).
    next_simplex_var: u32,
    /// SAT var → Simplex atom.
    atoms: FxHashMap<u32, SimplexAtom>,
    /// Tseitin clauses buffered before SAT solver creation.
    pending_clauses: Vec<Vec<Literal>>,
    sat: Option<CdclSolver>,
    /// Pre-allocated pool of SAT variables for branch-and-bound cuts.
    /// These are reserved before `finalize()` so the SAT solver's variable
    /// count already covers them; we hand them out on demand during
    /// `theory_check` without needing to grow the solver.
    bb_next: u32,
    bb_end: u32,
    /// All UF application sites, in order of first encounter.
    uf_apps: Vec<UfApp>,
    /// (func_name, [arg_simplex_var_ids]) → result_simplex_var, for deduplication.
    uf_app_cache: FxHashMap<(String, Vec<u32>), u32>,
    /// Canonical form → simplex_var, so the same linear expression always maps
    /// to the same variable when used as a UF argument.
    form_to_var_cache: FxHashMap<(Vec<(u32, i64)>, i64), u32>,
    /// Reverse: simplex_var → canonical form key (populated when form_to_var creates
    /// a new slack).
    var_to_form: FxHashMap<u32, (Vec<(u32, i64)>, i64)>,
    /// Simplex variable permanently fixed to 1, used to represent constant offsets
    /// in linear forms as `k * one_var` so the Simplex row stays exact.
    one_var: u32,
    /// Current Simplex decision level, synced with the SAT solver's level in
    /// theory_propagate via new_decision_level() calls.
    simplex_level: u32,
    /// Snapshot of the Simplex after encoding (rows only, no bounds).
    /// Used by theory_final_check to get a clean scratch for the rational check.
    initial_simplex: Option<SimplexSolver>,
    /// Model values saved from the last complete-model Simplex scratch in TFC.
    /// Keyed by Simplex variable ID; populated when TFC finds a SAT model so
    /// that model extraction uses the correct complete-model assignment rather
    /// than the incremental Simplex (which has stale/partial bounds after B&B).
    last_sat_model_values: FxHashMap<u32, i64>,
    /// Cancellation flag; set by the benchmark harness when the timeout fires.
    cancel: Arc<AtomicBool>,
    /// Cache for Ackermann var-equality literals: (min(a,b), max(a,b)) → literal.
    /// Prevents encode_var_eq from creating duplicate Simplex rows and SAT vars
    /// for the same pair (e.g. 270 calls → 17 unique pairs for Hash benchmarks).
    eq_cache: FxHashMap<(u32, u32), Literal>,
    /// Cache for arithmetic comparison atoms: (simplex_var, is_upper, bound) → SAT var.
    /// Prevents encode_arith_cmp from creating duplicate SAT atoms when the same
    /// comparison appears multiple times (e.g. via let-expansion).
    arith_atom_cache: FxHashMap<(u32, bool, i64), u32>,
    /// (le_sat, ge_sat) component SAT vars for each encode_var_eq pair.
    /// Populated alongside eq_cache so we can retrieve the component atoms
    /// without re-creating them (e.g. for Ackermann T-propagation bookkeeping).
    eq_detail_cache: FxHashMap<(u32, u32), (u32, u32)>,
    /// SAT vars that are the le/ge component atoms of Ackermann arg-equality
    /// encodings. These atoms represent `diff_slack ≤ 0` and `diff_slack ≥ 0`
    /// for arg diffs of UF pairs, where integer tightening (¬(x≤k) → x≥k+1)
    /// is unsound: it creates permanent Simplex bounds that block the solver
    /// from exploring branches where two UF args are equal.
    ackermann_le_ge_atoms: FxHashSet<u32>,
    /// (arg_i_var, arg_j_var, le_sat, ge_sat) tuples for Ackermann arg pairs.
    /// Used in theory_propagate to emit T-propagation lemmas when tight Simplex
    /// bounds prove an arg diff is zero (forcing the le/ge atoms TRUE by theory).
    ackermann_arg_tprop: Vec<(u32, u32, u32, u32)>,
    /// Full Ackermann pair data for lazy clause generation in TFC.
    /// Tuple: (arg_eq_lits, result_eq_lit, result_i, result_j).
    /// Ackermann clauses (¬eq_0 ∨ … ∨ res_eq) are NOT added upfront — for
    /// problems with many UF applications they would flood the SAT database
    /// with O(n²) clauses and degrade BCP.  TFC checks model values instead
    /// and returns a violated clause on demand.
    ackermann_full_pairs: Vec<(Vec<Literal>, Literal, u32, u32)>,
    /// Maps arg-equality SAT var → indices into ackermann_full_pairs.
    /// Used in theory_propagate to efficiently find pairs whose congruence
    /// precondition just became fully satisfied in the trail.
    ackermann_cong_watcher: FxHashMap<u32, Vec<usize>>,
}

impl LiaCdclT {
    fn new(max_simplex_vars: u32, cancel: Arc<AtomicBool>) -> Self {
        LiaCdclT {
            next_sat_var: 1,
            simplex: SimplexSolver::new(max_simplex_vars),
            var_ids: FxHashMap::default(),
            bool_var_ids: FxHashMap::default(),
            is_int: vec![true; max_simplex_vars as usize],
            next_simplex_var: 0,
            atoms: FxHashMap::default(),
            pending_clauses: Vec::new(),
            sat: None,
            bb_next: 0,
            bb_end: 0,
            uf_apps: Vec::new(),
            uf_app_cache: FxHashMap::default(),
            form_to_var_cache: FxHashMap::default(),
            var_to_form: FxHashMap::default(),
            one_var: 0,
            simplex_level: 0,
            initial_simplex: None,
            last_sat_model_values: FxHashMap::default(),
            cancel,
            eq_cache: FxHashMap::default(),
            arith_atom_cache: FxHashMap::default(),
            eq_detail_cache: FxHashMap::default(),
            ackermann_le_ge_atoms: FxHashSet::default(),
            ackermann_arg_tprop: Vec::new(),
            ackermann_full_pairs: Vec::new(),
            ackermann_cong_watcher: FxHashMap::default(),
        }
    }

    fn alloc_sat(&mut self) -> u32 {
        let v = self.next_sat_var;
        self.next_sat_var += 1;
        v
    }

    fn alloc_simplex(&mut self) -> u32 {
        let v = self.next_simplex_var;
        self.next_simplex_var += 1;
        // Grow Simplex capacity and is_int if needed.
        if self.next_simplex_var as usize > self.simplex.num_vars() as usize {
            self.simplex.grow_to(self.next_simplex_var + 64);
        }
        while self.is_int.len() < self.next_simplex_var as usize {
            self.is_int.push(true);
        }
        v
    }

    fn add_clause(&mut self, lits: &[Literal]) {
        self.pending_clauses.push(lits.to_vec());
    }

    /// Reserve the B&B variable pool and create the SAT solver.
    /// `bb_budget`: number of SAT variable slots to pre-allocate for branch-and-bound.
    fn finalize_with_bb(&mut self, bb_budget: u32) {
        self.bb_next = self.next_sat_var;
        self.next_sat_var += bb_budget;
        self.bb_end = self.next_sat_var;

        let num_vars = self.next_sat_var - 1;
        // Debug: simulate BCP to find propositional contradiction
        if std::env::var("RM_DEBUG_TFC").is_ok() {
            // value: None=unset, Some(true)=forced TRUE, Some(false)=forced FALSE
            let mut vals: Vec<Option<bool>> = vec![None; (num_vars + 1) as usize];
            let mut queue: std::collections::VecDeque<(u32, bool)> = std::collections::VecDeque::new();
            // Seed with unit clauses
            for clause in &self.pending_clauses {
                if clause.len() == 1 {
                    let lit = clause[0];
                    queue.push_back((lit.var(), lit.is_positive()));
                }
            }
            // Propagate
            let mut contradiction: Option<(u32, bool, bool)> = None;
            while let Some((var, val)) = queue.pop_front() {
                if var as usize >= vals.len() { continue; }
                if let Some(existing) = vals[var as usize] {
                    if existing != val {
                        contradiction = Some((var, existing, val));
                        break;
                    }
                    continue;
                }
                vals[var as usize] = Some(val);
                // Propagate through all clauses where this lit is FALSE → unit
                for clause in &self.pending_clauses {
                    // Check if our assignment makes this clause unit
                    let mut unset_count = 0u32;
                    let mut last_unset: Option<Literal> = None;
                    let mut satisfied = false;
                    for &lit in clause {
                        if lit.var() as usize >= vals.len() { unset_count += 1; last_unset = Some(lit); continue; }
                        match vals[lit.var() as usize] {
                            None => { unset_count += 1; last_unset = Some(lit); }
                            Some(v) if v == lit.is_positive() => { satisfied = true; break; }
                            _ => {} // this lit is FALSE
                        }
                    }
                    if !satisfied && unset_count == 1 {
                        if let Some(unit_lit) = last_unset {
                            queue.push_back((unit_lit.var(), unit_lit.is_positive()));
                        }
                    } else if !satisfied && unset_count == 0 {
                        log::trace!("[BCP] all-false clause: {:?}", clause);
                    }
                }
            }
            let assigned_count = vals.iter().filter(|v| v.is_some()).count();
            if let Some((var, v1, v2)) = contradiction {
                log::trace!("[BCP] contradiction at var={}: forced both {} and {}", var, v1, v2);
                if let Some(atom) = self.atoms.get(&var) {
                    log::trace!("  simplex atom for var {}: {:?}", var, atom);
                }
            } else {
                log::trace!("[BCP] no contradiction found; assigned {}/{} vars", assigned_count, num_vars);
            }
            log::trace!("[BCP] pending_clauses={} vars={}", self.pending_clauses.len(), num_vars);
            // RM_DUMP_DIMACS=/tmp/out.cnf dumps the initial clause set to a file
            // (unconditional: fires even if BCP found a contradiction)
            if let Ok(path) = std::env::var("RM_DUMP_DIMACS") {
                let mut out = String::new();
                out.push_str(&format!("p cnf {} {}\n", num_vars, self.pending_clauses.len()));
                for clause in &self.pending_clauses {
                    for lit in clause {
                        if lit.is_positive() {
                            out.push_str(&format!("{} ", lit.var()));
                        } else {
                            out.push_str(&format!("-{} ", lit.var()));
                        }
                    }
                    out.push_str("0\n");
                }
                if let Err(e) = std::fs::write(&path, &out) {
                    log::warn!("RM_DUMP_DIMACS: could not write to {path}: {e}");
                } else {
                    log::trace!("RM_DUMP_DIMACS: wrote {} to {path}", out.len());
                }
            }
        }
        let mut sat = CdclSolver::new(num_vars);
        sat.skip_bve();
        for clause in self.pending_clauses.drain(..) {
            sat.add_clause(&clause);
        }
        self.sat = Some(sat);
    }

    /// Take the next variable from the pre-allocated B&B pool.
    /// Returns None if the budget is exhausted (caller should treat as SAT).
    fn alloc_bb_var(&mut self) -> Option<u32> {
        if self.bb_next < self.bb_end {
            let v = self.bb_next;
            self.bb_next += 1;
            Some(v)
        } else {
            None
        }
    }

    fn solve(&mut self) -> LiaStatus {
        // Reserve 64 B&B cut variables per Int-sorted variable (user + UF results).
        // Count only actual user-declared Int vars, not the entire pre-allocated is_int
        // array (which is all-true and much larger than the real variable count).
        let int_count = self.var_ids.values()
            .filter(|&&id| (id as usize) < self.is_int.len() && self.is_int[id as usize])
            .count() as u32;
        let uf_count = self.uf_apps.len() as u32;
        let bb_budget = (int_count + uf_count + 1) * 64;
        log::debug!("LIA finalize: int_count={int_count} uf_count={uf_count} bb_budget={bb_budget} ackermann_tprop_pairs={}", self.ackermann_arg_tprop.len());
        self.finalize_with_bb(bb_budget);
        // Take the SAT solver out of self so we can pass `self` as the theory.
        let mut sat = match self.sat.take() {
            Some(s) => s,
            None => return LiaStatus::Unknown,
        };
        let result = sat.solve_with_theory(u64::MAX, self);
        self.sat = Some(sat);
        // If cancelled, return Unknown even if solve_with_theory thinks it's Sat.
        if self.cancel.load(Ordering::Relaxed) {
            return LiaStatus::Unknown;
        }
        match result {
            SolveResult::Sat(_) => LiaStatus::Sat,
            SolveResult::Unsat => LiaStatus::Unsat,
            SolveResult::BudgetExceeded | SolveResult::Unknown => LiaStatus::Unknown,
        }
    }
}

// ---------------------------------------------------------------------------
// TheorySolver implementation — incremental Simplex integration
// ---------------------------------------------------------------------------

impl TheorySolver for LiaCdclT {
    fn theory_propagate(
        &mut self,
        level: u32,
        trail: &[Literal],
        prev_trail_len: usize,
    ) -> Result<Vec<Vec<Literal>>, Vec<Literal>> {
        if self.cancel.load(Ordering::Relaxed) {
            return Ok(Vec::new());
        }
        // Sync Simplex decision level with the SAT level.
        while self.simplex_level < level {
            self.simplex.new_decision_level();
            self.simplex_level += 1;
        }
        // Assert newly assigned theory atoms into the incremental Simplex.
        // For TRUE atoms: assert the bound directly.
        // For FALSE atoms: apply integer tightening (¬(x≤k) → x≥k+1) UNLESS the
        // atom is an Ackermann or ITE arg-equality component (tracked in
        // ackermann_le_ge_atoms).  For those paired le/ge atoms, both can be FALSE
        // simultaneously before the Tseitin AND gate resolves, causing tightening to
        // assert contradictory persistent bounds (diff≥1 AND diff≤-1) and block
        // valid models.  Plain arithmetic comparison atoms (e.g. ¬(4*f3 ≤ 1)) have
        // no such pairing issue and must be tightened for integer completeness.
        for &lit in &trail[prev_trail_len..] {
            let var = lit.var();
            let val = lit.is_positive();
            let sat_raw = lit.raw();
            let atom = match self.atoms.get(&var) {
                Some(a) => a.clone(),
                None => continue,
            };
            let res = if val {
                // TRUE atom: assert bound directly.
                match atom {
                    SimplexAtom::Upper { var, bound } => {
                        self.simplex.assert_upper(var, Rational::from_int(bound), sat_raw)
                    }
                    SimplexAtom::Lower { var, bound } => {
                        self.simplex.assert_lower(var, Rational::from_int(bound), sat_raw)
                    }
                }
            } else if self.ackermann_le_ge_atoms.contains(&var) {
                // FALSE Ackermann/ITE equality atom: skip tightening (unsafe).
                continue;
            } else {
                // FALSE plain arithmetic atom: apply integer tightening.
                let neg_raw = Literal::negative(var).raw();
                match atom {
                    SimplexAtom::Upper { var, bound } => {
                        // ¬(slack ≤ bound) → slack ≥ bound+1
                        self.simplex.assert_lower(var, Rational::from_int(bound + 1), neg_raw)
                    }
                    SimplexAtom::Lower { var, bound } => {
                        // ¬(slack ≥ bound) → slack ≤ bound-1
                        self.simplex.assert_upper(var, Rational::from_int(bound - 1), neg_raw)
                    }
                }
            };
            if let Err(e) = res {
                return Err(mk_conflict_simplex(&e.lits));
            }
        }
        // Run Simplex to detect infeasibility from the newly asserted bounds.
        match self.simplex.check() {
            Err(e) => return Err(mk_conflict_simplex(&e.lits)),
            Ok(_) => {}
        }
        // T-propagation: when Simplex bounds prove an Ackermann arg diff is zero
        // (ub(arg_i) ≤ lb(arg_j) AND lb(arg_i) ≥ ub(arg_j)), force the le and ge
        // atoms TRUE by emitting theory lemmas. This chains through the Tseitin
        // AND and Ackermann clause to force result equality, enabling the SAT solver
        // to detect congruence conflicts without exhaustive propositional search.
        //
        // Guard: only emit for a pair if the target atom is NOT yet TRUE in the
        // current trail. Without this guard, T-propagation can infinite-loop when
        // the lemma's head is already TRUE (satisfied clause → no BCP progress →
        // theory_propagate called again → same lemma emitted → repeat).
        let mut tprop: Vec<Vec<Literal>> = Vec::new();
        // Build a one-shot TRUE-var set over the current trail for dedup checks.
        let trail_true: FxHashSet<u32> = trail.iter()
            .filter(|l| l.is_positive())
            .map(|l| l.var())
            .collect();
        for &(arg_i, arg_j, le_sat, ge_sat) in &self.ackermann_arg_tprop {
            // le_sat represents: arg_i - arg_j ≤ 0, i.e. arg_i ≤ arg_j.
            // Proved when ub(arg_i) ≤ lb(arg_j) (both are tight numeric bounds).
            let diff_le_zero = if trail_true.contains(&le_sat) {
                None // already TRUE in trail — lemma would be satisfied, skip
            } else {
                match (
                    self.simplex.upper_bound(arg_i),
                    self.simplex.lower_bound(arg_j),
                ) {
                    (Some((ub_i, ub_i_raw)), Some((lb_j, lb_j_raw))) if ub_i <= lb_j => {
                        Some((ub_i_raw, lb_j_raw))
                    }
                    _ => None,
                }
            };
            // ge_sat represents: arg_i - arg_j ≥ 0, i.e. arg_i ≥ arg_j.
            // Proved when lb(arg_i) ≥ ub(arg_j).
            let diff_ge_zero = if trail_true.contains(&ge_sat) {
                None // already TRUE in trail — lemma would be satisfied, skip
            } else {
                match (
                    self.simplex.lower_bound(arg_i),
                    self.simplex.upper_bound(arg_j),
                ) {
                    (Some((lb_i, lb_i_raw)), Some((ub_j, ub_j_raw))) if lb_i >= ub_j => {
                        Some((lb_i_raw, ub_j_raw))
                    }
                    _ => None,
                }
            };
            if let Some((ub_i_raw, lb_j_raw)) = diff_le_zero {
                // Lemma: [+le_sat, ¬ub_i_reason, ¬lb_j_reason]
                // Meaning: "if ub(arg_i) and lb(arg_j) witnesses hold, le must be TRUE".
                let mut le_lemma = vec![Literal::positive(le_sat)];
                if ub_i_raw != 0 {
                    le_lemma.push(Literal::from_raw(ub_i_raw).negate());
                }
                if lb_j_raw != 0 && lb_j_raw != ub_i_raw {
                    le_lemma.push(Literal::from_raw(lb_j_raw).negate());
                }
                tprop.push(le_lemma);
            }
            if let Some((lb_i_raw, ub_j_raw)) = diff_ge_zero {
                // Lemma: [+ge_sat, ¬lb_i_reason, ¬ub_j_reason]
                let mut ge_lemma = vec![Literal::positive(ge_sat)];
                if lb_i_raw != 0 {
                    ge_lemma.push(Literal::from_raw(lb_i_raw).negate());
                }
                if ub_j_raw != 0 && ub_j_raw != lb_i_raw {
                    ge_lemma.push(Literal::from_raw(ub_j_raw).negate());
                }
                tprop.push(ge_lemma);
            }
        }
        // Incremental congruence probe (S26): after check() the incremental Simplex
        // has a feasible model.  For pairs whose model values are equal but whose
        // le/ge atoms are not yet TRUE, probe whether asserting inequality is
        // infeasible.  This fires mid-search (not just at TFC), catching equalities
        // that arise through row equations rather than direct bounds.
        //
        // Limit: probe at most 30 pairs per call to bound overhead from Simplex clones.
        // Only run when the newly assigned trail segment is non-empty (at least one
        // new atom could have changed model values).
        if !trail[prev_trail_len..].is_empty() {
            let mut probed: usize = 0;
            for &(arg_i, arg_j, le_sat, ge_sat) in &self.ackermann_arg_tprop {
                if probed >= 30 {
                    break;
                }
                if le_sat == 0 || ge_sat == 0 {
                    continue;
                }
                let le_true = trail_true.contains(&le_sat);
                let ge_true = trail_true.contains(&ge_sat);
                if le_true && ge_true {
                    continue;
                }
                // Skip pairs with no decided arithmetic atoms: when neither le_sat nor
                // ge_sat is TRUE the LP is fully unconstrained so model values all sit
                // at the Simplex default (0), making model_value(arg_i)==model_value(arg_j)
                // trivially true for every pair — probing here is pure overhead with no
                // benefit.  Only probe once at least one bound has been committed.
                if !le_true && !ge_true {
                    continue;
                }
                let vi = self.simplex.model_value(arg_i);
                let vj = self.simplex.model_value(arg_j);
                if vi != vj {
                    continue;
                }
                // Retrieve the diff slack from the le_sat atom (Upper {var, bound=0}).
                let slack = match self.atoms.get(&le_sat) {
                    Some(SimplexAtom::Upper { var, .. }) => *var,
                    _ => continue,
                };
                probed += 1;
                if !le_true {
                    let mut probe = self.simplex.clone();
                    let neg_raw = Literal::negative(le_sat).raw();
                    let conflict = probe
                        .assert_lower(slack, Rational::from_int(1), neg_raw)
                        .err()
                        .map(|e| mk_conflict_simplex(&e.lits))
                        .or_else(|| probe.check().err().map(|e| mk_conflict_simplex(&e.lits)));
                    if let Some(c) = conflict {
                        tprop.push(c);
                    }
                }
                if !ge_true {
                    let mut probe = self.simplex.clone();
                    let neg_raw = Literal::negative(ge_sat).raw();
                    let conflict = probe
                        .assert_upper(slack, Rational::from_int(-1), neg_raw)
                        .err()
                        .map(|e| mk_conflict_simplex(&e.lits))
                        .or_else(|| probe.check().err().map(|e| mk_conflict_simplex(&e.lits)));
                    if let Some(c) = conflict {
                        tprop.push(c);
                    }
                }
            }
        }
        // Congruence T-propagation: when all arg-equality literals of an Ackermann
        // pair become TRUE in the trail, immediately propagate the result equality.
        // Uses ackermann_cong_watcher to avoid an O(n²) scan — only pairs
        // touched by newly assigned literals are checked.
        //
        // If result equality is unassigned → push unit lemma (T-prop).
        // If result equality is already FALSE in trail → return conflict.
        let trail_false: FxHashSet<u32> = trail.iter()
            .filter(|l| !l.is_positive())
            .map(|l| l.var())
            .collect();
        let mut checked: FxHashSet<usize> = FxHashSet::default();
        for &lit in &trail[prev_trail_len..] {
            if !lit.is_positive() {
                continue;
            }
            let Some(pair_indices) = self.ackermann_cong_watcher.get(&lit.var()) else {
                continue;
            };
            for &idx in pair_indices {
                if !checked.insert(idx) {
                    continue;
                }
                let (arg_eq_lits, res_eq_lit, _, _) = &self.ackermann_full_pairs[idx];
                if !arg_eq_lits.iter().all(|l| trail_true.contains(&l.var())) {
                    continue;
                }
                if trail_true.contains(&res_eq_lit.var()) {
                    continue; // already satisfied
                }
                // Build the Ackermann clause: ¬arg_eq_0 ∨ … ∨ res_eq
                let mut clause: Vec<Literal> = arg_eq_lits.iter().map(|l| l.negate()).collect();
                clause.push(*res_eq_lit);
                if trail_false.contains(&res_eq_lit.var()) {
                    // All literals in clause are FALSE → conflict.
                    return Err(clause);
                }
                // Result is unassigned — propagate it TRUE.
                tprop.push(clause);
            }
        }
        Ok(tprop)
    }

    fn theory_backtrack(&mut self, target_level: u32) {
        self.simplex.backtrack_to(target_level);
        self.simplex_level = target_level;
    }

    fn theory_final_check_preserves_state(&self) -> bool {
        // TFC uses a fresh Simplex clone; self.simplex is never touched, so
        // the incremental bounds at the UIP level remain valid after TFC.
        true
    }

    fn theory_final_check(&mut self, model: &rm_sat::Model) -> Option<Vec<Literal>> {
        // Full rational feasibility check on a fresh Simplex clone.
        //
        // theory_propagate is incremental and can miss infeasibilities when atoms
        // weren't re-asserted after backjumps (e.g., the final decision made by
        // branch_or_finish is never seen by theory_propagate). We check the complete
        // model by cloning the post-encoding Simplex (rows only, no bounds) and
        // asserting all TRUE atoms fresh — no stale incremental bounds.
        //
        // Only TRUE atoms are asserted here (FALSE atoms are skipped). Integer tightening
        // of FALSE atoms (¬(x ≤ k) → x ≥ k+1) in a rational Simplex produces unsound
        // conflict clauses when rational-valued slacks (e.g. diff_slack = ri − rj) have
        // a satisfying rational value in (k, k+1). theory_propagate handles negated atoms
        // incrementally with proper backtracking; TFC only needs the positive bounds to
        // detect genuine rational infeasibilities in the complete model.
        let mut scratch = self.initial_simplex.as_ref().unwrap().clone();
        let atoms_snapshot: Vec<(u32, SimplexAtom)> = self
            .atoms
            .iter()
            .filter(|(&sv, _)| sv <= model.num_vars())
            .map(|(&sv, atom)| (sv, atom.clone()))
            .collect();

        let rat_conflict: Option<Vec<Literal>> = 'rat: {
            for (sat_var, atom) in &atoms_snapshot {
                let val = model.value_of(*sat_var);
                if !val {
                    continue;
                }
                let sat_raw = Literal::positive(*sat_var).raw();
                let res = match *atom {
                    SimplexAtom::Upper { var, bound } => {
                        scratch.assert_upper(var, Rational::from_int(bound), sat_raw)
                    }
                    SimplexAtom::Lower { var, bound } => {
                        scratch.assert_lower(var, Rational::from_int(bound), sat_raw)
                    }
                };
                if let Err(e) = res {
                    break 'rat Some(mk_conflict_simplex(&e.lits));
                }
            }
            match scratch.check() {
                Ok(_) => None,
                Err(e) => Some(mk_conflict_simplex(&e.lits)),
            }
        };

        if let Some(conflict) = rat_conflict {
            return Some(conflict);
        }

        // Congruence check: after the rational Simplex says SAT, verify that for
        // every Ackermann arg pair the SAT model's equality atoms agree with what
        // the Simplex model actually assigns.
        //
        // This catches cases where the arg equality is derivable purely from
        // Simplex row equations (e.g. slack_xp1 = x+1 and y-x = 1 → x+1 = y)
        // with no explicit bound on the diff slack, so the arith_atom_cache fix in
        // encode_var_eq doesn't help.  We probe: if the SAT model has le_sat=false
        // but Simplex model_value says args are equal, asserting Lower(diff,1)
        // (the negation of Upper(diff,0)) must conflict with the existing rows —
        // we collect that conflict core as a theory lemma and return it.
        // S23 (TFC congruence probe) is disabled.
        //
        // The probe fires when scratch.model_value(arg_i) == scratch.model_value(arg_j)
        // but the SAT model has le_sat=FALSE, and probes if Lower(diff,1) is infeasible.
        // In practice, the equality in the scratch almost always arises because two
        // variables happen to have the same value due to B&B decisions (e.g. both pinned
        // to 0 or 1), not because of a genuine arithmetic row identity.  The resulting
        // conflict clauses reference B&B atoms and force Ackermann congruences in branches
        // where the args are NOT actually equal, eventually causing false UNSAT on SAT
        // instances (observed: hash_sat_06_03, hash_sat_03_05).
        //
        // Genuine congruences where arg equality is derivable from explicit arithmetic
        // assertions are handled by S24 (lazy Ackermann): the arith_atom_cache ensures
        // that problem assertions and Ackermann arg-equality encodings share the same
        // le_sat/ge_sat atoms, so BCP forces z_arg=TRUE and S24 fires.
        //
        // Re-enable S23 only if a case is found where S24 cannot detect the violation
        // and the probe can be restricted to purely structural (row-equation) infeasibility
        // that contains no B&B or contingent bound atoms.

        // Lazy Ackermann: check all deferred Ackermann pairs against the SAT model.
        // Ackermann clauses (¬eq_0 ∨ … ∨ res_eq) were not added upfront to avoid
        // flooding the SAT database with O(n²) clauses.  For each pair, if all arg
        // equality literals are TRUE and the result equality literal is FALSE in
        // the current complete SAT model, congruence is violated — return the
        // Ackermann clause as a conflict so CDCL learns it and backtracks.
        for (arg_eq_lits, res_eq_lit, _ri, _rj) in &self.ackermann_full_pairs {
            // Skip if any arg equality is FALSE (args are different in SAT model —
            // the implication is vacuously satisfied, no congruence violation).
            let all_args_true = arg_eq_lits.iter().all(|&lit| {
                model.value_of(lit.var()) == lit.is_positive()
            });
            if !all_args_true {
                continue;
            }
            // If result equality is FALSE → congruence violated.
            let res_false = model.value_of(res_eq_lit.var()) != res_eq_lit.is_positive();
            if res_false {
                let mut clause: Vec<Literal> = arg_eq_lits.iter().map(|l| l.negate()).collect();
                clause.push(*res_eq_lit);
                return Some(clause);
            }
        }

        // Integer feasibility: if any Int-sorted variable has a fractional value,
        // emit a branch-and-bound disjunction x ≤ floor(v) ∨ x ≥ ceil(v).
        // Use `scratch` (complete-model assignment) not `self.simplex` (incremental).
        let mut frac_var: Option<u32> = None;
        'outer: for (_, &simplex_var) in &self.var_ids {
            if simplex_var as usize >= self.is_int.len() || !self.is_int[simplex_var as usize] {
                continue;
            }
            if !scratch.model_value(simplex_var).is_integer() {
                frac_var = Some(simplex_var);
                break 'outer;
            }
        }
        if frac_var.is_none() {
            for app in &self.uf_apps {
                if !scratch.model_value(app.result_var).is_integer() {
                    frac_var = Some(app.result_var);
                    break;
                }
            }
        }
        if let Some(simplex_var) = frac_var {
            let v = scratch.model_value(simplex_var);
            let floor_v = v.floor_int();
            let ceil_v = v.ceil_int();
            let (sv, sv2) = match (self.alloc_bb_var(), self.alloc_bb_var()) {
                (Some(a), Some(b)) => (a, b),
                _ => {
                    // Pre-allocated B&B variable pool exhausted. Returning None here
                    // would be misinterpreted as SAT — unsound. Signal Unknown instead
                    // by setting the cancel flag; the solve() caller checks it and
                    // returns Unknown before returning Sat.
                    log::debug!("LIA B&B pool exhausted (bb_next={} bb_end={}); returning Unknown", self.bb_next, self.bb_end);
                    self.cancel.store(true, std::sync::atomic::Ordering::Relaxed);
                    return None;
                }
            };
            self.atoms.insert(sv, SimplexAtom::Upper { var: simplex_var, bound: floor_v });
            self.atoms.insert(sv2, SimplexAtom::Lower { var: simplex_var, bound: ceil_v });
            Some(vec![Literal::positive(sv), Literal::positive(sv2)])
        } else {
            // All integer variables have integer model values — genuine SAT.
            // Save the complete-model values from the scratch Simplex so that
            // model extraction uses the correct full-model assignment rather than
            // the incremental Simplex (which may have stale bounds after B&B jumps).
            self.last_sat_model_values.clear();
            for (_name, &id) in &self.var_ids {
                let val = scratch.model_value(id);
                self.last_sat_model_values.insert(id, val.floor_int());
            }
            None
        }
    }
}

fn mk_conflict_simplex(lits: &[u32]) -> Vec<Literal> {
    lits.iter()
        .map(|&raw| Literal::from_raw(raw).negate())
        .collect()
}

/// Encode "simplex_var_a = simplex_var_b" as a SAT literal using two Simplex
/// bound atoms: `a ≤ b` and `a ≥ b`, Tseitin-combined into one AND variable.
///
/// Returns `(eq_lit, le_sat, ge_sat)`. For the trivial `a == b` case,
/// `le_sat` and `ge_sat` are both 0 (sentinel meaning "always true").
fn encode_var_eq(a: u32, b: u32, solver: &mut LiaCdclT) -> (Literal, u32, u32) {
    // Handle the trivial case (a == b means always true).
    if a == b {
        let v = solver.alloc_sat();
        solver.add_clause(&[Literal::positive(v)]);
        return (Literal::positive(v), 0, 0);
    }
    // Cache check: same pair (order-normalised) reuses existing literal.
    let key = (a.min(b), a.max(b));
    if let Some(&lit) = solver.eq_cache.get(&key) {
        let (le, ge) = solver.eq_detail_cache[&key];
        return (lit, le, ge);
    }

    // Expand a and b through var_to_form to get user-variable-level linear forms.
    // This ensures the diff form matches what encode_arith_cmp creates for problem
    // assertions on the same relationship.
    //
    // encode_arith_cmp always normalises to zero constant in the form (moving the
    // constant to rhs_const).  For example `(assert (= y (+ x 1)))` creates form
    // {y:1, x:-1} (constant=0) with bound=1 (i.e. y-x ≤ 1 and y-x ≥ 1).
    //
    // So when encoding the Ackermann equality between xp1_slack (row: x+1) and y_var:
    //   a_form = {x:1, const:1},  b_form = {y:1}
    //   diff_vars = a_form - b_form variable parts = {x:1, y:-1} (constant extracted: C=1)
    //   rev_vars  = b_form - a_form variable parts = {x:-1, y:1} (constant: -C=-1)
    //   The equality is: rev_vars_slack = C  =>  arith_atom_cache[(rev_slack, true/false, C)]
    // which is exactly the assertion's arith_atom_cache[(slack_yx, true, 1)] and [(slack_yx, false, 1)].
    let a_form = var_to_linear_form(a, solver);
    let b_form = var_to_linear_form(b, solver);
    // diff = a_form - b_form (including constant).
    let mut diff_full = a_form.clone();
    diff_full.add_scaled(&b_form, -1);
    // Separate variable part from constant: equality is diff_vars_slack = -C.
    let big_c = diff_full.constant;
    diff_full.constant = 0; // diff_vars_form (no constant)

    // rev_vars = -(diff_vars) = b_vars - a_vars.  rev_vars_slack = C means a = b.
    let mut rev_vars = diff_full.clone();
    rev_vars.negate();

    // Build cache key for rev_vars (constant=0, matching encode_arith_cmp normalisation).
    let mut rev_key_pairs: Vec<(u32, i64)> = rev_vars.coeffs.iter()
        .filter(|(_, &c)| c != 0)
        .map(|(&v, &c)| (v, c))
        .collect();
    rev_key_pairs.sort_unstable();
    let rev_cache_key = (rev_key_pairs, 0i64);

    // Build cache key for diff_vars (a - b, constant=0).
    let mut diff_key_pairs: Vec<(u32, i64)> = diff_full.coeffs.iter()
        .filter(|(_, &c)| c != 0)
        .map(|(&v, &c)| (v, c))
        .collect();
    diff_key_pairs.sort_unstable();
    let diff_cache_key = (diff_key_pairs, 0i64);

    // Choose the slack direction.
    // Prefer rev if rev_slack already exists: its atoms (rev_slack, ?, C) may
    // already be in arith_atom_cache (from the problem assertion), letting BCP
    // force z_arg=TRUE when the assertion's unit clause is propagated.
    // Otherwise fall back to diff direction (with bound=-C), creating if needed.
    let (slack, le_bound, ge_bound, le_is_upper, ge_is_upper) =
        if let Some(&slack_rev) = solver.form_to_var_cache.get(&rev_cache_key) {
            // rev_slack = b - a (expanded).  rev_slack = C means a = b.
            //   le_sat = "a ≤ b" = "rev_slack ≥ C" = Lower(rev_slack, C)
            //   ge_sat = "a ≥ b" = "rev_slack ≤ C" = Upper(rev_slack, C)
            (slack_rev, big_c, big_c, false, true)
        } else {
            let slack_diff = if let Some(&s) = solver.form_to_var_cache.get(&diff_cache_key) {
                s
            } else {
                form_to_var(diff_full, solver)
            };
            // diff_slack = a - b (expanded).  diff_slack = -C means a = b.
            //   le_sat = "a ≤ b" = "diff_slack ≤ -C" = Upper(diff_slack, -C)
            //   ge_sat = "a ≥ b" = "diff_slack ≥ -C" = Lower(diff_slack, -C)
            (slack_diff, -big_c, -big_c, true, false)
        };

    let le_sat = if let Some(&v) = solver.arith_atom_cache.get(&(slack, le_is_upper, le_bound)) {
        v
    } else {
        let v = solver.alloc_sat();
        let atom = if le_is_upper {
            SimplexAtom::Upper { var: slack, bound: le_bound }
        } else {
            SimplexAtom::Lower { var: slack, bound: le_bound }
        };
        solver.atoms.insert(v, atom);
        solver.arith_atom_cache.insert((slack, le_is_upper, le_bound), v);
        v
    };
    let ge_sat = if let Some(&v) = solver.arith_atom_cache.get(&(slack, ge_is_upper, ge_bound)) {
        v
    } else {
        let v = solver.alloc_sat();
        let atom = if ge_is_upper {
            SimplexAtom::Upper { var: slack, bound: ge_bound }
        } else {
            SimplexAtom::Lower { var: slack, bound: ge_bound }
        };
        solver.atoms.insert(v, atom);
        solver.arith_atom_cache.insert((slack, ge_is_upper, ge_bound), v);
        v
    };

    // Tseitin AND: z ↔ (le ∧ ge)
    let v = solver.alloc_sat();
    let z = Literal::positive(v);
    let le = Literal::positive(le_sat);
    let ge = Literal::positive(ge_sat);
    solver.add_clause(&[z.negate(), le]);
    solver.add_clause(&[z.negate(), ge]);
    solver.add_clause(&[z, le.negate(), ge.negate()]);
    solver.eq_detail_cache.insert(key, (le_sat, ge_sat));
    solver.eq_cache.insert(key, z);
    (z, le_sat, ge_sat)
}

/// Return the canonical linear form for a Simplex variable.
/// For vars created by form_to_var (non-user slacks), returns the stored form.
/// For user variables (not in var_to_form), returns the unit form {var: 1}.
/// This single-level expansion is sufficient for UF arguments, which are either
/// user variables or first-level slacks (e.g. x+1 encoded as xp1_slack).
fn var_to_linear_form(var: u32, solver: &LiaCdclT) -> LinearForm {
    if let Some((key_pairs, constant)) = solver.var_to_form.get(&var) {
        let mut f = LinearForm::default();
        f.constant = *constant;
        for &(v, c) in key_pairs {
            *f.coeffs.entry(v).or_insert(0) += c;
        }
        f
    } else {
        let mut f = LinearForm::default();
        f.coeffs.insert(var, 1);
        f
    }
}

/// Add Ackermann congruence constraints for all pairs of UF applications with
/// the same function symbol.  For each such pair (i, j):
///   (∀k: arg_i[k] = arg_j[k]) → result_i = result_j
/// encoded as a SAT clause.
fn args_provably_differ(a: u32, b: u32, solver: &LiaCdclT) -> bool {
    if a == b { return false; }
    let Some(key_a) = solver.var_to_form.get(&a) else { return false };
    let Some(key_b) = solver.var_to_form.get(&b) else { return false };
    // Only skip pure-constant pairs (e.g. literal `5` vs literal `7` as UF args).
    // Symbolic slacks (non-empty var parts) are never skipped to avoid soundness issues
    // when the equality atom for the pair is needed elsewhere in the proof.
    if !key_a.0.is_empty() || !key_b.0.is_empty() { return false; }
    key_a.1 != key_b.1
}

fn add_ackermann_constraints(solver: &mut LiaCdclT) {
    // Collect pairs first to avoid borrow conflict on solver.uf_apps during encoding.
    let n = solver.uf_apps.len();
    let mut pairs: Vec<(String, Vec<u32>, Vec<u32>, u32, u32)> = Vec::new();
    for i in 0..n {
        for j in (i + 1)..n {
            if solver.uf_apps[i].func != solver.uf_apps[j].func {
                continue;
            }
            if solver.uf_apps[i].arg_vars.len() != solver.uf_apps[j].arg_vars.len() {
                continue;
            }
            pairs.push((
                solver.uf_apps[i].func.clone(),
                solver.uf_apps[i].arg_vars.clone(),
                solver.uf_apps[j].arg_vars.clone(),
                solver.uf_apps[i].result_var,
                solver.uf_apps[j].result_var,
            ));
        }
    }
    // Track which arg pairs have already been pushed to ackermann_arg_tprop.
    // Multiple Ackermann function-call pairs often share the same arg comparison
    // (e.g. op(e0,X) vs op(e1,X) and op(e0,Y) vs op(e1,Y) both use the e0-e1
    // pair).  Without dedup, ackermann_arg_tprop grows O(n²) even though there
    // are only O(k²) unique pairs for k distinct argument values.  Each TFC probe
    // and incremental-probe call iterates the whole list, so O(n²) entries
    // means O(n²) Simplex clones per call — catastrophic for large quasigroup/
    // permutation benchmarks with n=25 function applications (300 pairs → 600
    // useless clones vs 20 with dedup).
    let mut seen_tprop_pairs: FxHashSet<u32> = FxHashSet::default();
    for (_func, args_i, args_j, ri, rj) in pairs {
        if args_i.iter().zip(args_j.iter()).any(|(&a, &b)| args_provably_differ(a, b, solver)) {
            continue;
        }
        // Encode arg equalities, collecting le/ge SAT vars for T-propagation.
        let mut arg_lits: Vec<Literal> = Vec::with_capacity(args_i.len());
        for (&a, &b) in args_i.iter().zip(args_j.iter()) {
            let (eq_lit, le_sat, ge_sat) = encode_var_eq(a, b, solver);
            arg_lits.push(eq_lit);
            // Register non-trivial arg pairs for T-propagation.
            // Trivial pairs (a==b, le_sat==0) are always-true and need neither.
            // Deduplicate by le_sat: the same arg pair (same diff slack,
            // same le_sat atom) must not appear twice in ackermann_arg_tprop.
            if le_sat != 0 {
                solver.ackermann_le_ge_atoms.insert(le_sat);
                solver.ackermann_le_ge_atoms.insert(ge_sat);
                if seen_tprop_pairs.insert(le_sat) {
                    solver.ackermann_arg_tprop.push((a, b, le_sat, ge_sat));
                }
            }
        }
        // Encode result equality.
        let (res_eq, _, _) = encode_var_eq(ri, rj, solver);
        // Defer the Ackermann clause (¬eq_0 ∨ … ∨ res_eq) to TFC.
        // Adding it here for every pair would create O(n²) BCP-active clauses
        // that dominate the SAT instance for problems with many UF applications
        // (e.g. processor verification benchmarks with 10,000+ pairs).
        // TFC checks model values and returns the violated clause on demand.
        let pair_idx = solver.ackermann_full_pairs.len();
        for lit in &arg_lits {
            solver.ackermann_cong_watcher
                .entry(lit.var())
                .or_default()
                .push(pair_idx);
        }
        solver.ackermann_full_pairs.push((arg_lits, res_eq, ri, rj));
    }
}

// ---------------------------------------------------------------------------
// Term encoding
// ---------------------------------------------------------------------------

/// Reduce a LinearForm to a single Simplex variable, creating a slack row if
/// necessary. The same canonical form always maps to the same variable.
fn form_to_var(form: LinearForm, solver: &mut LiaCdclT) -> u32 {
    // Fast path: form is already a single variable with coefficient 1.
    if form.constant == 0 && form.coeffs.len() == 1 {
        let (&v, &c) = form.coeffs.iter().next().unwrap();
        if c == 1 {
            return v;
        }
    }
    // Build a canonical sorted key for the cache.
    let mut key_pairs: Vec<(u32, i64)> =
        form.coeffs.iter().filter(|(_, &c)| c != 0).map(|(&v, &c)| (v, c)).collect();
    key_pairs.sort_unstable();
    let cache_key = (key_pairs, form.constant);
    if let Some(&v) = solver.form_to_var_cache.get(&cache_key) {
        return v;
    }
    let slack = get_or_create_slack(&form, solver);
    solver.var_to_form.insert(slack, cache_key.clone());
    solver.form_to_var_cache.insert(cache_key, slack);
    slack
}

/// Extract a linear form from a term, mapping variable names to Simplex var ids.
/// For UF applications with arithmetic sort, creates (or retrieves cached)
/// Simplex variables and registers Ackermann app records on first encounter.
fn extract_linear(term: &Term, solver: &mut LiaCdclT) -> Option<LinearForm> {
    match &term.inner {
        TermInner::IntLiteral(n) => {
            let mut f = LinearForm::default();
            f.constant = *n;
            Some(f)
        }
        TermInner::Variable(name) if term.sort.is_arithmetic() => {
            let v = *solver.var_ids.get(name.as_str())?;
            let mut f = LinearForm::default();
            f.coeffs.insert(v, 1);
            Some(f)
        }
        TermInner::ArithOp(ArithOpKind::Add, args) => {
            let mut acc = LinearForm::default();
            for a in args {
                let f = extract_linear(a, solver)?;
                acc.add_scaled(&f, 1);
            }
            Some(acc)
        }
        TermInner::ArithOp(ArithOpKind::Sub, args) => match args.len() {
            1 => {
                let mut f = extract_linear(&args[0], solver)?;
                f.negate();
                Some(f)
            }
            2 => {
                let f0 = extract_linear(&args[0], solver)?;
                let f1 = extract_linear(&args[1], solver)?;
                let mut acc = LinearForm::default();
                acc.add_scaled(&f0, 1);
                acc.add_scaled(&f1, -1);
                Some(acc)
            }
            _ => None,
        },
        TermInner::ArithOp(ArithOpKind::Mul, args) => {
            if args.len() != 2 {
                return None;
            }
            let f0 = extract_linear(&args[0], solver)?;
            let f1 = extract_linear(&args[1], solver)?;
            if f0.is_constant() {
                let scale = f0.constant;
                let mut acc = LinearForm::default();
                acc.add_scaled(&f1, scale);
                Some(acc)
            } else if f1.is_constant() {
                let scale = f1.constant;
                let mut acc = LinearForm::default();
                acc.add_scaled(&f0, scale);
                Some(acc)
            } else {
                None // non-linear
            }
        }
        TermInner::Ite(cond, t_then, t_else) if term.sort.is_arithmetic() => {
            // Encode integer ite: result = if cond { t_then } else { t_else }.
            // Create a fresh Simplex variable r, then add:
            //   cond → r = t_then   (¬cond_lit ∨ rt_eq)
            //   ¬cond → r = t_else  (cond_lit ∨ re_eq)
            let t_form = extract_linear(t_then, solver)?;
            let e_form = extract_linear(t_else, solver)?;
            let tv = form_to_var(t_form, solver);
            let ev = form_to_var(e_form, solver);
            let c_lit = encode_bool(cond, solver).ok()?;
            let r = solver.alloc_simplex();
            let (rt_eq, rt_le, rt_ge) = encode_var_eq(r, tv, solver);
            let (re_eq, re_le, re_ge) = encode_var_eq(r, ev, solver);
            // Mark ITE equality le/ge atoms as unsafe for tightening: both can be
            // simultaneously FALSE before the cond gate resolves, so applying
            // ¬(diff≤0)→diff≥1 and ¬(diff≥0)→diff≤-1 together creates unsound bounds.
            for &s in &[rt_le, rt_ge, re_le, re_ge] {
                if s != 0 { solver.ackermann_le_ge_atoms.insert(s); }
            }
            solver.add_clause(&[c_lit.negate(), rt_eq]);
            solver.add_clause(&[c_lit, re_eq]);
            let mut f = LinearForm::default();
            f.coeffs.insert(r, 1);
            Some(f)
        }
        TermInner::FunCall(name, args) if term.sort.is_arithmetic() => {
            // Encode a UF application as a fresh Simplex variable via Ackermann
            // flattening.  Each arg is reduced to a single Simplex variable; the
            // cache key (func_name, arg_var_ids) deduplicates repeated occurrences.
            let mut arg_vars: Vec<u32> = Vec::with_capacity(args.len());
            for arg in args {
                let form = extract_linear(arg, solver)?;
                let v = form_to_var(form, solver);
                arg_vars.push(v);
            }
            let cache_key = (name.clone(), arg_vars.clone());
            if let Some(&result_var) = solver.uf_app_cache.get(&cache_key) {
                let mut f = LinearForm::default();
                f.coeffs.insert(result_var, 1);
                return Some(f);
            }
            let result_var = solver.alloc_simplex();
            solver.uf_app_cache.insert(cache_key, result_var);
            solver.uf_apps.push(UfApp { func: name.clone(), arg_vars, result_var });
            let mut f = LinearForm::default();
            f.coeffs.insert(result_var, 1);
            Some(f)
        }
        _ => None,
    }
}

/// Introduce a slack variable for a linear form (lhs - rhs).
/// Returns (diff_form, rhs_constant) where diff_form has zero constant term.
fn normalize_cmp(
    lhs: &Term,
    rhs: &Term,
    solver: &mut LiaCdclT,
) -> Option<(LinearForm, i64)> {
    let f_lhs = extract_linear(lhs, solver)?;
    let f_rhs = extract_linear(rhs, solver)?;
    let mut diff = LinearForm::default();
    diff.add_scaled(&f_lhs, 1);
    diff.add_scaled(&f_rhs, -1);
    let rhs_const = -diff.constant;
    diff.constant = 0;
    Some((diff, rhs_const))
}

/// Get or create a Simplex slack for a linear form. Adds the row if new.
fn get_or_create_slack(
    form: &LinearForm,
    solver: &mut LiaCdclT,
) -> u32 {
    let slack = solver.alloc_simplex();
    let mut coeffs: Vec<(u32, Rational)> = form
        .coeffs
        .iter()
        .filter(|(_, &c)| c != 0)
        .map(|(&v, &c)| (v, Rational::from_int(c)))
        .collect();
    if !coeffs.is_empty() {
        if form.constant != 0 {
            // Encode the constant offset as `k * one_var` so the Simplex row
            // represents the full linear form, not just the variable part.
            coeffs.push((solver.one_var, Rational::from_int(form.constant)));
        }
        solver.simplex.add_row(slack, coeffs);
    } else {
        // Constant-only form: pin the slack to its exact integer value via
        // SAT-forced bounds. Without bounds the Simplex treats the variable as
        // free, which makes every Ackermann arg-equality premise trivially
        // satisfiable and forces spurious UF congruences.
        let k = form.constant;
        let le_sat = solver.alloc_sat();
        solver.atoms.insert(le_sat, SimplexAtom::Upper { var: slack, bound: k });
        solver.add_clause(&[Literal::positive(le_sat)]);
        let ge_sat = solver.alloc_sat();
        solver.atoms.insert(ge_sat, SimplexAtom::Lower { var: slack, bound: k });
        solver.add_clause(&[Literal::positive(ge_sat)]);
    }
    slack
}

/// Encode a Boolean term into a SAT literal (with Tseitin for Boolean connectives).
/// Returns Err(()) if the term is not encodable (unsupported construct).
fn encode_bool(term: &Term, solver: &mut LiaCdclT) -> Result<Literal, ()> {
    match &term.inner {
        TermInner::True => {
            let v = solver.alloc_sat();
            solver.add_clause(&[Literal::positive(v)]);
            Ok(Literal::positive(v))
        }
        TermInner::False => {
            let v = solver.alloc_sat();
            solver.add_clause(&[Literal::negative(v)]);
            Ok(Literal::negative(v))
        }
        TermInner::Not(inner) if matches!(inner.inner, TermInner::Eq(..))
            && matches!(
                inner.inner,
                TermInner::Eq(ref a, _) if a.sort.is_arithmetic()
            ) =>
        {
            // Arithmetic disequality: x ≠ c  ↔  (x < c) ∨ (x > c)
            if let TermInner::Eq(lhs, rhs) = &inner.inner {
                let lt_lit = encode_arith_cmp(ArithCmpKind::Lt, lhs, rhs, solver)?;
                let gt_lit = encode_arith_cmp(ArithCmpKind::Gt, lhs, rhs, solver)?;
                let v = solver.alloc_sat();
                let z = Literal::positive(v);
                solver.add_clause(&[z.negate(), lt_lit, gt_lit]);
                solver.add_clause(&[lt_lit.negate(), z]);
                solver.add_clause(&[gt_lit.negate(), z]);
                return Ok(z);
            }
            unreachable!()
        }
        TermInner::Not(inner) => {
            match &inner.inner {
                // ¬(ArithCmp): encode the dual comparison as a positive atom so
                // theory_propagate asserts the bound when the literal is TRUE.
                // e.g. ¬(x ≤ k) → Lower(x, k+1).
                TermInner::ArithCmp(kind, lhs, rhs) => {
                    let dual = match kind {
                        ArithCmpKind::Le => ArithCmpKind::Gt,
                        ArithCmpKind::Lt => ArithCmpKind::Ge,
                        ArithCmpKind::Ge => ArithCmpKind::Lt,
                        ArithCmpKind::Gt => ArithCmpKind::Le,
                    };
                    return encode_arith_cmp(dual, lhs, rhs, solver);
                }
                // De Morgan: ¬(A∨B∨…) → (¬A ∧ ¬B ∧ …).
                // Push negation inside so ¬(ArithCmp) sub-expressions become
                // positive atoms (e.g. ¬(x≤k) → Lower(x,k+1)), which lets
                // theory_propagate assert their bounds when the conjunction is TRUE.
                // Without this, the formula ¬(¬P ∨ Q) would force both ¬P=FALSE
                // (→P=TRUE) and Q=FALSE as negative atoms that theory_propagate
                // silently skips, missing the infeasibility.
                TermInner::Or(subs) => {
                    let subs_clone: Vec<Term> = subs.clone();
                    let neg_lits: Vec<Literal> = subs_clone
                        .into_iter()
                        .map(|s| {
                            let neg = Term {
                                sort: SortExpr::Bool,
                                inner: TermInner::Not(Box::new(s)),
                            };
                            encode_bool(&neg, solver)
                        })
                        .collect::<Result<_, _>>()?;
                    let v = solver.alloc_sat();
                    let z = Literal::positive(v);
                    for &sl in &neg_lits {
                        solver.add_clause(&[z.negate(), sl]);
                    }
                    let mut cl: Vec<Literal> = neg_lits.iter().map(|l| l.negate()).collect();
                    cl.push(z);
                    solver.add_clause(&cl);
                    return Ok(z);
                }
                // Double negation: ¬(¬x) → x.
                TermInner::Not(inner2) => {
                    return encode_bool(inner2, solver);
                }
                _ => {}
            }
            let l = encode_bool(inner, solver)?;
            Ok(l.negate())
        }
        TermInner::And(args) => {
            let subs: Vec<Literal> = args
                .iter()
                .map(|a| encode_bool(a, solver))
                .collect::<Result<_, _>>()?;
            let v = solver.alloc_sat();
            let z = Literal::positive(v);
            for &sl in &subs {
                solver.add_clause(&[z.negate(), sl]);
            }
            let mut cl: Vec<Literal> = subs.iter().map(|l| l.negate()).collect();
            cl.push(z);
            solver.add_clause(&cl);
            Ok(z)
        }
        TermInner::Or(args) => {
            let subs: Vec<Literal> = args
                .iter()
                .map(|a| encode_bool(a, solver))
                .collect::<Result<_, _>>()?;
            let v = solver.alloc_sat();
            let z = Literal::positive(v);
            let mut cl = vec![z.negate()];
            cl.extend_from_slice(&subs);
            solver.add_clause(&cl);
            for &sl in &subs {
                solver.add_clause(&[sl.negate(), z]);
            }
            Ok(z)
        }
        TermInner::Ite(cond, t, e) if term.sort == SortExpr::Bool => {
            let c = encode_bool(cond, solver)?;
            let tl = encode_bool(t, solver)?;
            let el = encode_bool(e, solver)?;
            let v = solver.alloc_sat();
            let z = Literal::positive(v);
            // z ↔ ite(c, tl, el): standard Tseitin for mux
            solver.add_clause(&[z.negate(), c.negate(), tl]);
            solver.add_clause(&[z.negate(), c, el]);
            solver.add_clause(&[c.negate(), tl.negate(), z]);
            solver.add_clause(&[c, el.negate(), z]);
            Ok(z)
        }
        TermInner::ArithCmp(kind, lhs, rhs) => {
            encode_arith_cmp(*kind, lhs, rhs, solver)
        }
        TermInner::Eq(lhs, rhs) if lhs.sort.is_arithmetic() => {
            // Arithmetic equality: x = c  ↔  (x ≤ c) ∧ (x ≥ c).
            let le_lit = encode_arith_cmp(ArithCmpKind::Le, lhs, rhs, solver)?;
            let ge_lit = encode_arith_cmp(ArithCmpKind::Ge, lhs, rhs, solver)?;
            // Tseitin AND: v ↔ (le ∧ ge)
            let v = solver.alloc_sat();
            let z = Literal::positive(v);
            solver.add_clause(&[z.negate(), le_lit]);
            solver.add_clause(&[z.negate(), ge_lit]);
            solver.add_clause(&[z, le_lit.negate(), ge_lit.negate()]);
            Ok(z)
        }
        TermInner::Variable(name) if term.sort == SortExpr::Bool => {
            // Boolean variable: reuse the same SAT var across all occurrences of the same name.
            let v = if let Some(&existing) = solver.bool_var_ids.get(name.as_str()) {
                existing
            } else {
                let v = solver.alloc_sat();
                solver.bool_var_ids.insert(name.clone(), v);
                v
            };
            Ok(Literal::positive(v))
        }
        TermInner::Eq(_, _) => {
            // Non-arithmetic equality (e.g. two UF-sorted constants): model as a fresh
            // unconstrained propositional atom. No congruence closure; this lets the
            // formula structure remain intact so arithmetic assertions can still be
            // encoded. Works correctly for problems where UNSAT comes from arithmetic
            // alone (e.g. TwoSquares benchmarks with declare-sort S1 0).
            let v = solver.alloc_sat();
            Ok(Literal::positive(v))
        }
        _ => Err(()),
    }
}

fn encode_arith_cmp(
    kind: ArithCmpKind,
    lhs: &Term,
    rhs: &Term,
    solver: &mut LiaCdclT,
) -> Result<Literal, ()> {
    let (form, rhs_const) = normalize_cmp(lhs, rhs, solver).ok_or(())?;

    // If the form is purely constant (no variables), evaluate statically.
    if form.is_constant() {
        let holds = match kind {
            ArithCmpKind::Le => 0 <= rhs_const,
            ArithCmpKind::Lt => 0 < rhs_const,
            ArithCmpKind::Ge => 0 >= rhs_const,
            ArithCmpKind::Gt => 0 > rhs_const,
        };
        let v = solver.alloc_sat();
        if holds {
            // v is always true: the comparison is a tautology.
            solver.add_clause(&[Literal::positive(v)]);
            return Ok(Literal::positive(v));
        } else {
            // v must be false: the comparison is a contradiction.
            // Add unit clause ¬v (forces v=false) and return v as the FALSE literal.
            solver.add_clause(&[Literal::negative(v)]);
            return Ok(Literal::positive(v));
        }
    }

    // Use form_to_var so single-variable forms reuse the user var directly (no
    // redundant slack row), and multi-variable forms share the cached slack.
    let slack = form_to_var(form, solver);

    // Map the comparison to a Simplex atom:
    // slack = lhs_vars - rhs_vars
    // Le: slack ≤ rhs_const   → Upper(slack, rhs_const)
    // Lt: slack ≤ rhs_const-1 → Upper(slack, rhs_const-1)  [integers]
    // Ge: slack ≥ rhs_const   → Lower(slack, rhs_const)
    // Gt: slack ≥ rhs_const+1 → Lower(slack, rhs_const+1)  [integers]
    let (is_upper, bound) = match kind {
        ArithCmpKind::Le => (true, rhs_const),
        ArithCmpKind::Lt => (true, rhs_const - 1),
        ArithCmpKind::Ge => (false, rhs_const),
        ArithCmpKind::Gt => (false, rhs_const + 1),
    };
    let cache_key = (slack, is_upper, bound);
    if let Some(&v) = solver.arith_atom_cache.get(&cache_key) {
        return Ok(Literal::positive(v));
    }
    let v = solver.alloc_sat();
    let atom = if is_upper {
        SimplexAtom::Upper { var: slack, bound }
    } else {
        SimplexAtom::Lower { var: slack, bound }
    };
    solver.atoms.insert(v, atom);
    solver.arith_atom_cache.insert(cache_key, v);
    Ok(Literal::positive(v))
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Solve a QF_LIA / QF_LRA problem given the raw SMT-LIB text.
/// `cancel` is set to `true` by the benchmark harness when the timeout fires.
pub fn solve_qf_lia(text: &str, cancel: Arc<AtomicBool>) -> Result<LiaResult, String> {
    let script = Script::parse(text).map_err(|e| e.to_string())?;
    if script.assertions().is_empty() {
        return Ok(LiaResult { status: LiaStatus::Sat, model: vec![] });
    }

    // Collect Int/Real declared constants.
    let mut var_names: Vec<(String, SortExpr)> = Vec::new();
    use rm_syntax::Command;
    for cmd in &script.commands {
        if let Command::DeclareFun { name, args, result } = cmd {
            if args.is_empty() && result.is_arithmetic() {
                var_names.push((name.clone(), result.clone()));
            }
        }
    }

    // Allocate Simplex variables: first come user vars, then slacks.
    // Pre-allocate enough space. We'll conservatively use 2x user vars as
    // initial capacity; slacks are added dynamically.
    let user_count = var_names.len() as u32;
    // Rough upper bound: each comparison can introduce one slack; UF applications
    // each get a result var plus additional slacks for Ackermann constraints.
    let max_atoms = count_assertions(&script);
    let max_simplex = user_count + max_atoms * 8 + 64;

    let mut solver = LiaCdclT::new(max_simplex, cancel.clone());
    solver.next_simplex_var = user_count;

    for (i, (name, sort)) in var_names.iter().enumerate() {
        let id = i as u32;
        solver.var_ids.insert(name.clone(), id);
        if i < solver.is_int.len() {
            solver.is_int[i] = *sort == SortExpr::Int;
        }
    }

    // Allocate the "one variable": always fixed to 1 so constant offsets in
    // linear forms can be encoded as `k * one_var` in Simplex rows.
    {
        let ov = solver.alloc_simplex();
        solver.one_var = ov;
        solver.is_int[ov as usize] = false;
        let ov_le = solver.alloc_sat();
        solver.atoms.insert(ov_le, SimplexAtom::Upper { var: ov, bound: 1 });
        solver.add_clause(&[Literal::positive(ov_le)]);
        let ov_ge = solver.alloc_sat();
        solver.atoms.insert(ov_ge, SimplexAtom::Lower { var: ov, bound: 1 });
        solver.add_clause(&[Literal::positive(ov_ge)]);
    }

    // Encode assertions.
    for assertion in script.assertions() {
        match encode_bool(assertion, &mut solver) {
            Ok(lit) => solver.add_clause(&[lit]),
            Err(()) => {
                return Ok(LiaResult {
                    status: LiaStatus::Unknown,
                    model: Vec::new(),
                });
            }
        }
    }

    // Add Ackermann congruence constraints for all pairs of UF applications
    // with the same function symbol before handing off to the SAT/B&B loop.
    add_ackermann_constraints(&mut solver);

    // Save the Simplex state after encoding (rows only, no bounds).
    // theory_final_check clones this for each full-model rational check so it
    // starts from a clean state rather than an incremental state with stale bounds.
    solver.initial_simplex = Some(solver.simplex.clone());

    let status = solver.solve();
    let model = if status == LiaStatus::Sat {
        solver
            .var_ids
            .iter()
            .map(|(name, &id)| {
                // Use the scratch-model snapshot saved by theory_final_check rather
                // than the incremental Simplex, which may have stale bounds after
                // branch-and-bound pivots.
                let val = solver
                    .last_sat_model_values
                    .get(&id)
                    .copied()
                    .unwrap_or_else(|| solver.simplex.model_int(id));
                (name.clone(), val)
            })
            .collect()
    } else {
        Vec::new()
    };
    Ok(LiaResult { status, model })
}

fn count_assertions(script: &Script) -> u32 {
    // Rough count: number of assertion terms (each may introduce a few slacks).
    script.assertions().len() as u32 * 4 + 16
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn run(text: &str) -> LiaResult {
        solve_qf_lia(text, Arc::new(AtomicBool::new(false))).expect("parse error")
    }

    fn sat(text: &str) -> bool {
        run(text).status == LiaStatus::Sat
    }

    fn unsat(text: &str) -> bool {
        run(text).status == LiaStatus::Unsat
    }

    const PREAMBLE: &str = "(set-logic QF_LIA)\n\
                             (declare-fun x () Int)\n\
                             (declare-fun y () Int)\n";

    #[test]
    fn trivial_sat() {
        assert!(sat(&format!("{PREAMBLE}(assert (>= x 0))\n(check-sat)\n")));
    }

    #[test]
    fn trivial_unsat() {
        // x >= 5 and x <= 3
        assert!(unsat(&format!(
            "{PREAMBLE}(assert (>= x 5))\n(assert (<= x 3))\n(check-sat)\n"
        )));
    }

    #[test]
    fn simple_two_var_sat() {
        // x + y <= 10, x >= 2, y >= 3 → SAT (x=2, y=3 works)
        assert!(sat(&format!(
            "{PREAMBLE}\
             (assert (<= (+ x y) 10))\n\
             (assert (>= x 2))\n\
             (assert (>= y 3))\n\
             (check-sat)\n"
        )));
    }

    #[test]
    fn simple_two_var_unsat() {
        // x + y >= 10, x <= 3, y <= 3 → x+y <= 6 < 10 → UNSAT
        assert!(unsat(&format!(
            "{PREAMBLE}\
             (assert (>= (+ x y) 10))\n\
             (assert (<= x 3))\n\
             (assert (<= y 3))\n\
             (check-sat)\n"
        )));
    }

    #[test]
    fn scaled_var_sat() {
        // 2*x + y <= 7, x >= 2, y >= 1 → x=2, y=1, 2*2+1=5<=7 → SAT
        assert!(sat(&format!(
            "{PREAMBLE}\
             (assert (<= (+ (* 2 x) y) 7))\n\
             (assert (>= x 2))\n\
             (assert (>= y 1))\n\
             (check-sat)\n"
        )));
    }

    #[test]
    fn scaled_var_unsat() {
        // 2*x + y >= 10, x <= 3, y <= 2 → max 2*3+2=8 < 10 → UNSAT
        assert!(unsat(&format!(
            "{PREAMBLE}\
             (assert (>= (+ (* 2 x) y) 10))\n\
             (assert (<= x 3))\n\
             (assert (<= y 2))\n\
             (check-sat)\n"
        )));
    }

    #[test]
    fn disjunction_sat() {
        // (x <= 0 or x >= 5), x = 7 → SAT (x=7 satisfies x>=5)
        assert!(sat(&format!(
            "{PREAMBLE}\
             (assert (or (<= x 0) (>= x 5)))\n\
             (assert (= x 7))\n\
             (check-sat)\n"
        )));
    }

    #[test]
    fn disjunction_unsat() {
        // (x <= -1 or x >= 5), 1 <= x, x <= 4 → UNSAT
        assert!(unsat(&format!(
            "{PREAMBLE}\
             (assert (or (<= x (- 1)) (>= x 5)))\n\
             (assert (>= x 1))\n\
             (assert (<= x 4))\n\
             (check-sat)\n"
        )));
    }

    #[test]
    fn model_extraction() {
        let r = run(&format!(
            "{PREAMBLE}\
             (assert (= x 42))\n\
             (check-sat)\n"
        ));
        assert_eq!(r.status, LiaStatus::Sat);
        let xval = r.model.iter().find(|(n, _)| n == "x").map(|(_, v)| *v);
        assert_eq!(xval, Some(42), "model: {:?}", r.model);
    }

    /// Rational relaxation has the non-integer solution x=2.5, y=2.5.
    /// Branch-and-bound must pick x≤2 or x≥3 and find the integer SAT solution.
    #[test]
    fn branch_and_bound_sat() {
        // 2x + 2y >= 10, x >= 2, y >= 2 — all integer solutions exist (e.g. x=3, y=2)
        assert!(sat(&format!(
            "{PREAMBLE}\
             (assert (>= (+ (* 2 x) (* 2 y)) 10))\n\
             (assert (>= x 2))\n\
             (assert (>= y 2))\n\
             (check-sat)\n"
        )));
    }

    /// 2x + 2y >= 11, x <= 2, y <= 2 — max integer value 2*2+2*2=8 < 11 → UNSAT.
    /// Rational relaxation is SAT (x=y=2.75), so B&B must prove UNSAT.
    #[test]
    fn branch_and_bound_unsat() {
        assert!(unsat(&format!(
            "{PREAMBLE}\
             (assert (>= (+ (* 2 x) (* 2 y)) 11))\n\
             (assert (<= x 2))\n\
             (assert (<= y 2))\n\
             (check-sat)\n"
        )));
    }

    /// B&B with an explicit disjunction: exactly one of two ranges must hold.
    #[test]
    fn branch_and_bound_with_disjunction() {
        // (x = 1 or x = 3), 2x + y = 7  → x=3,y=1 is the only integer solution
        assert!(sat(&format!(
            "(set-logic QF_LIA)\n\
             (declare-fun x () Int)\n\
             (declare-fun y () Int)\n\
             (assert (or (= x 1) (= x 3)))\n\
             (assert (= (+ (* 2 x) y) 7))\n\
             (check-sat)\n"
        )));
    }

    /// Model values satisfy the original constraints.
    #[test]
    fn model_satisfies_constraints() {
        let r = run(&format!(
            "{PREAMBLE}\
             (assert (<= (+ x y) 5))\n\
             (assert (>= x 2))\n\
             (assert (>= y 1))\n\
             (check-sat)\n"
        ));
        assert_eq!(r.status, LiaStatus::Sat);
        let x = r.model.iter().find(|(n, _)| n == "x").map(|(_, v)| *v).unwrap();
        let y = r.model.iter().find(|(n, _)| n == "y").map(|(_, v)| *v).unwrap();
        assert!(x + y <= 5, "x+y={}", x + y);
        assert!(x >= 2, "x={}", x);
        assert!(y >= 1, "y={}", y);
    }

    // -----------------------------------------------------------------------
    // QF_UFLIA tests
    // -----------------------------------------------------------------------

    const UF_PREAMBLE: &str = "(set-logic QF_UFLIA)\n\
                                (declare-fun x () Int)\n\
                                (declare-fun y () Int)\n\
                                (declare-fun f (Int) Int)\n";

    /// f(x) = 5, same term appears twice → SAT
    #[test]
    fn uf_trivial_sat() {
        assert!(sat(&format!(
            "{UF_PREAMBLE}\
             (assert (= (f x) 5))\n\
             (check-sat)\n"
        )));
    }

    /// f(x) = 3 ∧ f(x) = 5 → UNSAT (same application, conflicting bounds)
    #[test]
    fn uf_same_app_conflict() {
        assert!(unsat(&format!(
            "{UF_PREAMBLE}\
             (assert (= (f x) 3))\n\
             (assert (= (f x) 5))\n\
             (check-sat)\n"
        )));
    }

    /// x = y ∧ f(x) = 3 ∧ f(y) ≠ 3 → UNSAT by congruence
    #[test]
    fn uf_congruence_unsat() {
        assert!(unsat(&format!(
            "{UF_PREAMBLE}\
             (assert (= x y))\n\
             (assert (= (f x) 3))\n\
             (assert (not (= (f y) 3)))\n\
             (check-sat)\n"
        )));
    }

    /// x ≠ y allows f(x) ≠ f(y) → SAT
    #[test]
    fn uf_distinct_args_sat() {
        assert!(sat(&format!(
            "{UF_PREAMBLE}\
             (assert (not (= x y)))\n\
             (assert (= (f x) 1))\n\
             (assert (= (f y) 2))\n\
             (check-sat)\n"
        )));
    }

    /// 2-arity UF: g(x,y) = g(x,y) + 1 → UNSAT
    #[test]
    fn uf_arity2_unsat() {
        assert!(unsat(
            "(set-logic QF_UFLIA)\n\
             (declare-fun x () Int)\n\
             (declare-fun y () Int)\n\
             (declare-fun g (Int Int) Int)\n\
             (assert (= (g x y) (+ (g x y) 1)))\n\
             (check-sat)\n"
        ));
    }

    /// Arithmetic on UF result: f(x) + f(y) ≤ 3, f(x) ≥ 2, f(y) ≥ 2 → UNSAT
    #[test]
    fn uf_arith_on_results_unsat() {
        assert!(unsat(&format!(
            "{UF_PREAMBLE}\
             (assert (<= (+ (f x) (f y)) 3))\n\
             (assert (>= (f x) 2))\n\
             (assert (>= (f y) 2))\n\
             (check-sat)\n"
        )));
    }

    /// f(x+1)=5, f(y)=3, y=x+1 → UNSAT: args are equal so Ackermann forces f(x+1)=f(y).
    /// Tests that constant offsets in linear UF args are correctly encoded.
    #[test]
    fn uf_constant_offset_arg_unsat() {
        assert!(unsat(
            "(set-logic QF_UFLIA)\n\
             (declare-fun x () Int)\n\
             (declare-fun y () Int)\n\
             (declare-fun f (Int) Int)\n\
             (assert (= y (+ x 1)))\n\
             (assert (= (f (+ x 1)) 5))\n\
             (assert (= (f y) 3))\n\
             (check-sat)\n"
        ));
    }

    /// f(x+2) = 5 and f(x+2) = 3 → UNSAT.
    /// Same arg via different paths; congruence must agree.
    #[test]
    fn uf_constant_offset_same_arg_unsat() {
        assert!(unsat(
            "(set-logic QF_UFLIA)\n\
             (declare-fun x () Int)\n\
             (declare-fun f (Int) Int)\n\
             (assert (= (f (+ x 2)) 5))\n\
             (assert (= (f (+ x 2)) 3))\n\
             (check-sat)\n"
        ));
    }
}
