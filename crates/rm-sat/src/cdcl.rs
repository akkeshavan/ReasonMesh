//! Production CDCL solver — M1 + M2 performance improvements.
//!
//! Implements:
//! - Two-watched-literal BCP with binary clause fast path
//! - 1-UIP conflict analysis with recursive clause minimization
//! - VSIDS with aggressive decay (0.8) and phase saving
//! - Glucose-style EMA restart (fast/slow LBD EMAs) with Luby fallback
//! - LBD-based learned-clause deletion with activity tiebreaking
//! - Failed literal probing (inprocessing) every 10 restarts
//! - XOR/parity reasoning: GF(2) unit propagation for parity-chain benchmarks

// S1-7: Chronological backtracking minimum gap.
// Only trigger chrono BT when the non-chrono jump would be this many levels deep.
// At gap=5 this fires for almost any conflict on medium/large instances, forcing
// many single-level backtracks before reaching the UIP backjump level.
// Raising to 30 restricts chrono BT to very deep jumps where it genuinely helps.
const CHRONO_BT_MIN_GAP: u32 = 30;

// ---------------------------------------------------------------------------
// Theory integration trait (DPLL(T) / CDCL(T))
// ---------------------------------------------------------------------------

/// Trait implemented by SMT theory solvers for DPLL(T) integration.
///
/// `solve_with_theory` calls `theory_propagate` after each BCP fixed point.
/// The theory can:
///   - Return `Ok(lemmas)`: add `lemmas` as new clauses; empty means no new information.
///   - Return `Err(conflict)`: the conflict clause is added to the SAT solver which
///     detects the conflict on the next propagation pass.
///
/// `theory_backtrack` is called before every backtrack so the theory can undo
/// assertions made at levels above `target_level`.
pub trait TheorySolver {
    /// Called after each BCP fixed point at decision `level`.
    /// `trail` is the full current assignment trail (all literals in order).
    /// `prev_trail_len` is the trail length at the previous theory call.
    fn theory_propagate(
        &mut self,
        level: u32,
        trail: &[Literal],
        prev_trail_len: usize,
    ) -> Result<Vec<Vec<Literal>>, Vec<Literal>>;

    /// Called before the SAT solver backtracks to `target_level`.
    fn theory_backtrack(&mut self, target_level: u32);

    /// Called when the SAT backbone returns a complete model.
    /// Returns `Some(conflict_clause)` if the model is theory-inconsistent,
    /// `None` if consistent. Default: always consistent (pure SAT, no theory).
    fn theory_final_check(&mut self, model: &Model) -> Option<Vec<Literal>> {
        let _ = model;
        None
    }

    /// Whether `theory_final_check` leaves the incremental theory state intact.
    /// When true, the CDCL loop may backjump to the UIP level after a TFC conflict
    /// (the theory state at that level is valid). When false, TFC has reset internal
    /// theory state (e.g. CC wiped by a fresh check), so the CDCL loop must backjump
    /// to base level and let `theory_propagate` rebuild state from scratch.
    fn theory_final_check_preserves_state(&self) -> bool {
        false
    }
}

use crate::{
    assignment::{Assignment, Value},
    bve::ElimEntry,
    clause::{ClauseArena, ClauseRef},
    model::Model,
    vmtf::VmtfList,
    watched::WatchList,
    xor::XorClause,
};
use rm_akx::literal::{Literal, Var};
use rm_gpu::GpuClause;
use smallvec::SmallVec;
use std::collections::BinaryHeap;
use std::time::Instant;

// ---------------------------------------------------------------------------
// Stable/focus mode alternation (Kissat-style)
// ---------------------------------------------------------------------------

/// Focus mode: aggressive EMA restarts, no walk, faster learning.
/// Stable mode: Luby restarts with 4× scale, walk enabled before each restart.
/// Phases alternate every PHASE_LEN restarts.
const PHASE_LEN: u64 = 16;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum SolverMode {
    Focus,
    Stable,
}

// ---------------------------------------------------------------------------
// Result type
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub enum SolveResult {
    Sat(Model),
    Unsat,
    Unknown,
    /// Conflict budget exhausted before the deadline — the caller may resplit.
    BudgetExceeded,
}

impl PartialEq for SolveResult {
    fn eq(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (Self::Unsat, Self::Unsat)
                | (Self::Unknown, Self::Unknown)
                | (Self::BudgetExceeded, Self::BudgetExceeded)
        )
    }
}

// ---------------------------------------------------------------------------
// VSIDS heap entry (lazy-deletion max-heap by activity)
// ---------------------------------------------------------------------------

#[derive(PartialEq)]
struct VsidsEntry {
    activity: f64,
    var: Var,
}
impl Eq for VsidsEntry {}
impl PartialOrd for VsidsEntry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for VsidsEntry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Activities are always finite; total_cmp avoids the NaN branch of partial_cmp.
        self.activity
            .total_cmp(&other.activity)
            .then_with(|| other.var.cmp(&self.var))
    }
}

// ---------------------------------------------------------------------------
// BCP branch-frequency counters
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, Default)]
pub struct BcpStats {
    pub binary_checks: u64,
    pub watch_entries_visited: u64,
    pub blocker_hits: u64,
    pub clause_fetches: u64,
    pub new_watch_found: u64,
    pub unit_props: u64,
    pub bcp_conflicts: u64,
}

// ---------------------------------------------------------------------------
// Solver
// ---------------------------------------------------------------------------

pub struct CdclSolver {
    num_vars: u32,
    assignment: Assignment,
    db: ClauseArena,
    watches: WatchList,

    // VSIDS: activity[var] is bumped on each conflict
    activity: Vec<f64>,
    /// Increment applied to activities on bump; grows by 1/decay each conflict.
    activity_inc: f64,
    activity_decay: f64,
    /// Max-heap for VSIDS variable selection (lazy deletion).
    heap: BinaryHeap<VsidsEntry>,
    /// Phase saving: last known polarity per variable (index = var).
    polarity: Vec<bool>,
    /// Reusable buffer for analyze() — avoids per-conflict Vec allocation.
    trail_buf: Vec<Literal>,

    // Luby restart schedule
    luby_u: u64,
    luby_v: u64,
    luby_scale: u64,
    next_restart_conflicts: u64,

    // Glucose-style EMA restart: restart when fast EMA of LBD exceeds slow EMA.
    // fast alpha = 0.03 (~33 conflict window), slow alpha = 0.00001 (~69k window).
    lbd_fast_ema: f64,
    lbd_slow_ema: f64,
    conflicts_at_last_restart: u64,

    // Binary clause fast path.
    // binaries[lit.raw()] = list of (implied_lit, clause_ref_raw).
    // When lit becomes True, each implied_lit must be True (implication).
    // Binary clauses are stored in the DB for reason tracking but NOT in the
    // watch list; rebuild_watches skips clauses with lits.len() < 3.
    binaries: Vec<Vec<(Literal, u32)>>,

    // Clause deletion
    learnt_limit: usize,
    learnt_limit_inc: f64,
    /// Hard ceiling on the learned-clause limit so long-running SMT timeouts
    /// can't accumulate GB of clauses (limit × 1.1^N otherwise diverges).
    learnt_limit_max: usize,

    // Statistics
    pub conflicts: u64,
    pub propagations: u64,
    pub restarts: u64,
    pub decisions: u64,
    /// Number of chronological backtracks (S1-7).
    pub chrono_bts: u64,

    // BCP branch counters (always enabled; single-cycle increments don't move the needle)
    pub bcp_binary_checks: u64,     // total binary-clause implication checks
    pub bcp_watch_visits: u64,      // total watch-list entries visited
    pub bcp_blocker_hits: u64,      // blocker was True → clause skipped entirely
    pub bcp_clause_fetches: u64,    // fell through to arena access (blocker miss)
    pub bcp_new_watch: u64,         // found a new non-false watch literal
    pub bcp_unit_props: u64,        // clause became unit → forced an assignment
    pub bcp_conflicts: u64,         // clause became conflicting

    /// Decision level of the first assumption pushed by the current `solve` call.
    base_level: u32,

    /// Highest decision level belonging to assumptions of the current `solve` call.
    assumption_floor: u32,

    /// Learned clauses produced since the last `drain_learned`. Drained by the
    /// Reasoner for AKX export.
    learned_outbox: Vec<(Vec<Literal>, u32)>,

    /// DRUP proof log.
    proof_log: Option<Vec<Vec<i32>>>,

    // S1-3: Timestamp seen array — avoids per-conflict Vec allocation.
    seen_stamp: Vec<u32>,
    analyze_stamp: u32,

    // S1-5: Clause activity bumping.
    clause_inc: f32,
    clause_decay: f32,

    // S1-6: Timestamp-based LBD computation.
    lbd_stamp: Vec<u32>,
    lbd_epoch: u32,

    // Inprocessing: failed literal probing every PROBE_CONFLICT_INTERVAL conflicts.
    conflicts_at_last_probe: u64,

    // Stable/focus mode alternation.
    mode: SolverMode,
    phase_restart_count: u64,

    // VMTF variable selection (Focus mode).
    vmtf: VmtfList,

    // BVE-eliminated variables: stored for model extension after solve.
    bve_eliminated: Vec<ElimEntry>,
    // Set to true after the first BVE pass so it never re-runs.
    bve_done: bool,

    /// Optional GPU accelerator for parallel WalkSAT phase guidance.
    /// When None, the existing sequential CPU walk_phase is used unchanged.
    gpu: Option<Box<dyn rm_gpu::GpuAccelerator>>,

    /// Consecutive restarts where walk_phase made zero improvement to the
    /// polarity score.  Once this reaches WALK_GIVE_UP we stop calling the
    /// walk entirely for this instance — it's almost certainly UNSAT and the
    /// walk is pure overhead (CPU: ~50μs/restart × thousands of restarts;
    /// GPU: ~1-2ms/restart × thousands of restarts).
    walk_no_improve: u32,

    // XOR/parity reasoning (GF(2) unit propagation).
    // Populated once after BVE by scanning the clause DB for k=2,3 XOR patterns.
    xor_clauses: Vec<XorClause>,
    xor_init_done: bool,
}

impl CdclSolver {
    pub fn new(num_vars: u32) -> Self {
        let mut heap = BinaryHeap::with_capacity(num_vars as usize + 1);
        for var in 1..=num_vars {
            heap.push(VsidsEntry { activity: 0.0, var });
        }
        CdclSolver {
            num_vars,
            assignment: Assignment::new(num_vars),
            db: ClauseArena::new(),
            watches: WatchList::new(num_vars),
            activity: vec![0.0; num_vars as usize + 1],
            activity_inc: 1.0,
            activity_decay: 0.95,
            heap,
            polarity: vec![false; num_vars as usize + 1],
            trail_buf: Vec::new(),
            luby_u: 1,
            luby_v: 1,
            luby_scale: 25,
            next_restart_conflicts: 25,
            lbd_fast_ema: 0.0,
            lbd_slow_ema: 0.0,
            conflicts_at_last_restart: 0,
            binaries: vec![Vec::new(); (num_vars * 2 + 2) as usize],
            learnt_limit: 5000,
            learnt_limit_inc: 1.1,
            learnt_limit_max: 500_000,
            conflicts: 0,
            propagations: 0,
            restarts: 0,
            decisions: 0,
            chrono_bts: 0,
            bcp_binary_checks: 0,
            bcp_watch_visits: 0,
            bcp_blocker_hits: 0,
            bcp_clause_fetches: 0,
            bcp_new_watch: 0,
            bcp_unit_props: 0,
            bcp_conflicts: 0,
            base_level: 0,
            assumption_floor: 0,
            learned_outbox: Vec::new(),
            proof_log: None,
            seen_stamp: vec![0u32; num_vars as usize + 1],
            analyze_stamp: 0,
            clause_inc: 1.0,
            clause_decay: 0.999,
            lbd_stamp: vec![0u32; num_vars as usize + 2],
            lbd_epoch: 0,
            conflicts_at_last_probe: 0,
            mode: SolverMode::Focus,
            phase_restart_count: 0,
            vmtf: VmtfList::new(num_vars),
            bve_eliminated: Vec::new(),
            bve_done: false,
            gpu: None,
            walk_no_improve: 0,
            xor_clauses: Vec::new(),
            xor_init_done: false,
        }
    }

    /// Number of variables in the formula (index 0 is unused).
    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }

    /// Disable BVE preprocessing for this solver instance.
    pub fn skip_bve(&mut self) {
        self.bve_done = true;
    }

    /// Set a default polarity bias for all variables.
    /// `prefer_true = true`: branch on positive literals first (good for SAT instances).
    /// `prefer_true = false`: branch on negative literals first (more UNSAT-oriented).
    /// Parallel portfolios use alternating bias across threads for search diversity.
    pub fn set_polarity_bias(&mut self, prefer_true: bool) {
        self.polarity.iter_mut().for_each(|p| *p = prefer_true);
    }

    /// Set the Luby restart base scale. Varying this across threads staggers
    /// restart schedules so threads explore different parts of the search space.
    pub fn set_luby_scale(&mut self, scale: u64) {
        self.luby_scale = scale.max(1);
        self.next_restart_conflicts = scale.max(1);
    }

    /// Attach a GPU accelerator for parallel WalkSAT phase guidance.
    /// When set, each `walk_phase()` call dispatches 10 000 trajectories to the
    /// GPU instead of the single-trajectory CPU path.
    pub fn set_gpu(&mut self, gpu: Box<dyn rm_gpu::GpuAccelerator>) {
        self.gpu = Some(gpu);
    }

    /// BCP branch-frequency counters accumulated over the entire solve.
    pub fn bcp_stats(&self) -> BcpStats {
        BcpStats {
            binary_checks: self.bcp_binary_checks,
            watch_entries_visited: self.bcp_watch_visits,
            blocker_hits: self.bcp_blocker_hits,
            clause_fetches: self.bcp_clause_fetches,
            new_watch_found: self.bcp_new_watch,
            unit_props: self.bcp_unit_props,
            bcp_conflicts: self.bcp_conflicts,
        }
    }

    // -----------------------------------------------------------------------
    // Proof logging (DRUP)
    // -----------------------------------------------------------------------

    /// Enable DRUP proof logging. Must be called before `solve()`.
    pub fn enable_proof_logging(&mut self) {
        self.proof_log = Some(Vec::new());
    }

    /// Consume and return the proof log (DRUP format).
    pub fn take_proof_log(&mut self) -> Option<Vec<Vec<i32>>> {
        self.proof_log.take()
    }

    fn lits_to_dimacs(lits: &[Literal]) -> Vec<i32> {
        lits.iter()
            .map(|l| {
                let v = l.var() as i32;
                if l.is_positive() { v } else { -v }
            })
            .collect()
    }

    fn log_proof_clause(&mut self, lits: &[Literal]) {
        if let Some(log) = &mut self.proof_log {
            log.push(Self::lits_to_dimacs(lits));
        }
    }

    fn log_proof_empty(&mut self) {
        if let Some(log) = &mut self.proof_log {
            log.push(Vec::new());
        }
    }

    // -----------------------------------------------------------------------
    // Clause addition
    // -----------------------------------------------------------------------

    /// Add a problem clause. Unit clauses are enqueued immediately at level 0.
    /// Binary clauses go to the binary implication table (fast BCP path) and
    /// the clause DB (reason tracking), but NOT the watch list.
    pub fn add_clause(&mut self, lits: &[Literal]) {
        match lits.len() {
            0 => {
                self.db.set_empty_clause();
            }
            1 => {
                let lit = lits[0];
                match self.assignment.literal_value(lit) {
                    Value::True => {}
                    Value::False => {
                        self.db.set_empty_clause();
                    }
                    Value::Undef => {
                        self.assignment.assign(lit, 0, ClauseRef::DECISION.0);
                    }
                }
            }
            2 => {
                // Binary: arena for reason tracking, binary table for BCP, skip watch list.
                let cr = self.db.add(lits, false, 0);
                self.binaries[lits[0].negate().raw() as usize].push((lits[1], cr.0));
                self.binaries[lits[1].negate().raw() as usize].push((lits[0], cr.0));
                // Handle the case where one literal is already False (unit at current level).
                // This matters when adding theory lemmas after the triggering literal has
                // already been fully propagated — the new binary would otherwise be silently
                // ignored, causing an infinite loop in the CDCL(T) outer loop.
                let v0 = self.assignment.literal_value(lits[0]);
                let v1 = self.assignment.literal_value(lits[1]);
                match (v0, v1) {
                    (Value::False, Value::False) => { self.db.set_empty_clause(); }
                    (Value::False, Value::Undef) => {
                        let lvl = self.assignment.current_level();
                        self.assignment.assign(lits[1], lvl, cr.0);
                    }
                    (Value::Undef, Value::False) => {
                        let lvl = self.assignment.current_level();
                        self.assignment.assign(lits[0], lvl, cr.0);
                    }
                    _ => {}
                }
            }
            _ => {
                // Reorder literals so positions 0 and 1 are the two best watch
                // candidates (non-False first). propagate() assumes lits[0] and
                // lits[1] are the watched positions — if a False literal were at
                // position 0 or 1 from the start, propagate()'s "other = lits[0]"
                // check would read the wrong literal and corrupt the watch state.
                let mut ordered: smallvec::SmallVec<[Literal; 8]> =
                    smallvec::SmallVec::from_slice(lits);
                let mut front = 0usize;
                for i in 0..ordered.len() {
                    if self.assignment.literal_value(ordered[i]) != Value::False {
                        ordered.swap(front, i);
                        front += 1;
                        if front == 2 {
                            break;
                        }
                    }
                }
                // front = number of non-False literals found (0, 1, or 2).
                let false_count = lits.len() - {
                    lits.iter()
                        .filter(|&&l| self.assignment.literal_value(l) != Value::False)
                        .count()
                };
                let lvl = self.assignment.current_level();
                if false_count == lits.len() {
                    // All literals are False: immediate conflict.
                    self.db.set_empty_clause();
                    return;
                }
                let cr = self.db.add(&ordered, false, 0);
                if false_count == lits.len() - 1 {
                    // All-but-one: unit propagation (ordered[0] is the non-False one).
                    let unit = ordered[0];
                    if self.assignment.literal_value(unit) == Value::Undef {
                        self.assignment.assign(unit, lvl, cr.0);
                    }
                }
                // Standard 2-watch setup: lits[0] and lits[1] are guaranteed
                // non-False (or there are < 2 non-False, in which case the conflict
                // case above already returned).
                self.watches.watch(ordered[0].negate(), cr, ordered[1]);
                self.watches.watch(ordered[1].negate(), cr, ordered[0]);
            }
        }
    }

    // -----------------------------------------------------------------------
    // Main solve loop
    // -----------------------------------------------------------------------

    /// Solve under optional additional `assumptions`. Returns after at most
    /// `max_conflicts` conflicts (use `u64::MAX` for unlimited).
    pub fn solve(&mut self, assumptions: &[Literal], max_conflicts: u64) -> SolveResult {
        self.solve_inner(assumptions, max_conflicts, None)
    }

    /// DPLL(T) solve: interleave SAT search with a theory solver.
    ///
    /// After each BCP fixed point, calls `theory.theory_propagate(level, trail, prev)`.
    /// Returned lemmas are added as clauses; a returned conflict triggers backtracking.
    /// The theory is notified before every backtrack via `theory.theory_backtrack`.
    ///
    /// Does not use SAT assumptions (base_level = 0).
    pub fn solve_with_theory(
        &mut self,
        max_conflicts: u64,
        theory: &mut dyn TheorySolver,
    ) -> SolveResult {
        if self.db.has_empty_clause() {
            self.log_proof_empty();
            return SolveResult::Unsat;
        }

        if !self.bve_done && self.assignment.current_level() == 0 && self.conflicts == 0 {
            self.run_bve();
            if self.db.has_empty_clause() {
                return SolveResult::Unsat;
            }
        }

        if !self.xor_init_done {
            self.xor_init_done = true;
            self.init_xor_reasoning();
        }

        self.base_level = 0;
        self.assumption_floor = 0;

        if self.settle_root_propagations() {
            self.log_proof_empty();
            self.backtrack_and_reschedule(0);
            return SolveResult::Unsat;
        }

        // Initial theory call at level 0 before any decisions.
        {
            let trail_snap: Vec<Literal> = self.assignment.trail().to_vec();
            match theory.theory_propagate(0, &trail_snap, 0) {
                Err(conflict) => {
                    self.add_clause(&conflict);
                }
                Ok(lemmas) => {
                    for lemma in lemmas {
                        self.add_clause(&lemma);
                    }
                }
            }
        }

        let conflicts_at_entry = self.conflicts;
        let mut prev_trail_len = self.assignment.trail().len();

        let result = loop {
            if self.db.has_empty_clause() {
                self.log_proof_empty();
                break SolveResult::Unsat;
            }

            if let Some(conflict_cr) = self.propagate() {
                // ---- SAT conflict ----
                if self.assignment.current_level() == self.base_level {
                    self.log_proof_empty();
                    break SolveResult::Unsat;
                }
                self.conflicts += 1;

                let current_level = self.assignment.current_level();
                let (learnt, mut backjump_level) = self.analyze(conflict_cr);
                if backjump_level < self.assumption_floor {
                    backjump_level = self.assumption_floor;
                }

                let effective = if current_level > backjump_level + CHRONO_BT_MIN_GAP
                    && current_level.saturating_sub(1) >= self.assumption_floor
                {
                    self.chrono_bts += 1;
                    current_level - 1
                } else {
                    backjump_level
                };

                // Theory backtrack before SAT backtrack.
                theory.theory_backtrack(effective);
                self.backtrack_and_reschedule(effective);
                self.decay_activities();
                prev_trail_len = self.assignment.trail().len();

                match self.assignment.literal_value(learnt[0]) {
                    Value::True => {}
                    Value::False => {
                        self.log_proof_empty();
                        break SolveResult::Unsat;
                    }
                    Value::Undef => {
                        self.log_proof_clause(&learnt);
                        if learnt.len() == 1 {
                            self.learned_outbox.push((learnt.to_vec(), 1));
                            self.assignment.assign(
                                learnt[0],
                                effective,
                                ClauseRef::DECISION.0,
                            );
                        } else {
                            let cr = self.add_learned_clause(&learnt);
                            self.assignment.assign(learnt[0], effective, cr.0);
                        }
                    }
                }

                // Restart if scheduled — notify theory first.
                if self.should_restart() {
                    theory.theory_backtrack(self.base_level);
                    self.do_restart();
                    prev_trail_len = self.assignment.trail().len();
                }
                self.maybe_reduce_db();

            } else {
                // ---- BCP fixed point — query theory ----
                let level = self.assignment.current_level();
                let trail_snap: Vec<Literal> = self.assignment.trail().to_vec();
                let snap_len = trail_snap.len();

                match theory.theory_propagate(level, &trail_snap, prev_trail_len) {
                    Err(conflict) => {
                        // Theory conflict: backjump to the second-highest literal level
                        // so the highest-level literal becomes UNDEF and the conflict
                        // clause is unit after backjump.
                        //
                        // Critical: when all conflict literals are at the same level
                        // (second_lv == max_lv), second_lv is NOT below max_lv, so
                        // add_clause would receive an all-false clause → set_empty_clause
                        // → false UNSAT. We cap at max_lv-1 to force at least one UNDEF.
                        self.conflicts += 1;
                        let cur_level = self.assignment.current_level();
                        let backjump_level = if cur_level > self.base_level
                            && !conflict.is_empty()
                        {
                            let mut max_lv = self.base_level;
                            let mut second_lv = self.base_level;
                            for &lit in &conflict {
                                let lv = self.assignment.level_of(lit.var());
                                if lv >= max_lv {
                                    second_lv = max_lv;
                                    max_lv = lv;
                                } else if lv > second_lv {
                                    second_lv = lv;
                                }
                            }
                            // Cap at max_lv-1: ensures backjump is strictly below the
                            // highest conflict level so that literal becomes UNDEF.
                            second_lv.min(max_lv.saturating_sub(1)).max(self.base_level)
                        } else {
                            self.base_level
                        };
                        if cur_level > backjump_level {
                            theory.theory_backtrack(backjump_level);
                            self.backtrack_and_reschedule(backjump_level);
                            self.decay_activities();
                            prev_trail_len = self.assignment.trail().len();
                            self.maybe_reduce_db();
                        }
                        // Add the (now unit or partially-assigned) conflict clause.
                        // Do NOT update prev_trail_len here: the literal forced by
                        // add_clause (the UIP) must be seen by the next theory_propagate.
                        self.add_clause(&conflict);
                    }
                    Ok(lemmas) => {
                        prev_trail_len = snap_len;
                        if lemmas.is_empty() {
                            // No new theory information — branch or finish.
                            let trail_before = self.assignment.trail().len();
                            if let Some(r) = self.branch_or_finish() {
                                // Full model found — do a final theory consistency check
                                // before accepting the SAT result. theory_propagate is
                                // incremental and may miss inconsistencies when level sync
                                // causes some atoms to not be re-asserted after backjumps.
                                if let SolveResult::Sat(ref model) = r {
                                    if let Some(conflict) = theory.theory_final_check(model) {
                                        // Theory rejected the model — backjump first so the
                                        // conflict clause is not all-False (which would set
                                        // the empty clause and return false UNSAT), then add
                                        // the clause and continue search.
                                        //
                                        // When TFC preserves incremental state (e.g. LiaCdclT
                                        // uses a fresh clone), backjump to the UIP level so the
                                        // theory state at that level remains valid.
                                        //
                                        // When TFC resets incremental state (e.g. CdclT's
                                        // theory_check wipes CC to a scratch level), backjump
                                        // to base level so theory_propagate can rebuild state
                                        // from scratch without inheriting stale CC merges.
                                        self.conflicts += 1;
                                        let cur_level = self.assignment.current_level();
                                        let backjump_level =
                                            if theory.theory_final_check_preserves_state()
                                                && cur_level > self.base_level
                                                && !conflict.is_empty()
                                            {
                                                let mut max_lv = self.base_level;
                                                let mut second_lv = self.base_level;
                                                for &lit in &conflict {
                                                    let lv = self.assignment.level_of(lit.var());
                                                    if lv >= max_lv {
                                                        second_lv = max_lv;
                                                        max_lv = lv;
                                                    } else if lv > second_lv {
                                                        second_lv = lv;
                                                    }
                                                }
                                                second_lv
                                                    .min(max_lv.saturating_sub(1))
                                                    .max(self.base_level)
                                            } else {
                                                self.base_level
                                            };
                                        if cur_level > backjump_level {
                                            theory.theory_backtrack(backjump_level);
                                            self.backtrack_and_reschedule(backjump_level);
                                            self.decay_activities();
                                            prev_trail_len = self.assignment.trail().len();
                                            self.maybe_reduce_db();
                                        }
                                        self.add_clause(&conflict);
                                        // Allow the Luby/EMA restart schedule to fire after
                                        // TFC conflicts. Without this, rapid TFC chains
                                        // starve restarts: learned clauses never become unit
                                        // at level 0, blocking UNSAT derivation on hard
                                        // problems.
                                        if self.should_restart() {
                                            theory.theory_backtrack(self.base_level);
                                            self.do_restart();
                                            prev_trail_len = self.assignment.trail().len();
                                        }
                                    } else {
                                        break r;
                                    }
                                } else {
                                    break r;
                                }
                            }
                            // Detect restart inside branch_or_finish.
                            if self.assignment.trail().len() < trail_before {
                                theory.theory_backtrack(self.base_level);
                                prev_trail_len = self.assignment.trail().len();
                            }
                        } else {
                            // Add theory lemmas and re-run BCP before branching.
                            for lemma in lemmas {
                                self.add_clause(&lemma);
                            }
                        }
                    }
                }
            }

            if self.conflicts - conflicts_at_entry > max_conflicts {
                break SolveResult::BudgetExceeded;
            }
        };

        theory.theory_backtrack(self.base_level);
        self.backtrack_and_reschedule(self.base_level);
        result
    }

    /// Solve bounded by both a conflict budget and a wall-clock deadline.
    pub fn solve_with_deadline(
        &mut self,
        assumptions: &[Literal],
        max_conflicts: u64,
        deadline: Option<Instant>,
    ) -> SolveResult {
        self.solve_inner(assumptions, max_conflicts, deadline)
    }

    // -----------------------------------------------------------------------
    // Lookahead / cube-and-conquer helpers (public API used by lookahead.rs)
    // -----------------------------------------------------------------------

    /// Whether variable `var` is currently assigned (true or false).
    #[inline]
    pub fn is_var_assigned(&self, var: Var) -> bool {
        self.assignment.is_assigned(var)
    }

    /// Propagate any pending level-0 unit assignments.  Returns `true` if a
    /// contradiction was found (formula is UNSAT at root).  Must be called at
    /// level 0 only.
    pub fn propagate_units(&mut self) -> bool {
        debug_assert_eq!(self.assignment.current_level(), 0);
        self.propagate().is_some()
    }

    /// Probe `var = phase` via unit propagation and measure how many additional
    /// literals are forced.  Returns `u32::MAX` when the probe leads to a
    /// conflict (failed literal).  The solver state is fully restored after the
    /// call.  Must be called at `base_level` (level 0 on a fresh solver).
    pub fn probe_var(&mut self, var: Var, phase: bool) -> u32 {
        debug_assert!(!self.assignment.is_assigned(var), "probe_var called on assigned var");
        let lit = if phase {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        };
        let before = self.assignment.num_assigned();
        self.assignment.new_decision_level();
        self.assignment
            .assign(lit, self.assignment.current_level(), ClauseRef::DECISION.0);
        if self.propagate().is_some() {
            self.backtrack_and_reschedule(self.base_level);
            u32::MAX
        } else {
            let forced = (self.assignment.num_assigned() - before - 1) as u32;
            self.backtrack_and_reschedule(self.base_level);
            forced
        }
    }

    /// Check whether the formula is consistent under `assumptions` via BCP only
    /// (no branching).  Returns `true` if no contradiction is found.  The
    /// solver state is fully restored after the call.
    pub fn is_feasible_under_assumptions(&mut self, assumptions: &[Literal]) -> bool {
        let saved_level = self.assignment.current_level();
        for &lit in assumptions {
            match self.assignment.literal_value(lit) {
                Value::True => {}
                Value::False => {
                    self.backtrack_and_reschedule(saved_level);
                    return false;
                }
                Value::Undef => {
                    self.assignment.new_decision_level();
                    self.assignment.assign(
                        lit,
                        self.assignment.current_level(),
                        ClauseRef::DECISION.0,
                    );
                }
            }
        }
        let ok = self.propagate().is_none();
        self.backtrack_and_reschedule(saved_level);
        ok
    }

    fn solve_inner(
        &mut self,
        assumptions: &[Literal],
        max_conflicts: u64,
        deadline: Option<Instant>,
    ) -> SolveResult {
        if self.db.has_empty_clause() {
            self.log_proof_empty();
            return SolveResult::Unsat;
        }

        // BVE preprocessing on the very first solve call (no assumptions, level 0).
        // bve_done is set inside run_bve so this fires at most once per solver.
        if !self.bve_done
            && assumptions.is_empty()
            && self.assignment.current_level() == 0
            && self.conflicts == 0
        {
            self.run_bve();
            if self.db.has_empty_clause() {
                return SolveResult::Unsat;
            }
        }

        // XOR/parity reasoning: scan the clause DB once (after BVE) for XOR patterns.
        if !self.xor_init_done {
            self.xor_init_done = true;
            self.init_xor_reasoning();
        }

        self.base_level = if assumptions.is_empty() {
            0
        } else {
            self.assignment.current_level()
        };

        if self.base_level == 0 && self.settle_root_propagations() {
            self.log_proof_empty();
            self.backtrack_and_reschedule(0);
            return SolveResult::Unsat;
        }

        if let Some(r) = self.push_assumptions_onto_trail(assumptions) {
            return r;
        }

        let conflicts_at_entry = self.conflicts;
        let result = loop {
            // Inprocessing (failed literal probing) may discover UNSAT
            // without going through the normal conflict path.
            if self.db.has_empty_clause() {
                self.log_proof_empty();
                break SolveResult::Unsat;
            }

            if let Some(conflict_cr) = self.propagate() {
                if let Some(r) = self.process_conflict_in_loop(conflict_cr) {
                    break r;
                }
            } else if !self.xor_clauses.is_empty() {
                let trail_before = self.assignment.trail().len();
                if let Some(conflict_cr) = self.xor_propagate() {
                    if let Some(r) = self.process_conflict_in_loop(conflict_cr) {
                        break r;
                    }
                } else if self.assignment.trail().len() == trail_before {
                    // Neither BCP nor XOR made progress — safe to branch.
                    if let Some(r) = self.branch_or_finish() {
                        break r;
                    }
                }
                // If XOR added trail entries, loop back to BCP before branching.
            } else if let Some(r) = self.branch_or_finish() {
                break r;
            }

            if self.conflicts - conflicts_at_entry > max_conflicts {
                break SolveResult::BudgetExceeded;
            }
            if deadline.is_some_and(|d| Instant::now() >= d) {
                break SolveResult::Unknown;
            }
        };

        self.backtrack_and_reschedule(self.base_level);
        result
    }

    fn settle_root_propagations(&mut self) -> bool {
        self.propagate().is_some()
    }

    fn push_assumptions_onto_trail(&mut self, assumptions: &[Literal]) -> Option<SolveResult> {
        let mut pushed = 0u32;
        for &lit in assumptions {
            match self.assignment.literal_value(lit) {
                Value::True => {}
                Value::False => {
                    self.log_proof_empty();
                    self.backtrack_and_reschedule(self.base_level);
                    return Some(SolveResult::Unsat);
                }
                Value::Undef => {
                    self.assignment.new_decision_level();
                    self.assignment.assign(
                        lit,
                        self.assignment.current_level(),
                        ClauseRef::DECISION.0,
                    );
                    self.decisions += 1;
                    pushed += 1;
                }
            }
        }
        self.assumption_floor = if pushed > 0 {
            self.base_level + pushed
        } else {
            self.base_level
        };
        None
    }

    fn process_conflict_in_loop(&mut self, conflict_cr: ClauseRef) -> Option<SolveResult> {
        if self.assignment.current_level() == self.base_level {
            self.log_proof_empty();
            return Some(SolveResult::Unsat);
        }
        self.conflicts += 1;

        let current_level = self.assignment.current_level();
        let (learnt, mut backjump_level) = self.analyze(conflict_cr);
        if backjump_level < self.assumption_floor {
            backjump_level = self.assumption_floor;
        }

        // S1-7: Chronological backtracking (conservative one-level variant).
        let effective_backjump =
            if current_level > backjump_level + CHRONO_BT_MIN_GAP
                && current_level.saturating_sub(1) >= self.assumption_floor
            {
                self.chrono_bts += 1;
                current_level - 1
            } else {
                backjump_level
            };

        self.backtrack_and_reschedule(effective_backjump);
        self.decay_activities();

        match self.assignment.literal_value(learnt[0]) {
            Value::True => {}
            Value::False => {
                self.log_proof_empty();
                return Some(SolveResult::Unsat);
            }
            Value::Undef => {
                self.log_proof_clause(&learnt);
                if learnt.len() == 1 {
                    self.learned_outbox.push((learnt.to_vec(), 1));
                    self.assignment
                        .assign(learnt[0], effective_backjump, ClauseRef::DECISION.0);
                } else {
                    let cr = self.add_learned_clause(&learnt);
                    self.assignment.assign(learnt[0], effective_backjump, cr.0);
                }
            }
        }
        self.maybe_restart();
        self.maybe_reduce_db();
        None
    }

    fn branch_or_finish(&mut self) -> Option<SolveResult> {
        if self.should_restart() {
            self.do_restart();
            return None;
        }
        if let Some(lit) = self.pick_branch() {
            self.assignment.new_decision_level();
            self.assignment
                .assign(lit, self.assignment.current_level(), ClauseRef::DECISION.0);
            self.decisions += 1;
            None
        } else {
            Some(SolveResult::Sat(self.extract_model()))
        }
    }

    /// Import a batch of learned clauses (e.g. from AKX) into the clause database.
    pub fn import_clauses(&mut self, clauses: &[Vec<Literal>]) -> usize {
        self.backtrack_and_reschedule(0);
        self.base_level = 0;
        for lits in clauses {
            self.add_clause(lits);
        }
        clauses.len()
    }

    /// Expose arena for inprocessing passes (vivification etc.).
    pub fn arena(&self) -> &ClauseArena {
        &self.db
    }

    pub fn arena_mut(&mut self) -> &mut ClauseArena {
        &mut self.db
    }

    // -----------------------------------------------------------------------
    // Boolean Constraint Propagation
    // -----------------------------------------------------------------------

    /// Run BCP to a fixed point. Returns the conflicting ClauseRef, if any.
    ///
    /// For each newly-True literal `p`:
    ///   1. Binary fast path: iterate `binaries[p.raw()]` in a tight loop.
    ///   2. Regular watch list: process 3+ literal clauses as before.
    fn propagate(&mut self) -> Option<ClauseRef> {
        while self.assignment.prop_head < self.assignment.trail().len() {
            let p = self.assignment.trail()[self.assignment.prop_head];
            self.assignment.prop_head += 1;
            self.propagations += 1;

            // Binary clause fast path.
            let p_raw = p.raw() as usize;
            let n_bin = self.binaries[p_raw].len();
            self.bcp_binary_checks += n_bin as u64;
            for bi in 0..n_bin {
                // SAFETY: bi < n_bin = self.binaries[p_raw].len()
                let (impl_lit, reason_raw) = unsafe { *self.binaries[p_raw].get_unchecked(bi) };
                match self.assignment.literal_value(impl_lit) {
                    Value::True => {}
                    Value::Undef => {
                        let lvl = self.assignment.current_level();
                        self.assignment.assign(impl_lit, lvl, reason_raw);
                    }
                    Value::False => {
                        return Some(ClauseRef(reason_raw));
                    }
                }
            }

            // Regular watch list (3+ literal clauses).
            let mut wlist = std::mem::take(self.watches.get_mut(p));
            let n = wlist.len();
            self.bcp_watch_visits += n as u64;
            let (mut i, mut j) = (0usize, 0usize);
            let mut conflict = None;

            while i < n {
                let (cr, blocker) = wlist[i];
                i += 1;

                // Lazy deleted-clause cleanup: drop the watch entry silently.
                if self.db.is_deleted(cr) {
                    continue;
                }

                // Blocker fast path: if the other watched literal is already True,
                // the clause is satisfied — skip the arena fetch entirely.
                // Blockers may be stale, but a stale True blocker still implies
                // the literal is in the clause and is True, so skipping is safe.
                if self.assignment.literal_value(blocker) == Value::True {
                    self.bcp_blocker_hits += 1;
                    wlist[j] = (cr, blocker);
                    j += 1;
                    continue;
                }

                // Fell through: must load the clause from the arena.
                self.bcp_clause_fetches += 1;

                // Ensure lits[1] is the watch that just became False (p = lits[1].negate()).
                if self.db.lit_at(cr, 0).negate() == p {
                    self.db.swap_lits(cr, 0, 1);
                }
                let other = self.db.lit_at(cr, 0);

                // Other watch is True: clause satisfied; refresh the blocker.
                if self.assignment.literal_value(other) == Value::True {
                    wlist[j] = (cr, other);
                    j += 1;
                    continue;
                }

                // Search for a new non-false literal to watch.
                let clause_len = self.db.clause_len(cr);
                let mut found_new = false;
                for k in 2..clause_len {
                    let cand = self.db.lit_at(cr, k);
                    if self.assignment.literal_value(cand) != Value::False {
                        self.db.swap_lits(cr, 1, k);
                        let new_watch_lit = self.db.lit_at(cr, 1);
                        self.watches.watch(new_watch_lit.negate(), cr, other);
                        found_new = true;
                        break;
                    }
                }
                if found_new {
                    self.bcp_new_watch += 1;
                    continue;
                }

                // No new watch: clause is unit or conflicting.
                wlist[j] = (cr, other);
                j += 1;

                match self.assignment.literal_value(other) {
                    Value::Undef => {
                        self.bcp_unit_props += 1;
                        self.assignment
                            .assign(other, self.assignment.current_level(), cr.0);
                    }
                    Value::False => {
                        self.bcp_conflicts += 1;
                        while i < n {
                            wlist[j] = wlist[i];
                            j += 1;
                            i += 1;
                        }
                        conflict = Some(cr);
                        break;
                    }
                    Value::True => unreachable!("handled above"),
                }
            }

            wlist.truncate(j);
            *self.watches.get_mut(p) = wlist;

            if let Some(cr) = conflict {
                return Some(cr);
            }
        }
        None
    }

    // -----------------------------------------------------------------------
    // 1-UIP Conflict Analysis
    // -----------------------------------------------------------------------

    /// Analyse `conflict_cr` and return (learnt_clause, backjump_level).
    fn analyze(&mut self, conflict_cr: ClauseRef) -> (SmallVec<[Literal; 16]>, u32) {
        let current_level = self.assignment.current_level();

        self.analyze_stamp = self.analyze_stamp.wrapping_add(1);
        if self.analyze_stamp == 0 {
            self.seen_stamp.iter_mut().for_each(|s| *s = 0);
            self.analyze_stamp = 1;
        }
        let stamp = self.analyze_stamp;

        let mut learnt: SmallVec<[Literal; 16]> = SmallVec::new();
        let mut counter = 0usize;

        self.process_reason_into(
            conflict_cr,
            current_level,
            stamp,
            &mut learnt,
            &mut counter,
            None,
        );

        let mut trail_snapshot = std::mem::take(&mut self.trail_buf);
        trail_snapshot.clear();
        trail_snapshot.extend_from_slice(self.assignment.trail());

        let uip = self.find_uip_on_trail(
            &trail_snapshot,
            current_level,
            stamp,
            &mut learnt,
            &mut counter,
        );
        self.trail_buf = trail_snapshot;

        let (mut clause, backjump_level) = self.build_learned_clause(uip, learnt);

        self.minimize_learned_clause(&mut clause, stamp);

        (clause, backjump_level)
    }

    fn find_uip_on_trail(
        &mut self,
        trail: &[Literal],
        current_level: u32,
        stamp: u32,
        learnt: &mut SmallVec<[Literal; 16]>,
        counter: &mut usize,
    ) -> Literal {
        let mut trail_pos = trail.len();
        loop {
            loop {
                debug_assert!(trail_pos > 0, "1-UIP analysis walked past trail start");
                trail_pos -= 1;
                if self.seen_stamp[trail[trail_pos].var() as usize] == stamp {
                    break;
                }
            }

            let lit = trail[trail_pos];
            let var = lit.var();
            self.seen_stamp[var as usize] = 0;

            if self.assignment.level_of(var) != current_level {
                continue;
            }

            *counter -= 1;
            if *counter == 0 {
                return lit;
            }

            let reason_raw = self.assignment.reason_of(var);
            let reason_cr = ClauseRef(reason_raw);
            if !reason_cr.is_sentinel() {
                self.process_reason_into(
                    reason_cr,
                    current_level,
                    stamp,
                    learnt,
                    counter,
                    Some(var),
                );
            }
        }
    }

    fn build_learned_clause(
        &self,
        uip: Literal,
        mut learnt: SmallVec<[Literal; 16]>,
    ) -> (SmallVec<[Literal; 16]>, u32) {
        let asserting = uip.negate();
        let backjump_level = if learnt.is_empty() {
            0
        } else {
            let (max_idx, max_lvl) = learnt
                .iter()
                .enumerate()
                .map(|(i, l)| (i, self.assignment.level_of(l.var())))
                .max_by_key(|&(_, lvl)| lvl)
                .unwrap();
            learnt.swap(0, max_idx);
            max_lvl
        };

        let mut clause: SmallVec<[Literal; 16]> = SmallVec::new();
        clause.push(asserting);
        clause.extend_from_slice(&learnt);
        (clause, backjump_level)
    }

    fn process_reason_into(
        &mut self,
        cr: ClauseRef,
        current_level: u32,
        stamp: u32,
        learnt: &mut SmallVec<[Literal; 16]>,
        counter: &mut usize,
        resolving_var: Option<Var>,
    ) {
        // Bump clause activity and mark as recently used for clause deletion.
        self.db.bump_activity(cr, self.clause_inc);
        if self.db.is_learnt(cr) {
            self.db.mark_used(cr);
            // Lower the stored LBD if the clause's effective LBD has dropped
            // (some levels have since collapsed), promoting tier-3 → tier-2.
            if self.db.lbd(cr) > 2 {
                let lits: SmallVec<[Literal; 16]> = self.db.lits(cr).iter().copied().collect();
                let new_lbd = self.compute_lbd(&lits);
                if new_lbd < self.db.lbd(cr) {
                    self.db.set_lbd(cr, new_lbd);
                }
            }
        }

        // Collect the literals into a local SmallVec to release the &self.db borrow
        // before calling bump_var_activity (which needs &mut self).
        let lits: SmallVec<[Literal; 16]> = self.db.lits(cr).iter().copied().collect();
        for &lit in &lits {
            let var = lit.var();
            if Some(var) == resolving_var || self.seen_stamp[var as usize] == stamp {
                continue;
            }
            let lvl = self.assignment.level_of(var);
            if lvl == 0 {
                continue;
            }
            self.seen_stamp[var as usize] = stamp;
            self.bump_var_activity(var);
            if lvl == current_level {
                *counter += 1;
            } else {
                learnt.push(lit);
            }
        }
    }

    // -----------------------------------------------------------------------
    // Recursive learned-clause minimization
    // -----------------------------------------------------------------------

    /// Remove redundant literals from a learned clause using recursive DFS up
    /// the reason graph. A literal is redundant if every variable in its reason
    /// chain is either at level 0, already in the frontier (seen_stamp), or
    /// itself redundant. A cumulative work counter caps the total effort.
    fn minimize_learned_clause(&mut self, learnt: &mut SmallVec<[Literal; 16]>, stamp: u32) {
        if learnt.len() <= 1 {
            return;
        }
        let mut work = 0u32;
        let mut i = 1; // index 0 is the UIP; never removed
        while i < learnt.len() {
            let var = learnt[i].var();
            if self.literal_redundant(var, stamp, &mut work) {
                learnt.swap_remove(i);
            } else {
                i += 1;
            }
        }
    }

    fn literal_redundant(&self, var: Var, stamp: u32, work: &mut u32) -> bool {
        const MAX_WORK: u32 = 500;
        let reason_cr = ClauseRef(self.assignment.reason_of(var));
        if reason_cr.is_sentinel() {
            return false;
        }
        let n = self.db.clause_len(reason_cr);
        *work = work.saturating_add(n as u32);
        if *work > MAX_WORK {
            return false;
        }
        for i in 0..n {
            let rv = self.db.lit_at(reason_cr, i).var();
            if rv == var {
                continue;
            }
            if self.assignment.level_of(rv) == 0 {
                continue;
            }
            if self.seen_stamp[rv as usize] == stamp {
                continue;
            }
            if !self.literal_redundant(rv, stamp, work) {
                return false;
            }
        }
        true
    }

    // -----------------------------------------------------------------------
    // Learned clause management
    // -----------------------------------------------------------------------

    fn add_learned_clause(&mut self, lits: &[Literal]) -> ClauseRef {
        debug_assert!(lits.len() >= 2);
        let lbd = self.compute_lbd(lits);

        // Update Glucose-style LBD EMAs for adaptive restart decisions.
        let lf = lbd as f64;
        self.lbd_fast_ema = 0.03 * lf + 0.97 * self.lbd_fast_ema;
        self.lbd_slow_ema = 0.00001 * lf + 0.99999 * self.lbd_slow_ema;

        let cr = self.db.add(lits, true, lbd);

        if lits.len() == 2 {
            // Binary learned clause: fast-path table only, not the watch list.
            self.binaries[lits[0].negate().raw() as usize].push((lits[1], cr.0));
            self.binaries[lits[1].negate().raw() as usize].push((lits[0], cr.0));
        } else {
            self.watches.watch(lits[0].negate(), cr, lits[1]);
            self.watches.watch(lits[1].negate(), cr, lits[0]);
        }
        self.learned_outbox.push((lits.to_vec(), lbd));
        cr
    }

    /// Drain the learned clauses produced since the last call. Used by the
    /// Reasoner to build exportable AKX clause knowledge.
    pub fn drain_learned(&mut self) -> Vec<(Vec<Literal>, u32)> {
        std::mem::take(&mut self.learned_outbox)
    }

    // -----------------------------------------------------------------------
    // XOR / parity reasoning
    // -----------------------------------------------------------------------

    /// Scan the clause DB for k=2 and k=3 XOR-encoded clause groups and store
    /// them in `self.xor_clauses`. Called once after BVE.
    fn init_xor_reasoning(&mut self) {
        use std::collections::{HashMap, HashSet};

        // Deduplicate clauses before grouping.  BVE can add resolvent clauses
        // that coincide with existing problem clauses; counting a duplicate
        // twice would produce a false 4-tuple for k=3 (or false pair for k=2),
        // leading to an unsound XOR constraint and wrong UNSAT results.
        let mut seen: HashSet<SmallVec<[u32; 4]>> = HashSet::new();
        let mut groups: HashMap<SmallVec<[u32; 4]>, SmallVec<[bool; 8]>> = HashMap::new();

        self.db.for_each_clause(2, |_cr, _lbd, learnt, lits| {
            if learnt || lits.len() > 3 {
                return;
            }
            // Canonical form: sort raw literal values so differently-ordered
            // copies of the same clause hash identically.
            let mut canon: SmallVec<[u32; 4]> = lits.iter().map(|l| l.raw()).collect();
            canon.sort_unstable();
            if !seen.insert(canon) {
                return; // skip duplicate
            }

            let mut vars: SmallVec<[u32; 4]> = lits.iter().map(|l| l.var()).collect();
            vars.sort_unstable();
            if vars.windows(2).any(|w| w[0] == w[1]) {
                return;
            }
            let neg_parity = lits.iter().filter(|l| !l.is_positive()).count() % 2 == 1;
            groups.entry(vars).or_default().push(neg_parity);
        });

        for (vars, parities) in groups {
            let k = vars.len();
            let expected = 1usize << (k - 1); // 2 for k=2, 4 for k=3
            if parities.len() != expected {
                continue;
            }
            let first = parities[0];
            if !parities.iter().all(|&p| p == first) {
                continue;
            }
            self.xor_clauses.push(XorClause {
                vars: smallvec::SmallVec::from_slice(&vars),
                rhs: !first,
            });
        }
    }

    /// One pass of XOR unit propagation. Returns a conflict ClauseRef if any
    /// XOR constraint is violated. Assignments forced by unit XOR constraints
    /// are added to the trail; the caller should loop back to BCP afterward.
    fn xor_propagate(&mut self) -> Option<ClauseRef> {
        for i in 0..self.xor_clauses.len() {
            let mut free_var: Option<u32> = None;
            let mut partial_xor = self.xor_clauses[i].rhs;
            let mut n_free = 0usize;

            let n_vars = self.xor_clauses[i].vars.len();
            for j in 0..n_vars {
                let v = self.xor_clauses[i].vars[j];
                match self.assignment.value_of(v) {
                    Value::True => partial_xor ^= true,
                    Value::False => {}
                    Value::Undef => {
                        n_free += 1;
                        if n_free == 1 {
                            free_var = Some(v);
                        }
                    }
                }
            }

            if n_free == 0 {
                // All assigned: partial_xor != false means XOR constraint violated.
                if partial_xor {
                    return Some(self.make_xor_conflict_clause(i));
                }
            } else if n_free == 1 {
                let fv = free_var.unwrap();
                // fv must be set to partial_xor to satisfy the XOR constraint.
                let forced_lit = if partial_xor {
                    Literal::positive(fv)
                } else {
                    Literal::negative(fv)
                };
                match self.assignment.literal_value(forced_lit) {
                    Value::True => {}
                    Value::False => {
                        return Some(self.make_xor_conflict_clause(i));
                    }
                    Value::Undef => {
                        let cr = self.make_xor_reason_clause(i, forced_lit);
                        let lvl = self.assignment.current_level();
                        self.assignment.assign(forced_lit, lvl, cr.0);
                        self.propagations += 1;
                    }
                }
            }
        }
        None
    }

    /// Build the reason clause for an XOR-forced literal and add it to the DB.
    /// Format: [forced_lit, neg(v1_assigned), neg(v2_assigned), ...] — the
    /// forced literal is at position 0; all other literals are currently False.
    fn make_xor_reason_clause(&mut self, xor_idx: usize, forced_lit: Literal) -> ClauseRef {
        let forced_var = forced_lit.var();
        let n = self.xor_clauses[xor_idx].vars.len();

        let mut clause: SmallVec<[Literal; 8]> = SmallVec::new();
        clause.push(forced_lit);
        for j in 0..n {
            let v = self.xor_clauses[xor_idx].vars[j];
            if v == forced_var {
                continue;
            }
            let lit = match self.assignment.value_of(v) {
                Value::True => Literal::negative(v),
                Value::False => Literal::positive(v),
                Value::Undef => unreachable!("non-forced XOR vars must be assigned"),
            };
            clause.push(lit);
        }
        self.add_xor_explanation(&clause)
    }

    /// Build the conflict clause for a violated XOR constraint and add it to
    /// the DB. All literals in the clause are currently False. The literal at
    /// the highest decision level is placed first so `analyze` picks the right
    /// UIP.
    fn make_xor_conflict_clause(&mut self, xor_idx: usize) -> ClauseRef {
        let n = self.xor_clauses[xor_idx].vars.len();
        let mut clause: SmallVec<[Literal; 8]> = SmallVec::new();
        for j in 0..n {
            let v = self.xor_clauses[xor_idx].vars[j];
            let lit = match self.assignment.value_of(v) {
                Value::True => Literal::negative(v),
                Value::False => Literal::positive(v),
                Value::Undef => continue,
            };
            clause.push(lit);
        }

        // Sort descending by level so lits[0] is the most-recently-assigned literal.
        let levels: SmallVec<[u32; 8]> =
            clause.iter().map(|l| self.assignment.level_of(l.var())).collect();
        let mut idx: SmallVec<[usize; 8]> = (0..clause.len()).collect();
        idx.sort_unstable_by(|&a, &b| levels[b].cmp(&levels[a]));
        let sorted: SmallVec<[Literal; 8]> = idx.iter().map(|&i| clause[i]).collect();
        clause = sorted;

        if clause.len() < 2 {
            self.db.set_empty_clause();
            return ClauseRef::DECISION;
        }
        self.add_xor_explanation(&clause)
    }

    /// Add an XOR explanation clause (reason or conflict) to the DB and watch
    /// lists without touching the AKX outbox (these are structural, not learnt
    /// knowledge).
    fn add_xor_explanation(&mut self, lits: &[Literal]) -> ClauseRef {
        debug_assert!(lits.len() >= 2);
        let lbd = self.compute_lbd(lits);
        let cr = self.db.add(lits, true, lbd);
        if lits.len() == 2 {
            self.binaries[lits[0].negate().raw() as usize].push((lits[1], cr.0));
            self.binaries[lits[1].negate().raw() as usize].push((lits[0], cr.0));
        } else {
            self.watches.watch(lits[0].negate(), cr, lits[1]);
            self.watches.watch(lits[1].negate(), cr, lits[0]);
        }
        cr
    }

    /// S1-6: Compute LBD (Literal Block Distance) using a timestamp array.
    fn compute_lbd(&mut self, lits: &[Literal]) -> u32 {
        self.lbd_epoch = self.lbd_epoch.wrapping_add(1);
        if self.lbd_epoch == 0 {
            self.lbd_stamp.iter_mut().for_each(|s| *s = 0);
            self.lbd_epoch = 1;
        }
        let ep = self.lbd_epoch;
        let mut lbd = 0u32;
        for &lit in lits {
            let lvl = self.assignment.level_of(lit.var()) as usize;
            if lvl < self.lbd_stamp.len() && self.lbd_stamp[lvl] != ep {
                self.lbd_stamp[lvl] = ep;
                lbd += 1;
            }
        }
        lbd
    }

    fn maybe_reduce_db(&mut self) {
        if self.db.learnt_count() <= self.learnt_limit {
            return;
        }
        // Deletion predicate:
        //   tier-1 (lbd ≤ 2):  never deleted.
        //   tier-2 (lbd 3–6):  delete if activity below threshold (low recent use).
        //   tier-3 (lbd > 6):  always deleted unless currently a reason clause.
        self.db.reduce_learned(|cr, lbd, activity, lit0, _used| {
            lbd > 2
                && self.assignment.reason_of(lit0.var()) != cr.0
                && (lbd > 6 || activity < 1e-4)
        });

        // Compact the arena to reclaim deleted words.  compact() returns (old, new)
        // offset pairs for every live clause that moved.
        //
        // We must ALWAYS rebuild watches after compact: stale entries for deleted
        // clauses point to now-removed arena offsets and would OOB on the next BCP
        // lazy-deletion check, even when no live clause moved (remaps empty).
        let remaps = self.db.compact();

        if !remaps.is_empty() {
            // compact() produces remaps sorted ascending by old offset — binary search
            // is allocation-free and faster than a HashMap for typical remap set sizes.

            // Remap reason pointers for every assigned variable.
            for var in 1..=(self.num_vars as Var) {
                let r = self.assignment.reason_of(var);
                if !ClauseRef(r).is_sentinel() {
                    if let Ok(pos) = remaps.binary_search_by_key(&r, |&(old, _)| old) {
                        self.assignment.set_reason(var, remaps[pos].1);
                    }
                }
            }

            // Remap ClauseRef raw values stored in the binary-clause table.
            for entry_list in self.binaries.iter_mut() {
                for (_, cr_raw) in entry_list.iter_mut() {
                    if let Ok(pos) = remaps.binary_search_by_key(cr_raw, |&(old, _)| old) {
                        *cr_raw = remaps[pos].1;
                    }
                }
            }
        }

        // Always rebuild watch lists from the compacted arena.
        self.db.rebuild_watches(&mut self.watches);

        self.learnt_limit = ((self.learnt_limit as f64 * self.learnt_limit_inc) as usize)
            .min(self.learnt_limit_max);
    }

    // -----------------------------------------------------------------------
    // VSIDS
    // -----------------------------------------------------------------------

    fn bump_var_activity(&mut self, var: Var) {
        // VMTF: always move to front regardless of mode; the VSIDS heap is
        // updated in parallel so switching modes doesn't lose bump information.
        self.vmtf.move_to_front(var);
        self.activity[var as usize] += self.activity_inc;
        if self.activity[var as usize] > 1e100 {
            for a in self.activity.iter_mut() {
                *a *= 1e-100;
            }
            self.activity_inc *= 1e-100;
            self.rebuild_heap();
        } else {
            self.heap
                .push(VsidsEntry { activity: self.activity[var as usize], var });
        }
    }

    fn decay_activities(&mut self) {
        self.activity_inc /= self.activity_decay;
    }

    fn rebuild_heap(&mut self) {
        self.heap.clear();
        for var in 1..=self.num_vars {
            self.heap
                .push(VsidsEntry { activity: self.activity[var as usize], var });
        }
    }

    /// Reschedule all variables that will be unassigned by backtracking to
    /// `target_level`, then perform the backtrack.
    fn backtrack_and_reschedule(&mut self, target_level: u32) {
        let to_reschedule: SmallVec<[Literal; 32]> = self
            .assignment
            .trail_from_level(target_level)
            .iter()
            .copied()
            .collect();
        for lit in to_reschedule {
            self.heap.push(VsidsEntry {
                activity: self.activity[lit.var() as usize],
                var: lit.var(),
            });
        }
        self.assignment.backtrack_to(target_level);
    }

    // -----------------------------------------------------------------------
    // Branching
    // -----------------------------------------------------------------------

    fn pick_branch(&mut self) -> Option<Literal> {
        // Focus mode: VMTF (O(1) move-to-front, recency-driven for AKX import).
        // Stable mode: VSIDS lazy-deletion max-heap with 0.95 decay.
        if self.mode == SolverMode::Focus {
            let var = self.vmtf.front_unassigned(|v| !self.assignment.is_assigned(v))?;
            return Some(if self.polarity[var as usize] {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            });
        }
        loop {
            let entry = self.heap.pop()?;
            let var = entry.var;
            if self.assignment.is_assigned(var) {
                continue;
            }
            if entry.activity < self.activity[var as usize] {
                continue;
            }
            return Some(if self.polarity[var as usize] {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            });
        }
    }

    // -----------------------------------------------------------------------
    // Restarts (Luby schedule + Glucose EMA)
    // -----------------------------------------------------------------------

    /// Returns true when a restart should fire: either Luby schedule is due, or
    /// the fast LBD EMA has risen above 0.8× the slow EMA (search is thrashing).
    fn should_restart(&self) -> bool {
        if self.conflicts >= self.next_restart_conflicts {
            return true;
        }
        // EMA restart only fires in Focus mode; Stable relies on Luby schedule.
        if self.mode != SolverMode::Focus {
            return false;
        }
        // Require at least 50 conflicts since last restart before firing EMA.
        // Guard of 50 (down from 500) enables kissat-style aggressive restarts
        // in Focus mode every ~50 conflicts. The 0.8 threshold fires whenever
        // fast ≈ slow (almost always after warmup) so acts as a fixed 50-conflict
        // interval, keeping Focus restarts as dense as kissat's inner schedule.
        let conflicts_since = self.conflicts.saturating_sub(self.conflicts_at_last_restart);
        self.lbd_slow_ema > 0.0
            && conflicts_since >= 50
            && self.lbd_fast_ema > self.lbd_slow_ema * 0.8
    }

    fn maybe_restart(&mut self) {
        if self.should_restart() {
            self.do_restart();
        }
    }

    fn do_restart(&mut self) {
        // Phase saving: record current polarities before clearing the trail.
        for &lit in self.assignment.trail() {
            self.polarity[lit.var() as usize] = lit.is_positive();
        }
        // Target phase walk: only in Stable mode.  GPU walk (≥2000 vars) is
        // gated by WALK_GIVE_UP; CPU walk always runs (negligible overhead).
        const GPU_MIN_VARS: u32 = 2000;
        const WALK_GIVE_UP: u32 = 50;
        let skip_walk = self.gpu.is_some()
            && self.num_vars >= GPU_MIN_VARS
            && self.walk_no_improve >= WALK_GIVE_UP;
        if self.mode == SolverMode::Stable
            && self.assumption_floor == 0
            && !skip_walk
        {
            self.walk_phase();
        }
        self.backtrack_and_reschedule(self.assumption_floor);
        // Compact the lazy heap: with slow decay (0.95) the heap accumulates
        // stale entries 4× faster between rescalings, degrading branch selection.
        // Rebuilding at every restart (every ~38 conflicts) keeps it at O(n).
        self.rebuild_heap();
        self.restarts += 1;
        self.conflicts_at_last_restart = self.conflicts;

        // Stable/focus mode phase bookkeeping.
        self.phase_restart_count += 1;
        if self.phase_restart_count >= PHASE_LEN {
            self.phase_restart_count = 0;
            self.mode = match self.mode {
                SolverMode::Focus => SolverMode::Stable,
                SolverMode::Stable => SolverMode::Focus,
            };
        }

        self.activity_decay = 0.95;

        // Luby schedule: 4× wider intervals in Stable mode so the walk has
        // more conflicts to work with between restarts.
        let next = luby_next(&mut self.luby_u, &mut self.luby_v);
        let effective_scale = self.luby_scale;
        self.next_restart_conflicts = self.conflicts + next * effective_scale;

        // Run inprocessing every INPROCESS_INTERVAL conflicts
        // (probe → vivify → subsume → strengthen).
        // Tied to conflicts (not restart count) so EMA-frequent restarts don't
        // cause runaway overhead on hard instances.
        const INPROCESS_INTERVAL: u64 = 5_000;
        if self.assumption_floor == 0
            && self.conflicts.saturating_sub(self.conflicts_at_last_probe)
                >= INPROCESS_INTERVAL
        {
            self.conflicts_at_last_probe = self.conflicts;
            self.inprocess_probe();
            if !self.db.has_empty_clause() {
                self.inprocess_vivify();
            }
            if !self.db.has_empty_clause() {
                self.inprocess_subsume();
            }
            if !self.db.has_empty_clause() {
                self.inprocess_strengthen();
            }
        }

        // Decay clause activity on restart.
        self.clause_inc /= self.clause_decay;
        if self.clause_inc > 1e20 {
            self.clause_inc = 1.0;
            self.db.rescale_activities(1e-20);
        }
    }

    // -----------------------------------------------------------------------
    // Inprocessing: vivification (clause strengthening)
    // -----------------------------------------------------------------------

    /// Strengthen clauses by trying to shorten them via BCP.
    ///
    /// For each candidate clause C = {l0, l1, …, l_{k-1}} we push ¬l0, ¬l1, …
    /// one by one at level 1 and propagate.  If a conflict arises, C is subsumed
    /// (delete it).  If some l_j becomes True, C can be replaced by a shorter
    /// clause (the assumed-False prefix plus l_j).
    ///
    /// Candidates are sorted by LBD ascending so the most useful clauses are
    /// processed first within the budget.  Non-learnt clauses (BVE resolvents,
    /// short problem clauses) are included at LBD ≤ 4 — they often have the
    /// lowest LBD and highest leverage.
    fn inprocess_vivify(&mut self) {
        debug_assert_eq!(self.assignment.current_level(), 0);
        const MAX_VIVIFY: usize = 3000;

        // Collect LEARNT candidates (size ≥ 3, LBD ≤ 12) sorted by LBD ascending.
        // Only learnt clauses are vivified: vivifying problem clauses via level-1
        // propagation chains that go through learned clauses is unsound when those
        // learned clauses are later deleted by reduction.
        let mut candidates: Vec<(ClauseRef, u32)> = Vec::new();
        self.db.for_each_clause(3, |cr, lbd, learnt, _| {
            if learnt && lbd <= 12 {
                candidates.push((cr, lbd));
            }
        });
        // Sort by LBD ascending so the highest-leverage clauses are tried first.
        candidates.sort_unstable_by_key(|&(_, lbd)| lbd);

        let mut tried = 0;
        for (cr, saved_lbd) in candidates {
            if tried >= MAX_VIVIFY {
                break;
            }
            if self.db.is_deleted(cr) {
                continue;
            }
            let n = self.db.clause_len(cr);
            // Copy lits: we need ownership so we can call &mut self methods below.
            let lits: Vec<Literal> = (0..n).map(|i| self.db.lit_at(cr, i)).collect();

            // Skip if already satisfied at level 0.
            if lits.iter().any(|&l| {
                matches!(self.assignment.literal_value(l), Value::True)
                    && self.assignment.level_of(l.var()) == 0
            }) {
                continue;
            }

            tried += 1;
            self.assignment.new_decision_level();

            // Track which literals formed the "assumed-False" prefix.
            let mut assumed: Vec<Literal> = Vec::new();
            // Result: None=no change, Delete=subsumed, Shorten(v)=replace
            let mut result: Option<Vec<Literal>> = None;

            'vivify: for i in 0..n - 1 {
                let lit = lits[i];
                match self.assignment.literal_value(lit) {
                    Value::True => {
                        // lit became True (implied by earlier assumptions).
                        // Clause shortens to the assumed prefix + this literal.
                        let mut shorter = assumed.clone();
                        shorter.push(lit);
                        result = Some(shorter);
                        break 'vivify;
                    }
                    Value::False => {
                        // Already forced False; literal is redundant in C.
                        continue;
                    }
                    Value::Undef => {
                        self.assignment
                            .assign(lit.negate(), 1, ClauseRef::DECISION.0);
                        assumed.push(lit);
                        match self.propagate() {
                            Some(_) => {
                                // Conflict: C is subsumed — mark for deletion.
                                result = Some(Vec::new()); // empty = delete marker
                                break 'vivify;
                            }
                            None => {
                                // Check if any remaining literal became True.
                                for j in i + 1..n {
                                    if matches!(
                                        self.assignment.literal_value(lits[j]),
                                        Value::True
                                    ) {
                                        let mut shorter = assumed.clone();
                                        shorter.push(lits[j]);
                                        result = Some(shorter);
                                        break 'vivify;
                                    }
                                }
                            }
                        }
                    }
                }
            }

            self.backtrack_and_reschedule(0);

            match result {
                None => {}
                Some(new_lits) if new_lits.is_empty() => {
                    // Subsumed: delete.
                    self.db.mark_deleted(cr);
                }
                Some(new_lits) if new_lits.len() < n => {
                    self.db.mark_deleted(cr);
                    let new_lbd = saved_lbd.min(new_lits.len() as u32);
                    match new_lits.len() {
                        0 => unreachable!(),
                        1 => {
                            let unit = new_lits[0];
                            match self.assignment.literal_value(unit) {
                                Value::Undef => {
                                    self.assignment
                                        .assign(unit, 0, ClauseRef::DECISION.0);
                                    if self.propagate().is_some() {
                                        self.db.set_empty_clause();
                                        return;
                                    }
                                }
                                Value::False => {
                                    self.db.set_empty_clause();
                                    return;
                                }
                                Value::True => {}
                            }
                        }
                        2 => {
                            let new_cr = self.db.add(&new_lits, true, 1);
                            self.binaries[new_lits[0].negate().raw() as usize]
                                .push((new_lits[1], new_cr.0));
                            self.binaries[new_lits[1].negate().raw() as usize]
                                .push((new_lits[0], new_cr.0));
                        }
                        _ => {
                            let new_cr = self.db.add(&new_lits, true, new_lbd);
                            self.watches.watch(
                                new_lits[0].negate(),
                                new_cr,
                                new_lits[1],
                            );
                            self.watches.watch(
                                new_lits[1].negate(),
                                new_cr,
                                new_lits[0],
                            );
                        }
                    }
                }
                Some(_) => {
                    // Same length or empty: no improvement.
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // Inprocessing: forward subsumption elimination
    // -----------------------------------------------------------------------

    /// Remove clauses that are subsumed by a strictly shorter clause.
    ///
    /// For each clause C (iterated shortest-first), look up every clause D that
    /// shares at least one literal with C.  If C ⊆ D (every literal of C occurs
    /// in D) and |D| > |C|, delete D — it is redundant.
    ///
    /// A 64-bit signature (bitmask of var % 64) pre-filters candidates so the
    /// full subset check only runs when the signature is compatible.  Caps at
    /// MAX_CHECKS candidate pairs per call to bound wall-clock cost.
    fn inprocess_subsume(&mut self) {
        debug_assert_eq!(self.assignment.current_level(), 0);
        const MAX_CHECKS: usize = 20_000;

        let lit_cap = (self.num_vars * 2 + 2) as usize;

        // Collect all non-deleted clauses ≥ 2 with their signature and length.
        let mut entries: Vec<(ClauseRef, usize, u64)> = Vec::new();
        self.db.for_each_clause(2, |cr, _, _, lits| {
            let mut sig: u64 = 0;
            for &l in lits {
                sig |= 1u64 << (l.var() % 64);
            }
            entries.push((cr, lits.len(), sig));
        });
        // Shorter clauses first: they are potential subsumers.
        entries.sort_unstable_by_key(|&(_, len, _)| len);

        // Build occurrence lists: literal raw index → indices into `entries`.
        let mut occs: Vec<Vec<usize>> = vec![Vec::new(); lit_cap];
        for (ei, &(cr, len, _)) in entries.iter().enumerate() {
            for i in 0..len {
                let raw = self.db.lit_at(cr, i).raw() as usize;
                if raw < lit_cap {
                    occs[raw].push(ei);
                }
            }
        }

        let mut checks = 0usize;
        let mut any_deleted = false;

        'outer: for ei in 0..entries.len() {
            let (cr_c, len_c, sig_c) = entries[ei];
            if self.db.is_deleted(cr_c) {
                continue;
            }
            // Collect lits of C (copy out to avoid borrow conflict).
            let lits_c: SmallVec<[Literal; 16]> =
                (0..len_c).map(|i| self.db.lit_at(cr_c, i)).collect();

            // Choose the literal in C with the smallest occurrence list as pivot.
            let pivot_raw = lits_c
                .iter()
                .map(|l| l.raw() as usize)
                .filter(|&r| r < lit_cap)
                .min_by_key(|&r| occs[r].len())
                .unwrap_or(usize::MAX);
            if pivot_raw == usize::MAX {
                continue;
            }

            for &ej in &occs[pivot_raw] {
                if ej <= ei {
                    continue; // only check strictly larger entries
                }
                let (cr_d, len_d, sig_d) = entries[ej];
                if len_d <= len_c {
                    continue;
                }
                if self.db.is_deleted(cr_d) {
                    continue;
                }
                if sig_c & sig_d != sig_c {
                    continue; // signature says C cannot be a subset of D
                }

                // A learned clause must never subsume a problem clause: the
                // learned clause may be deleted by reduction, which would make
                // the problem clause necessary again — but it's already gone.
                if self.db.is_learnt(cr_c) && !self.db.is_learnt(cr_d) {
                    continue;
                }

                checks += 1;
                if checks > MAX_CHECKS {
                    break 'outer;
                }

                // Full subset check: every literal of C must appear in D.
                let lits_d: SmallVec<[Literal; 16]> =
                    (0..len_d).map(|i| self.db.lit_at(cr_d, i)).collect();
                if lits_c.iter().all(|&l| lits_d.contains(&l)) {
                    self.db.mark_deleted(cr_d);
                    any_deleted = true;
                }
            }
        }

        // BCP handles deleted watch entries lazily, so no rebuild needed unless
        // we also need deterministic watch counts.  A rebuild here keeps the watch
        // list tight and avoids accumulating stale entries across many inprocessing
        // rounds.
        if any_deleted {
            self.db.rebuild_watches(&mut self.watches);
        }
    }

    // -----------------------------------------------------------------------
    // Inprocessing: binary self-subsuming resolution (clause strengthening)
    // -----------------------------------------------------------------------

    /// For each binary clause (¬p ∨ q) and each long clause C containing both
    /// p and q, remove p from C (self-subsuming resolution on p).
    ///
    /// Particularly effective on PHP: binary hole-conflict clauses (¬x_pi ∨ ¬x_pj)
    /// can shorten many learned clauses, driving down LBD and improving proof quality.
    /// Each call is capped at MAX_STRENGTHENS operations to bound wall-clock cost.
    fn inprocess_strengthen(&mut self) {
        debug_assert_eq!(self.assignment.current_level(), 0);
        const MAX_STRENGTHENS: usize = 4_000;

        let nv = self.num_vars as usize;
        let lit_cap = (2 * nv + 4).min(self.binaries.len());

        // Build occurrence lists for non-deleted long (≥3) clauses.
        let mut occ: Vec<Vec<ClauseRef>> = vec![Vec::new(); lit_cap];
        self.db.for_each_clause(3, |cr, _, _, lits| {
            for &l in lits {
                let r = l.raw() as usize;
                if r < lit_cap {
                    occ[r].push(cr);
                }
            }
        });

        // Collect (clause, literal-to-remove) pairs.
        // For binary (¬p ∨ q): any long clause C with both p_lit and q can have p_lit removed.
        let mut to_shrink: Vec<(ClauseRef, Literal)> = Vec::new();

        'outer: for p_lit_raw in 0..lit_cap {
            let p_lit = Literal::from_raw(p_lit_raw as u32);
            // Iterate by index so we don't clone the binary list.
            let n_bin = self.binaries[p_lit_raw].len();
            for bi in 0..n_bin {
                let (q, _) = self.binaries[p_lit_raw][bi];
                let q_raw = q.raw() as usize;
                if q_raw >= lit_cap {
                    continue;
                }
                let q_neg = q.negate();
                for &cr in &occ[p_lit_raw] {
                    if to_shrink.len() >= MAX_STRENGTHENS {
                        break 'outer;
                    }
                    if self.db.is_deleted(cr) {
                        continue;
                    }
                    // Collect lits once; release &self.db before touching &self.assignment.
                    let lits: SmallVec<[Literal; 16]> =
                        self.db.lits(cr).iter().copied().collect();
                    // Single pass: check has_q, tautology, and reason in one scan.
                    let mut has_q = false;
                    let mut has_neg_q = false;
                    let mut is_reason = false;
                    for &l in &lits {
                        if l == q { has_q = true; }
                        if l == q_neg { has_neg_q = true; }
                        if self.assignment.reason_of(l.var()) == cr.0 { is_reason = true; }
                    }
                    if !has_q || has_neg_q || is_reason {
                        continue;
                    }
                    to_shrink.push((cr, p_lit));
                }
            }
        }

        if to_shrink.is_empty() {
            return;
        }

        // Apply: delete original, add shortened version.
        // One clause may only be processed once per pass (further literals removed next pass).
        let mut queued: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let mut to_add: Vec<(Vec<Literal>, bool)> = Vec::new();

        for (cr, remove_lit) in to_shrink {
            if queued.contains(&cr.0) || self.db.is_deleted(cr) {
                continue;
            }
            let n = self.db.clause_len(cr);
            let is_learnt = self.db.is_learnt(cr);
            let new_lits: Vec<Literal> = (0..n)
                .map(|i| self.db.lit_at(cr, i))
                .filter(|&l| l != remove_lit)
                .collect();
            if new_lits.len() < n {
                queued.insert(cr.0);
                to_add.push((new_lits, is_learnt));
            }
        }

        for &cr_raw in &queued {
            self.db.mark_deleted(ClauseRef(cr_raw));
        }

        let mut any_unit = false;
        for (new_lits, is_learnt) in to_add {
            match new_lits.len() {
                0 => {
                    self.db.set_empty_clause();
                    return;
                }
                1 => {
                    let unit = new_lits[0];
                    match self.assignment.literal_value(unit) {
                        Value::Undef => {
                            self.assignment.assign(unit, 0, ClauseRef::DECISION.0);
                            any_unit = true;
                        }
                        Value::False => {
                            self.db.set_empty_clause();
                            return;
                        }
                        Value::True => {}
                    }
                }
                2 => {
                    let cr = self.db.add(&new_lits, is_learnt, 1);
                    self.binaries[new_lits[0].negate().raw() as usize]
                        .push((new_lits[1], cr.0));
                    self.binaries[new_lits[1].negate().raw() as usize]
                        .push((new_lits[0], cr.0));
                }
                _ => {
                    // Conservative LBD estimate: use clause length (actual LBD can only
                    // be lower; compute_lbd requires level info we have at level 0).
                    let estimated_lbd = new_lits.len() as u32;
                    let cr = self.db.add(&new_lits, is_learnt, estimated_lbd);
                    self.watches.watch(new_lits[0].negate(), cr, new_lits[1]);
                    self.watches.watch(new_lits[1].negate(), cr, new_lits[0]);
                }
            }
        }

        if any_unit {
            if self.propagate().is_some() {
                self.db.set_empty_clause();
                return;
            }
        }

        self.db.rebuild_watches(&mut self.watches);
    }

    // -----------------------------------------------------------------------
    // Target phase walk (local search to improve polarity table per restart)
    // -----------------------------------------------------------------------

    /// Dispatch walk to GPU (if available) or the sequential CPU walk.
    fn walk_phase(&mut self) {
        if self.assumption_floor > 0 {
            return;
        }
        // Metal/CUDA round-trip overhead is ~1-2ms per call (buffer alloc, command
        // buffer encode, waitUntilCompleted, 9 buffer deallocs).  On instances with
        // < 2000 vars that overhead dwarfs the actual GPU compute time and makes RM
        // 3-5× slower than a single-threaded CPU solver.  Fall back to CPU walk for
        // small instances; GPU pays off once the shader compute time exceeds ~2ms.
        const GPU_MIN_VARS: u32 = 2000;
        let improved = if self.gpu.is_some() && self.num_vars >= GPU_MIN_VARS {
            self.walk_phase_gpu()
        } else {
            self.walk_phase_cpu()
        };
        if improved {
            self.walk_no_improve = 0;
        } else {
            self.walk_no_improve = self.walk_no_improve.saturating_add(1);
        }
    }

    /// GPU-accelerated walk: dispatches 10 000 independent WalkSAT trajectories
    /// to the Metal (or CUDA) backend and writes back the best polarity found.
    /// Returns true if the polarity was updated (sat_count improved).
    fn walk_phase_gpu(&mut self) -> bool {
        let n = self.num_vars as usize;
        let mut gpu_clauses: Vec<GpuClause> = Vec::new();
        self.db.for_each_clause(2, |_, _, _, lits| {
            let dimacs: Vec<i32> = lits
                .iter()
                .map(|l| {
                    let v = l.var() as i32;
                    if l.is_positive() { v } else { -v }
                })
                .collect();
            gpu_clauses.push(GpuClause { lits: dimacs });
        });
        if gpu_clauses.is_empty() {
            return false;
        }

        let initial_polarity = self.polarity.clone();
        let seed = self.conflicts
            .wrapping_mul(0x9e3779b97f4a7c15)
            .wrapping_add((self.restarts as u64).wrapping_mul(0x6c62272e07bb0142));

        // Compute sat_count for the current polarity (the "before" score).
        let initial_score = {
            let pol = &self.polarity;
            gpu_clauses.iter().filter(|c| {
                c.lits.iter().any(|&l| {
                    let v = l.unsigned_abs() as usize;
                    v >= 1 && v <= n && (l > 0) == pol[v]
                })
            }).count()
        };

        let result = self.gpu.as_ref().unwrap().walk(
            &gpu_clauses,
            self.num_vars,
            &initial_polarity,
            seed,
            10_000,
            4,
        );

        if result.sat_count > initial_score {
            for v in 1..=n {
                self.polarity[v] = result.polarity[v];
            }
            true
        } else {
            false
        }
    }

    /// Sequential single-trajectory WalkSAT.
    ///
    /// Iterates up to `4 × num_vars` flip steps.  Each step picks a random
    /// unsatisfied clause and flips the variable in that clause with the lowest
    /// break count (fewest currently-singleton-satisfied clauses lost).
    /// The best assignment seen (most clauses satisfied) is committed back to
    /// `self.polarity` so future decisions are guided toward it.
    ///
    /// Called once per restart, after phase saving and before backtracking.
    /// Has no effect when assumption_floor > 0 (incremental solving context).
    /// Returns true if the polarity table was updated (walk found improvement).
    fn walk_phase_cpu(&mut self) -> bool {
        if self.assumption_floor > 0 {
            return false;
        }
        let n = self.num_vars as usize;
        let max_steps = n * 16;

        // Collect all non-deleted clauses (size ≥ 2) into flat storage.
        // We copy literals out of the arena so we can borrow `self.polarity`
        // mutably later without fighting the borrow checker.
        let mut clauses: Vec<Vec<Literal>> = Vec::new();
        self.db.for_each_clause(2, |_, _, _, lits| {
            clauses.push(lits.to_vec());
        });
        let nc = clauses.len();
        if nc == 0 {
            return false;
        }

        // Occurrence lists: literal raw → list of clause indices (u32 to save memory).
        let lit_cap = 2 * n + 4;
        let mut occs: Vec<Vec<u32>> = vec![Vec::new(); lit_cap];
        for (ci, c) in clauses.iter().enumerate() {
            for &l in c {
                let raw = l.raw() as usize;
                if raw < lit_cap {
                    occs[raw].push(ci as u32);
                }
            }
        }

        // Walk assignment: start from the current saved polarity table.
        let mut wa: Vec<bool> = self.polarity.clone(); // indexed 0..=n

        // Per-clause satisfaction count (number of true literals).
        let mut sat_count: Vec<u8> = clauses
            .iter()
            .map(|c| {
                c.iter()
                    .filter(|&&l| {
                        let v = l.var() as usize;
                        if l.is_positive() { wa[v] } else { !wa[v] }
                    })
                    .count()
                    .min(255) as u8
            })
            .collect();

        let mut total_sat: usize = sat_count.iter().filter(|&&s| s > 0).count();
        let initial_score = total_sat;
        let mut best_score = total_sat;
        let mut best_phase = wa.clone();

        // LCG RNG seeded from solver state (deterministic, no std::time).
        let mut rng: u64 = self.conflicts
            .wrapping_mul(0x9e3779b97f4a7c15)
            .wrapping_add((self.restarts as u64).wrapping_mul(0x6c62272e07bb0142));

        let mut steps_since_improvement = 0usize;
        const WALK_EARLY_EXIT: usize = 500;

        'walk: for _ in 0..max_steps {
            // Pick a random clause; retry once if it happens to be satisfied.
            rng = rng
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let mut ci = (rng >> 33) as usize % nc;
            if sat_count[ci] > 0 {
                rng = rng
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                ci = (rng >> 33) as usize % nc;
                if sat_count[ci] > 0 {
                    continue;
                }
            }

            // 15% noise: pick a random literal from the clause instead of
            // greedily picking the minimum break-count variable.  This lets
            // WalkSAT escape local optima that have no zero-break flip.
            rng = rng
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let noise = (rng >> 33) % 100 < 15;
            let clause = &clauses[ci];

            if noise {
                rng = rng
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                let pick = (rng >> 33) as usize % clause.len();
                let v = clause[pick].var() as usize;
                if v == 0 || v > n {
                    continue;
                }
                wa[v] = !wa[v];
                let (gain_lit, lose_lit) = if wa[v] {
                    (Literal::positive(v as u32), Literal::negative(v as u32))
                } else {
                    (Literal::negative(v as u32), Literal::positive(v as u32))
                };
                for &c in &occs[gain_lit.raw() as usize] {
                    let c = c as usize;
                    if sat_count[c] == 0 { total_sat += 1; }
                    sat_count[c] = sat_count[c].saturating_add(1);
                }
                for &c in &occs[lose_lit.raw() as usize] {
                    let c = c as usize;
                    if sat_count[c] == 1 { total_sat -= 1; }
                    sat_count[c] = sat_count[c].saturating_sub(1);
                }
                if total_sat > best_score {
                    best_score = total_sat;
                    best_phase = wa.clone();
                    steps_since_improvement = 0;
                } else {
                    steps_since_improvement += 1;
                    if steps_since_improvement >= WALK_EARLY_EXIT {
                        break 'walk;
                    }
                }
                continue;
            }

            // Find the variable in this clause with the minimum break count.
            let mut flip_var = 0usize;
            let mut min_break = usize::MAX;

            for &l in clause {
                let v = l.var() as usize;
                if v == 0 || v > n {
                    continue;
                }
                let cur_lit = if wa[v] {
                    Literal::positive(v as u32)
                } else {
                    Literal::negative(v as u32)
                };
                let brk: usize = occs[cur_lit.raw() as usize]
                    .iter()
                    .filter(|&&c| sat_count[c as usize] == 1)
                    .count();
                if brk < min_break {
                    min_break = brk;
                    flip_var = v;
                }
                if min_break == 0 {
                    break;
                }
            }
            if flip_var == 0 {
                continue;
            }

            // Perform the flip and update sat_count incrementally.
            wa[flip_var] = !wa[flip_var];
            let (gain_lit, lose_lit) = if wa[flip_var] {
                (
                    Literal::positive(flip_var as u32),
                    Literal::negative(flip_var as u32),
                )
            } else {
                (
                    Literal::negative(flip_var as u32),
                    Literal::positive(flip_var as u32),
                )
            };

            for &c in &occs[gain_lit.raw() as usize] {
                let c = c as usize;
                if sat_count[c] == 0 {
                    total_sat += 1;
                }
                sat_count[c] = sat_count[c].saturating_add(1);
            }
            for &c in &occs[lose_lit.raw() as usize] {
                let c = c as usize;
                if sat_count[c] == 1 {
                    total_sat -= 1;
                }
                sat_count[c] = sat_count[c].saturating_sub(1);
            }

            if total_sat > best_score {
                best_score = total_sat;
                best_phase = wa.clone();
                steps_since_improvement = 0;
            } else {
                steps_since_improvement += 1;
                if steps_since_improvement >= WALK_EARLY_EXIT {
                    break 'walk;
                }
            }
        }

        // Only overwrite polarity when the walk actually found a better assignment.
        // For UNSAT instances the walk makes no progress; writing back a random-search
        // polarity would corrupt the CDCL phase table with meaningless noise.
        if best_score > initial_score {
            for v in 1..=n {
                self.polarity[v] = best_phase[v];
            }
            true
        } else {
            false
        }
    }

    // -----------------------------------------------------------------------
    // Inprocessing: failed literal probing
    // -----------------------------------------------------------------------

    /// Probe each unassigned variable at level 1. If assigning a literal leads
    /// to a BCP conflict, its negation is forced as a level-0 unit. Discovers
    /// backbone variables cheaply between restarts.
    ///
    /// Runs up to MAX_ROUNDS passes; each pass probes up to MAX_PROBES_PER_ROUND
    /// variables. Stops early when no new unit is discovered (fixpoint).
    fn inprocess_probe(&mut self) {
        debug_assert_eq!(self.assignment.current_level(), 0);
        const MAX_PROBES_PER_ROUND: u32 = 600;
        const MAX_ROUNDS: u32 = 4;

        // Probe high-activity variables first: they are most likely to be backbone
        // and yield the most unit propagations when forced.
        let mut probe_vars: Vec<Var> = (1..=self.num_vars)
            .filter(|&v| !self.assignment.is_assigned(v))
            .collect();
        probe_vars.sort_unstable_by(|&a, &b| {
            self.activity[b as usize]
                .partial_cmp(&self.activity[a as usize])
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        for _ in 0..MAX_ROUNDS {
            let trail_len_before = self.assignment.trail().len();
            let mut probed = 0u32;

            for &var in &probe_vars {
                if probed >= MAX_PROBES_PER_ROUND {
                    break;
                }
                if self.assignment.is_assigned(var) {
                    continue;
                }
                for polarity in [true, false] {
                    if self.assignment.is_assigned(var) {
                        break;
                    }
                    probed += 1;
                    let probe_lit = if polarity {
                        Literal::positive(var)
                    } else {
                        Literal::negative(var)
                    };
                    self.assignment.new_decision_level();
                    self.assignment.assign(probe_lit, 1, ClauseRef::DECISION.0);
                    let conflict = self.propagate();
                    if conflict.is_some() {
                        // Failed literal: probe_lit → contradiction; force its negation.
                        let forced = probe_lit.negate();
                        self.backtrack_and_reschedule(0);
                        match self.assignment.literal_value(forced) {
                            Value::True => {} // already forced by other means
                            Value::False => {
                                // Both polarities lead to contradiction: UNSAT.
                                self.db.set_empty_clause();
                                return;
                            }
                            Value::Undef => {
                                self.assignment.assign(forced, 0, ClauseRef::DECISION.0);
                                if self.propagate().is_some() {
                                    self.db.set_empty_clause();
                                    return;
                                }
                            }
                        }
                    } else {
                        self.backtrack_and_reschedule(0);
                    }
                }
            }

            // Fixpoint: no new level-0 units derived this round.
            if self.assignment.trail().len() == trail_len_before {
                break;
            }
        }
    }

    // -----------------------------------------------------------------------
    // Model extraction
    // -----------------------------------------------------------------------

    fn extract_model(&self) -> Model {
        let mut values = vec![false; self.num_vars as usize + 1];
        for var in 1..=self.num_vars {
            values[var as usize] = matches!(self.assignment.value_of(var), Value::True);
        }
        // Extend the assignment with BVE-eliminated variables (reverse order).
        crate::bve::extend_model(&mut values, &self.bve_eliminated);
        Model::new(values)
    }

    // -----------------------------------------------------------------------
    // BVE preprocessing
    // -----------------------------------------------------------------------

    /// Run Bounded Variable Elimination before the main search loop.
    /// Fills `self.bve_eliminated` and adds resolvents to the arena, then
    /// rebuilds the watch list from the reduced formula.
    fn run_bve(&mut self) {
        debug_assert_eq!(self.assignment.current_level(), 0);
        // Mark done first so the guard never re-fires, even on early return.
        self.bve_done = true;

        // Settle all pending unit propagations before BVE sees the formula.
        // BVE deletes original clauses before propagation runs; if a root
        // assertion or Tseitin unit was on the trail but not yet propagated,
        // BVE would process the pre-propagation formula and could delete clauses
        // that are essential for UNSAT detection, producing incorrect SAT results.
        if self.propagate().is_some() {
            self.db.set_empty_clause();
            return;
        }

        let arena_start = self.db.data_len();
        let eliminated = crate::bve::run(
            &mut self.db,
            self.num_vars,
            |var| self.assignment.is_assigned(var),
        );

        // Scan new arena entries (added by BVE as resolvents) and register:
        //   len=1 → assign the literal at level 0 (unit propagation)
        //   len=2 → insert into the binary propagation table so BCP sees them.
        // We collect first to avoid holding an immutable borrow while mutating
        // `self.assignment` and `self.binaries`.
        let mut new_shorts: Vec<(Vec<Literal>, u32)> = Vec::new();
        self.db.for_each_clause_from(arena_start, 1, |cr, _, _, lits| {
            if lits.len() <= 2 {
                new_shorts.push((lits.to_vec(), cr.0));
            }
        });

        let mut early_unsat = false;
        for (lits, cr_raw) in new_shorts {
            match lits.len() {
                1 => {
                    let unit = lits[0];
                    match self.assignment.literal_value(unit) {
                        Value::Undef => {
                            self.assignment.assign(unit, 0, cr_raw);
                        }
                        Value::False => {
                            self.db.set_empty_clause();
                            early_unsat = true;
                            break;
                        }
                        Value::True => {}
                    }
                }
                2 => {
                    self.binaries[lits[0].negate().raw() as usize]
                        .push((lits[1], cr_raw));
                    self.binaries[lits[1].negate().raw() as usize]
                        .push((lits[0], cr_raw));
                }
                _ => unreachable!(),
            }
        }
        if early_unsat {
            return;
        }

        // Propagate all newly assigned unit literals.
        if self.propagate().is_some() {
            self.db.set_empty_clause();
            return;
        }

        if eliminated.is_empty() {
            return;
        }

        // Rebuild watch list from the reduced formula.
        self.db.rebuild_watches(&mut self.watches);
        self.bve_eliminated = eliminated;
    }
}

// ---------------------------------------------------------------------------
// Luby restart sequence
// ---------------------------------------------------------------------------

/// Advance the Luby generator and return the next element.
/// Generates: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
fn luby_next(u: &mut u64, v: &mut u64) -> u64 {
    let result = *v;
    if *u & u.wrapping_neg() == *v {
        *u += 1;
        *v = 1;
    } else {
        *v <<= 1;
    }
    result
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use rm_akx::literal::Literal;

    // -----------------------------------------------------------------------
    // Brute-force oracle for property tests
    // -----------------------------------------------------------------------

    /// DIMACS-style: positive int = positive literal (1-indexed), negative = negative.
    fn brute_force(num_vars: u32, clauses: &[Vec<i32>]) -> bool {
        'outer: for mask in 0u64..(1u64 << num_vars) {
            for clause in clauses {
                let sat = clause.iter().any(|&lit| {
                    let var = (lit.unsigned_abs() - 1) as u64;
                    let val = (mask >> var) & 1 == 1;
                    if lit > 0 { val } else { !val }
                });
                if !sat {
                    continue 'outer;
                }
            }
            return true;
        }
        false
    }

    fn dimacs_to_solver(num_vars: u32, clauses: &[Vec<i32>]) -> CdclSolver {
        let mut s = CdclSolver::new(num_vars);
        for clause in clauses {
            let lits: Vec<Literal> = clause
                .iter()
                .map(|&l| {
                    if l > 0 {
                        Literal::positive(l as u32)
                    } else {
                        Literal::negative((-l) as u32)
                    }
                })
                .collect();
            s.add_clause(&lits);
        }
        s
    }

    fn cdcl_is_sat(num_vars: u32, clauses: &[Vec<i32>]) -> bool {
        let mut s = dimacs_to_solver(num_vars, clauses);
        matches!(s.solve(&[], u64::MAX), SolveResult::Sat(_))
    }

    // -----------------------------------------------------------------------
    // Basic sanity
    // -----------------------------------------------------------------------

    #[test]
    fn empty_formula_is_sat() {
        let mut s = CdclSolver::new(1);
        assert!(matches!(s.solve(&[], u64::MAX), SolveResult::Sat(_)));
    }

    #[test]
    fn empty_clause_is_unsat() {
        let mut s = CdclSolver::new(1);
        s.add_clause(&[]);
        assert_eq!(s.solve(&[], u64::MAX), SolveResult::Unsat);
    }

    #[test]
    fn unit_sat() {
        assert!(cdcl_is_sat(1, &[vec![1]]));
    }

    #[test]
    fn unit_unsat() {
        let sat = cdcl_is_sat(1, &[vec![1], vec![-1]]);
        assert!(!sat);
    }

    #[test]
    fn simple_2sat() {
        // (x1 ∨ x2) ∧ (¬x1 ∨ x2) → x2 must be true
        assert!(cdcl_is_sat(2, &[vec![1, 2], vec![-1, 2]]));
    }

    #[test]
    fn simple_unsat_3() {
        // x1 ∧ x2 ∧ (¬x1 ∨ ¬x2)
        let sat = cdcl_is_sat(2, &[vec![1], vec![2], vec![-1, -2]]);
        assert!(!sat);
    }

    // -----------------------------------------------------------------------
    // Model validation
    // -----------------------------------------------------------------------

    #[test]
    fn model_is_valid() {
        let clauses = vec![vec![1, 2], vec![-1, 3], vec![-2, -3]];
        let mut s = dimacs_to_solver(3, &clauses);
        match s.solve(&[], u64::MAX) {
            SolveResult::Sat(model) => {
                assert!(model.verify_dimacs(&clauses), "model failed verification");
            }
            _ => panic!("expected SAT"),
        }
    }

    // -----------------------------------------------------------------------
    // Brute-force oracle comparison on random 3-SAT instances
    // -----------------------------------------------------------------------

    struct Lcg {
        state: u64,
    }
    impl Lcg {
        fn new(seed: u64) -> Self {
            Lcg { state: seed }
        }
        fn next(&mut self) -> u64 {
            self.state = self
                .state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.state
        }
        fn range(&mut self, lo: i32, hi: i32) -> i32 {
            lo + (self.next() % (hi - lo + 1) as u64) as i32
        }
    }

    fn random_3sat(rng: &mut Lcg, num_vars: u32, num_clauses: u32) -> Vec<Vec<i32>> {
        (0..num_clauses)
            .map(|_| {
                let mut lits = Vec::new();
                let mut used = vec![false; num_vars as usize + 1];
                for _ in 0..3 {
                    loop {
                        let var = rng.range(1, num_vars as i32);
                        if !used[var as usize] {
                            used[var as usize] = true;
                            let sign = if rng.next() & 1 == 0 { 1 } else { -1 };
                            lits.push(sign * var);
                            break;
                        }
                    }
                }
                lits
            })
            .collect()
    }

    #[test]
    fn oracle_3sat_4vars() {
        let mut rng = Lcg::new(42);
        let num_vars = 4u32;
        let mut mismatches = 0;
        for _ in 0..500 {
            let clauses = random_3sat(&mut rng, num_vars, 8);
            let bf = brute_force(num_vars, &clauses);
            let cdcl = cdcl_is_sat(num_vars, &clauses);
            if bf != cdcl {
                mismatches += 1;
                eprintln!("mismatch: bf={bf} cdcl={cdcl} clauses={clauses:?}");
            }
        }
        assert_eq!(mismatches, 0, "{mismatches} mismatches in oracle test");
    }

    #[test]
    fn oracle_3sat_6vars() {
        let mut rng = Lcg::new(137);
        let num_vars = 6u32;
        let mut mismatches = 0;
        for _ in 0..200 {
            let clauses = random_3sat(&mut rng, num_vars, 14);
            let bf = brute_force(num_vars, &clauses);
            let cdcl = cdcl_is_sat(num_vars, &clauses);
            if bf != cdcl {
                mismatches += 1;
                eprintln!("mismatch: bf={bf} cdcl={cdcl}");
            }
        }
        assert_eq!(mismatches, 0, "{mismatches} mismatches in oracle test");
    }

    #[test]
    fn oracle_sweep_broad() {
        let mut rng = Lcg::new(7);
        let mut mismatches = 0u32;
        let mut checked = 0u32;
        for num_vars in 3..=8u32 {
            for num_clauses in (num_vars - 1)..=(num_vars * 3) {
                for _ in 0..40 {
                    let clauses = random_3sat(&mut rng, num_vars, num_clauses);
                    let bf = brute_force(num_vars, &clauses);
                    let mut s = dimacs_to_solver(num_vars, &clauses);
                    match s.solve(&[], u64::MAX) {
                        SolveResult::Sat(m) => {
                            assert_eq!(m.num_vars(), num_vars, "model must be complete");
                            if !m.verify_dimacs(&clauses) {
                                mismatches += 1;
                                eprintln!("invalid SAT model: {clauses:?} model={m:?}");
                            }
                            if !bf {
                                mismatches += 1;
                                eprintln!("SAT but brute-force says UNSAT: {clauses:?}");
                            }
                        }
                        SolveResult::Unsat => {
                            if bf {
                                mismatches += 1;
                                eprintln!("UNSAT but brute-force says SAT: {clauses:?}");
                            }
                        }
                        SolveResult::Unknown | SolveResult::BudgetExceeded => {
                            mismatches += 1;
                            eprintln!("UNKNOWN for small formula: {clauses:?}");
                        }
                    }
                    checked += 1;
                }
            }
        }
        assert_eq!(
            mismatches, 0,
            "{mismatches}/{checked} mismatches in oracle sweep"
        );
    }

    // -----------------------------------------------------------------------
    // Assumptions (incremental cube solving)
    // -----------------------------------------------------------------------

    #[test]
    fn solve_with_assumptions_sat() {
        let clauses = vec![vec![1, 2]];
        let mut s = dimacs_to_solver(2, &clauses);
        match s.solve(&[Literal::negative(2)], u64::MAX) {
            SolveResult::Sat(m) => {
                assert!(
                    m.satisfies(Literal::negative(2)),
                    "assumption not satisfied"
                );
                assert!(m.satisfies(Literal::positive(1)), "expected x1");
                assert!(m.verify_dimacs(&clauses));
            }
            other => panic!("expected SAT, got {other:?}"),
        }
    }

    #[test]
    fn solve_with_assumptions_unsat() {
        let mut s = dimacs_to_solver(1, &[vec![1]]);
        assert_eq!(
            s.solve(&[Literal::negative(1)], u64::MAX),
            SolveResult::Unsat
        );
    }

    fn brute_force_assumptions(
        num_vars: u32,
        clauses: &[Vec<i32>],
        assumptions: &[Literal],
    ) -> bool {
        'outer: for mask in 0u64..(1u64 << num_vars) {
            for &a in assumptions {
                let var = (a.var() - 1) as u64;
                let val = (mask >> var) & 1 == 1;
                let ok = if a.is_positive() { val } else { !val };
                if !ok {
                    continue 'outer;
                }
            }
            for clause in clauses {
                let sat = clause.iter().any(|&lit| {
                    let var = (lit.unsigned_abs() - 1) as u64;
                    let val = (mask >> var) & 1 == 1;
                    if lit > 0 { val } else { !val }
                });
                if !sat {
                    continue 'outer;
                }
            }
            return true;
        }
        false
    }

    #[test]
    fn oracle_with_random_assumptions() {
        let mut rng = Lcg::new(99);
        let num_vars = 5u32;
        for _ in 0..300 {
            let clauses = random_3sat(&mut rng, num_vars, 10);
            let mut assumptions = Vec::new();
            for v in 1..=num_vars {
                if rng.next() & 3 == 0 {
                    let l = if rng.next() & 1 == 0 {
                        Literal::positive(v)
                    } else {
                        Literal::negative(v)
                    };
                    assumptions.push(l);
                }
            }
            let bf = brute_force_assumptions(num_vars, &clauses, &assumptions);
            let mut s = dimacs_to_solver(num_vars, &clauses);
            let cdcl = match s.solve(&assumptions, u64::MAX) {
                SolveResult::Sat(m) => {
                    for &a in &assumptions {
                        assert!(m.satisfies(a), "model misses assumption {a:?}");
                    }
                    assert!(m.verify_dimacs(&clauses), "model violates a clause");
                    true
                }
                SolveResult::Unsat => false,
                SolveResult::Unknown | SolveResult::BudgetExceeded => {
                    panic!("UNKNOWN for small formula")
                }
            };
            assert_eq!(
                bf, cdcl,
                "mismatch with assumptions {assumptions:?} on {clauses:?}"
            );
        }
    }

    #[test]
    fn repeated_assumption_solves_are_independent() {
        // (x1 ∨ x2) ∧ (¬x1 ∨ x3)
        let clauses = vec![vec![1, 2], vec![-1, 3]];
        let mut s = dimacs_to_solver(3, &clauses);

        match s.solve(&[Literal::negative(2)], u64::MAX) {
            SolveResult::Sat(m) => {
                assert!(m.satisfies(Literal::positive(1)));
                assert!(m.satisfies(Literal::positive(3)));
            }
            other => panic!("expected SAT, got {other:?}"),
        }

        assert_eq!(
            s.solve(&[Literal::negative(1), Literal::negative(2)], u64::MAX),
            SolveResult::Unsat
        );

        match s.solve(&[Literal::positive(3)], u64::MAX) {
            SolveResult::Sat(m) => {
                assert!(m.satisfies(Literal::positive(3)));
                assert!(m.verify_dimacs(&clauses));
            }
            other => panic!("expected SAT, got {other:?}"),
        }
    }

    #[test]
    fn import_clauses_mid_search_g0() {
        let mut s = dimacs_to_solver(3, &[vec![-1, -2, -3]]);
        assert!(matches!(s.solve(&[], 0), SolveResult::Sat(_)));

        let units: Vec<Vec<Literal>> = vec![vec![1], vec![2], vec![3]]
            .into_iter()
            .map(|c| c.into_iter().map(|l| Literal::positive(l as u32)).collect())
            .collect();
        assert_eq!(s.import_clauses(&units), 3);
        assert_eq!(s.solve(&[], u64::MAX), SolveResult::Unsat);
    }

    // -----------------------------------------------------------------------
    // Budget behaviour
    // -----------------------------------------------------------------------

    #[test]
    fn zero_budget_returns_budget_exceeded() {
        let (nv, clauses) = pigeonhole(3, 2);
        let mut s = dimacs_to_solver(nv, &clauses);
        assert_eq!(s.solve(&[], 0), SolveResult::BudgetExceeded);
    }

    #[test]
    fn unlimited_budget_terminates() {
        let (nv, clauses) = pigeonhole(5, 5);
        let mut s = dimacs_to_solver(nv, &clauses);
        match s.solve(&[], u64::MAX) {
            SolveResult::Sat(m) => {
                let violating: Vec<&Vec<i32>> = clauses
                    .iter()
                    .filter(|c| !m.verify_dimacs(std::slice::from_ref(c)))
                    .collect();
                if !violating.is_empty() {
                    panic!("SAT model violates clauses {violating:?} (model={m:?}, vars={nv})");
                }
            }
            SolveResult::Unsat => {
                if brute_force(nv, &clauses) {
                    panic!("reported UNSAT but pigeonhole(5,5) is satisfiable");
                }
            }
            SolveResult::Unknown | SolveResult::BudgetExceeded => {
                panic!("expected a decision for pigeonhole(5,5)")
            }
        }
    }

    // -----------------------------------------------------------------------
    // Pigeonhole: n+1 pigeons in n holes — classic hard UNSAT
    // -----------------------------------------------------------------------

    fn pigeonhole(pigeons: u32, holes: u32) -> (u32, Vec<Vec<i32>>) {
        let var = |p: u32, h: u32| -> i32 { (p * holes + h + 1) as i32 };
        let num_vars = pigeons * holes;
        let mut clauses: Vec<Vec<i32>> = Vec::new();

        for p in 0..pigeons {
            clauses.push((0..holes).map(|h| var(p, h)).collect());
        }
        for h in 0..holes {
            for p1 in 0..pigeons {
                for p2 in (p1 + 1)..pigeons {
                    clauses.push(vec![-var(p1, h), -var(p2, h)]);
                }
            }
        }
        (num_vars, clauses)
    }

    #[test]
    fn pigeonhole_3_2_is_unsat() {
        let (nv, clauses) = pigeonhole(3, 2);
        let sat = cdcl_is_sat(nv, &clauses);
        assert!(!sat, "pigeonhole(3,2) should be UNSAT");
    }

    #[test]
    fn pigeonhole_4_3_is_unsat() {
        let (nv, clauses) = pigeonhole(4, 3);
        let sat = cdcl_is_sat(nv, &clauses);
        assert!(!sat, "pigeonhole(4,3) should be UNSAT");
    }

    #[test]
    fn luby_sequence() {
        let mut u = 1u64;
        let mut v = 1u64;
        let expected = [1u64, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
        for &e in &expected {
            assert_eq!(luby_next(&mut u, &mut v), e);
        }
    }

    #[test]
    fn reduction_keeps_reasons_and_watches_live() {
        let (nv, clauses) = pigeonhole(8, 7);
        let mut s = dimacs_to_solver(nv, &clauses);
        s.learnt_limit = 4;
        assert_eq!(s.solve(&[], u64::MAX), SolveResult::Unsat);
    }

    #[test]
    fn deadline_returns_unknown_with_propagation() {
        let (nv, clauses) = pigeonhole(10, 9);
        let mut s = dimacs_to_solver(nv, &clauses);
        let deadline = std::time::Instant::now()
            .checked_add(std::time::Duration::from_millis(30))
            .unwrap();
        match s.solve_with_deadline(&[], u64::MAX, Some(deadline)) {
            SolveResult::Unknown | SolveResult::BudgetExceeded => {}
            SolveResult::Unsat => {}
            SolveResult::Sat(_) => panic!("PHP(10,9) is UNSAT"),
        }
    }

    // -----------------------------------------------------------------------
    // XOR / parity reasoning tests
    // -----------------------------------------------------------------------

    /// Build a CNF encoding XOR(v1,...,vk) = rhs using the standard 2^(k-1)
    /// clause encoding. Returns (num_vars, clauses).
    fn xor_chain_cnf(n_bits: u32, rhs_parity: bool) -> (u32, Vec<Vec<i32>>) {
        // Encode a binary XOR tree over n_bits input variables.
        // Inputs: 1..=n_bits.  Intermediate nodes: n_bits+1..
        // XOR(a, b) = c encoded as 4 clauses (= XOR2_CNF).
        let mut clauses = Vec::new();
        let mut next_var = n_bits + 1;
        let mut layer: Vec<i32> = (1..=n_bits as i32).collect();

        fn xor2(a: i32, b: i32, c: i32, cls: &mut Vec<Vec<i32>>) {
            // XOR(a,b)=c: 4 clauses
            cls.push(vec![a, b, -c]);
            cls.push(vec![a, -b, c]);
            cls.push(vec![-a, b, c]);
            cls.push(vec![-a, -b, -c]);
        }

        while layer.len() > 1 {
            let mut next = Vec::new();
            let mut i = 0;
            while i + 1 < layer.len() {
                let out = next_var as i32;
                next_var += 1;
                xor2(layer[i], layer[i + 1], out, &mut clauses);
                next.push(out);
                i += 2;
            }
            if i < layer.len() {
                next.push(layer[i]);
            }
            layer = next;
        }
        // layer[0] is the final XOR result; assert it equals rhs_parity
        let root = layer[0];
        if rhs_parity {
            clauses.push(vec![root]); // root = 1
        } else {
            clauses.push(vec![-root]); // root = 0
        }

        (next_var - 1, clauses)
    }

    #[test]
    fn xor_chain_8bit_sat() {
        // XOR of 8 bits = 1 should be SAT
        let (nv, clauses) = xor_chain_cnf(8, true);
        assert!(cdcl_is_sat(nv, &clauses));
    }

    #[test]
    fn xor_chain_8bit_unsat() {
        // XOR of 8 bits = 1 AND all bits forced to 0: UNSAT
        // 8 zeros XOR = 0, but we require 1.
        let (nv, mut clauses) = xor_chain_cnf(8, true);
        for v in 1u32..=8 {
            clauses.push(vec![-(v as i32)]); // force all input bits to 0
        }
        let mut s = dimacs_to_solver(nv, &clauses);
        assert_eq!(s.solve(&[], u64::MAX), SolveResult::Unsat);
    }

    #[test]
    fn xor_chain_16bit_solves_quickly() {
        // A 16-bit XOR chain is par-hard for plain CDCL.
        // With XOR propagation it should solve in a handful of conflicts.
        let (nv, clauses) = xor_chain_cnf(16, true);
        let mut s = dimacs_to_solver(nv, &clauses);
        let result = s.solve(&[], 50_000);
        assert!(
            matches!(result, SolveResult::Sat(_)),
            "expected SAT within budget, got {:?}",
            result
        );
    }

    #[test]
    fn xor_chain_32bit_solves_quickly() {
        // par32-equivalent: 32-bit XOR chain with XOR reasoning should succeed.
        let (nv, clauses) = xor_chain_cnf(32, true);
        let mut s = dimacs_to_solver(nv, &clauses);
        let result = s.solve(&[], 200_000);
        assert!(
            matches!(result, SolveResult::Sat(_)),
            "expected SAT within budget, got {:?}",
            result
        );
    }
}
