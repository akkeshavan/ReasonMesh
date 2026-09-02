//! Production CDCL solver — Milestone M1.
//!
//! Implements:
//! - Two-watched-literal BCP (MiniSAT watch convention)
//! - 1-UIP conflict analysis with non-chronological backjumping
//! - VSIDS branching with exponential decay
//! - Luby restart schedule
//! - Basic learned-clause deletion by LBD
//! - Model extraction on SAT

use crate::{
    assignment::{Assignment, Value},
    clause::{Clause, ClauseDb, ClauseRef},
    model::Model,
    watched::WatchList,
};
use rm_akx::literal::{Literal, Var};
use smallvec::SmallVec;
use std::time::Instant;

// ---------------------------------------------------------------------------
// Result type
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub enum SolveResult {
    Sat(Model),
    Unsat,
    Unknown,
}

impl PartialEq for SolveResult {
    fn eq(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (Self::Unsat, Self::Unsat) | (Self::Unknown, Self::Unknown)
        )
    }
}

// ---------------------------------------------------------------------------
// Solver
// ---------------------------------------------------------------------------

pub struct CdclSolver {
    num_vars: u32,
    assignment: Assignment,
    db: ClauseDb,
    watches: WatchList,

    // VSIDS: activity[var] is bumped on each conflict
    activity: Vec<f64>,
    /// Increment applied to activities on bump; grows by 1/decay each conflict.
    activity_inc: f64,
    activity_decay: f64,

    // Luby restart schedule
    luby_u: u64,
    luby_v: u64,
    luby_scale: u64,
    next_restart_conflicts: u64,

    // Clause deletion
    learnt_limit: usize,
    learnt_limit_inc: f64,

    // Statistics
    pub conflicts: u64,
    pub propagations: u64,
    pub restarts: u64,
    pub decisions: u64,

    /// Decision level of the first assumption pushed by the current `solve`
    /// call. Search never backjumps or restarts below this level, so the
    /// assumptions stay assigned for the whole call.
    base_level: u32,

    /// Highest decision level that belongs to the assumptions of the current
    /// `solve` call (i.e. `base_level + num_assumptions` when > 0, else
    /// `base_level`). Backjumps and restarts never go below this, preserving
    /// every assumption literal on the trail.
    assumption_floor: u32,

    /// Learned clauses produced since the last `drain_learned`. Drained by the
    /// Reasoner for AKX export; cleared by the solver's LBD-based reduction
    /// only via removal from the clause DB, never from this queue.
    learned_outbox: Vec<(Vec<Literal>, u32)>,

    /// DRUP proof log: each entry is one learned clause in DIMACS literal
    /// encoding (positive = var true, negative = var false). Populated only
    /// when proof logging is enabled via `enable_proof_logging()`.
    /// The final entry is always the empty clause `[]` on UNSAT.
    proof_log: Option<Vec<Vec<i32>>>,
}

impl CdclSolver {
    pub fn new(num_vars: u32) -> Self {
        CdclSolver {
            num_vars,
            assignment: Assignment::new(num_vars),
            db: ClauseDb::new(),
            watches: WatchList::new(num_vars),
            activity: vec![0.0; num_vars as usize + 1],
            activity_inc: 1.0,
            activity_decay: 0.95,
            luby_u: 1,
            luby_v: 1,
            luby_scale: 100,
            next_restart_conflicts: 100,
            learnt_limit: 2000,
            learnt_limit_inc: 1.1,
            conflicts: 0,
            propagations: 0,
            restarts: 0,
            decisions: 0,
            base_level: 0,
            assumption_floor: 0,
            learned_outbox: Vec::new(),
            proof_log: None,
        }
    }

    /// Number of variables in the formula (index 0 is unused).
    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }

    // -----------------------------------------------------------------------
    // Proof logging (DRUP)
    // -----------------------------------------------------------------------

    /// Enable DRUP proof logging. Must be called before `solve()`.
    /// Each learned clause — and the final empty clause on UNSAT — will be
    /// appended to the internal log.
    pub fn enable_proof_logging(&mut self) {
        self.proof_log = Some(Vec::new());
    }

    /// Consume and return the proof log (DRUP format): each inner `Vec<i32>`
    /// is one clause in DIMACS literal encoding. The last entry is `[]` (the
    /// empty clause) if the result was UNSAT. Returns `None` if logging was
    /// not enabled.
    pub fn take_proof_log(&mut self) -> Option<Vec<Vec<i32>>> {
        self.proof_log.take()
    }

    /// Convert a slice of `Literal`s to DIMACS integer representation.
    fn lits_to_dimacs(lits: &[Literal]) -> Vec<i32> {
        lits.iter()
            .map(|l| {
                let v = l.var() as i32;
                if l.is_positive() { v } else { -v }
            })
            .collect()
    }

    /// Append a clause to the proof log (if logging is enabled).
    fn log_proof_clause(&mut self, lits: &[Literal]) {
        if let Some(log) = &mut self.proof_log {
            log.push(Self::lits_to_dimacs(lits));
        }
    }

    /// Append the empty clause to the proof log (signals UNSAT).
    fn log_proof_empty(&mut self) {
        if let Some(log) = &mut self.proof_log {
            log.push(Vec::new());
        }
    }

    // -----------------------------------------------------------------------
    // Clause addition
    // -----------------------------------------------------------------------

    /// Add a problem clause. Unit clauses are enqueued immediately at level 0.
    pub fn add_clause(&mut self, lits: &[Literal]) {
        match lits.len() {
            0 => {
                // Empty clause → immediate UNSAT; store a sentinel for the solve loop.
                self.db.set_empty_clause();
            }
            1 => {
                // Unit clause: assign at level 0 if unassigned, conflict if false.
                let lit = lits[0];
                match self.assignment.literal_value(lit) {
                    Value::True => {} // already satisfied
                    Value::False => {
                        self.db.set_empty_clause();
                    }
                    Value::Undef => {
                        self.assignment.assign(lit, 0, ClauseRef::DECISION.0);
                    }
                }
            }
            _ => {
                let sv: SmallVec<[Literal; 4]> = lits.iter().copied().collect();
                let cr = self.db.add(Clause::new(sv, false));
                // Convention: watches[lit.raw()] is checked when lit is propagated (True).
                // A clause with watches w0,w1 is stored under (¬w0) and (¬w1).
                // When ¬w0 is assigned (making w0 false), we check watches[(¬w0).raw()].
                // Equivalently: when literal p is assigned, check watches[p.raw()].
                // Storage: watches[(¬w0).raw()] and watches[(¬w1).raw()].
                let w0 = lits[0].negate();
                let w1 = lits[1].negate();
                self.watches.watch(w0, cr);
                self.watches.watch(w1, cr);
            }
        }
    }

    // -----------------------------------------------------------------------
    // Main solve loop
    // -----------------------------------------------------------------------

    /// Solve under optional additional `assumptions`. Returns after at most
    /// `max_conflicts` conflicts (use `u64::MAX` for unlimited).
    ///
    /// The assumption literals are pinned at the bottom of the decision stack:
    /// backjumps and restarts never go below `base_level`, so assumptions stay
    /// assigned for the whole call and are never re-decided with a flipped
    /// polarity. On exit the solver is left back at `base_level`, so a fresh
    /// `solve` with a different assumption set starts clean.
    pub fn solve(&mut self, assumptions: &[Literal], max_conflicts: u64) -> SolveResult {
        self.solve_inner(assumptions, max_conflicts, None)
    }

    /// Solve under optional additional `assumptions`, bounded by both a
    /// conflict budget and (optionally) a wall-clock deadline. Returns
    /// `SolveResult::Unknown` as soon as the deadline passes (the benchmark
    /// runner uses this to honor each problem's `timeout_secs`).
    pub fn solve_with_deadline(
        &mut self,
        assumptions: &[Literal],
        max_conflicts: u64,
        deadline: Option<Instant>,
    ) -> SolveResult {
        self.solve_inner(assumptions, max_conflicts, deadline)
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

        self.base_level = self.assignment.current_level();

        // Settle all level-0 propagation *before* pushing assumptions.
        //
        // `add_clause` assigns unit clauses immediately but does not run BCP
        // on their consequences. If that work is deferred to the main loop
        // (which runs at a higher decision level once assumptions are pushed),
        // a clause can be woken late — after its watched literals were both
        // falsified at levels below the current one. BCP would then report a
        // conflict whose clause contains NO literal at the current level,
        // which breaks the 1-UIP invariant in `analyze`. Running propagation
        // to a fixed point at level 0 first makes every assumption-level wake
        // trigger on a literal assigned at the current level, restoring the
        // invariant.
        if self.base_level == 0 && self.propagate().is_some() {
            self.assignment.backtrack_to(0);
            return SolveResult::Unsat;
        }

        // Push assumptions as decisions.
        let mut assumptions_pushed = 0u32;
        for &lit in assumptions {
            match self.assignment.literal_value(lit) {
                Value::True => {} // already implied
                Value::False => {
                    self.assignment.backtrack_to(self.base_level);
                    return SolveResult::Unsat;
                }
                Value::Undef => {
                    self.assignment.new_decision_level();
                    self.assignment.assign(
                        lit,
                        self.assignment.current_level(),
                        ClauseRef::DECISION.0,
                    );
                    self.decisions += 1;
                    assumptions_pushed += 1;
                }
            }
        }
        self.assumption_floor = if assumptions_pushed > 0 {
            self.base_level + assumptions_pushed
        } else {
            self.base_level
        };

        let conflicts_at_entry = self.conflicts;

        let result = loop {
            if let Some(conflict_cr) = self.propagate() {
                if self.assignment.current_level() == self.base_level {
                    // Conflict at the assumption boundary: the problem under
                    // the current assumptions (or the whole problem) is UNSAT.
                    self.log_proof_empty();
                    break SolveResult::Unsat;
                }
                self.conflicts += 1;
                if self.conflicts - conflicts_at_entry > max_conflicts {
                    break SolveResult::Unknown;
                }

                let (learnt, mut backjump_level) = self.analyze(conflict_cr);
                // Never backjump below the assumption levels.
                if backjump_level < self.assumption_floor {
                    backjump_level = self.assumption_floor;
                }
                self.assignment.backtrack_to(backjump_level);
                self.decay_activities();

                // learnt[0] is the asserting literal, unit at `backjump_level`.
                // It may already be assigned at that level (typically because
                // the conflict led back into the assumption region). If it is
                // already False, the assumptions themselves are contradictory:
                // every literal of the (valid) learnt clause is then False at
                // `backjump_level`, so return UNSAT. If already True the
                // clause is satisfied at that level and needs no assertion.
                match self.assignment.literal_value(learnt[0]) {
                    Value::True => {}
                    Value::False => {
                        self.log_proof_empty();
                        break SolveResult::Unsat;
                    }
                    Value::Undef => {
                        self.log_proof_clause(&learnt);
                        if learnt.len() == 1 {
                            // Unit learnings are asserted directly (never added
                            // to the clause DB), but they are the most potent
                            // exportable knowledge — stage them for AKX export.
                            self.learned_outbox.push((learnt.to_vec(), 1));
                            self.assignment.assign(
                                learnt[0],
                                backjump_level,
                                ClauseRef::DECISION.0,
                            );
                        } else {
                            let cr = self.add_learned_clause(&learnt);
                            self.assignment.assign(learnt[0], backjump_level, cr.0);
                        }
                    }
                }

                self.maybe_restart();
                self.maybe_reduce_db();
            } else {
                // No conflict. Decide or return SAT.
                if self.conflicts >= self.next_restart_conflicts {
                    self.do_restart();
                } else if let Some(lit) = self.pick_branch() {
                    self.assignment.new_decision_level();
                    self.assignment.assign(
                        lit,
                        self.assignment.current_level(),
                        ClauseRef::DECISION.0,
                    );
                    self.decisions += 1;
                } else {
                    // All variables assigned — extract model.
                    break SolveResult::Sat(self.extract_model());
                }
            }

            if self.conflicts - conflicts_at_entry > max_conflicts {
                break SolveResult::Unknown;
            }
            if deadline.is_some_and(|d| Instant::now() >= d) {
                break SolveResult::Unknown;
            }
        };

        // Leave the solver clean for the next call.
        self.assignment.backtrack_to(self.base_level);
        result
    }

    /// Import a batch of learned clauses (e.g. from AKX) into the clause
    /// database.
    ///
    /// This is the M1 answer to research gate G0: mid-search importing needs
    /// **no structural changes** to the trail or clause database — imported
    /// clauses are integrated at decision level 0, which is where every
    /// worker returns at a restart/backjump boundary anyway. The worker
    /// runtime must call this only when the solver is (or has just been
    /// returned to) level 0, matching the import-point protocol in the spec.
    ///
    /// Returns the number of clauses added.
    pub fn import_clauses(&mut self, clauses: &[Vec<Literal>]) -> usize {
        self.assignment.backtrack_to(0);
        self.base_level = 0;
        for lits in clauses {
            self.add_clause(lits);
        }
        clauses.len()
    }

    // -----------------------------------------------------------------------
    // Boolean Constraint Propagation
    // -----------------------------------------------------------------------

    /// Run BCP to a fixed point. Returns the conflicting ClauseRef, if any.
    ///
    /// Watch convention (MiniSAT):
    ///   watches[p.raw()] = clauses woken when literal p is assigned True.
    ///   Each clause stores its two watched literals as w0, w1.
    ///   It is added under (¬w0).raw() and (¬w1).raw().
    ///   When literal q = ¬w0 is assigned True, w0 is False; watches[q.raw()] is checked.
    fn propagate(&mut self) -> Option<ClauseRef> {
        while self.assignment.prop_head < self.assignment.trail().len() {
            let p = self.assignment.trail()[self.assignment.prop_head];
            self.assignment.prop_head += 1;
            self.propagations += 1;

            // p was just assigned True, so ¬p is False.
            // All clauses watching ¬p (stored under p.raw()) need checking.
            // We must iterate carefully because we may remove items mid-iteration.
            let mut idx = 0;
            'clause_loop: loop {
                let cr = {
                    let list = self.watches.get(p);
                    if idx >= list.len() {
                        break 'clause_loop;
                    }
                    list[idx]
                };

                // Ensure watches[0] is the "other" literal (not ¬p).
                // By convention, the literal that triggered the wake is the one
                // that became False. In our clause, we stored under ¬w, so the
                // watch that became False is p.negate() = ¬p.
                // Rearrange so that clause[1] is the False watch, clause[0] is other.
                {
                    let clause = self.db.get_mut(cr);
                    if clause.lits[0].negate() == p {
                        clause.lits.swap(0, 1);
                    }
                    // Now lits[1].negate() == p, i.e., lits[1] is the watch that became False.
                }

                let other_watch = self.db.get(cr).lits[0];

                // If the other watch is already True, the clause is satisfied; keep watch.
                if self.assignment.literal_value(other_watch) == Value::True {
                    idx += 1;
                    continue;
                }

                // Try to find a new non-False literal to replace lits[1].
                let n = self.db.get(cr).lits.len();
                let mut found_new = false;
                for k in 2..n {
                    let cand = self.db.get(cr).lits[k];
                    if self.assignment.literal_value(cand) != Value::False {
                        // Swap candidate to position 1 and update watches.
                        self.db.get_mut(cr).lits.swap(1, k);
                        let new_watch = self.db.get(cr).lits[1];
                        // Remove this clause from watches[p] and add to watches[¬new_watch].
                        self.watches.remove(p, cr);
                        self.watches.watch(new_watch.negate(), cr);
                        found_new = true;
                        // Don't advance idx since we removed the item at idx.
                        break;
                    }
                }

                if found_new {
                    continue;
                }

                // No new watch found. lits[0] is the only hope.
                match self.assignment.literal_value(other_watch) {
                    Value::False => {
                        // Conflict.
                        return Some(cr);
                    }
                    Value::Undef => {
                        // Unit propagation: force other_watch.
                        self.assignment
                            .assign(other_watch, self.assignment.current_level(), cr.0);
                        idx += 1;
                    }
                    Value::True => unreachable!("handled above"),
                }
            }
        }
        None
    }

    // -----------------------------------------------------------------------
    // 1-UIP Conflict Analysis
    // -----------------------------------------------------------------------

    /// Analyse `conflict_cr` and return (learnt_clause, backjump_level).
    ///
    /// The returned clause has the asserting literal at index 0 and the highest
    /// second-level literal (if any) at index 1 — ready for watched-literal setup.
    fn analyze(&mut self, conflict_cr: ClauseRef) -> (SmallVec<[Literal; 8]>, u32) {
        let current_level = self.assignment.current_level();

        // seen[var] = true once we've enqueued var in the analysis.
        let mut seen = vec![false; self.num_vars as usize + 1];
        // Literals in the learned clause from levels < current_level.
        let mut learnt: SmallVec<[Literal; 8]> = SmallVec::new();
        // Number of current-level vars still to resolve.
        let mut counter = 0usize;

        // Process the initial conflict clause.
        self.process_reason_into(
            conflict_cr,
            current_level,
            &mut seen,
            &mut learnt,
            &mut counter,
            None,
        );

        // Walk the trail backward to find the 1-UIP.
        // Copy the trail into a local Vec to avoid borrow conflicts with self.
        let trail_snapshot: Vec<Literal> = self.assignment.trail().to_vec();
        let mut trail_pos = trail_snapshot.len();
        let uip = loop {
            // Scan backward for the next seen variable.
            loop {
                if trail_pos == 0 {
                    // Invariant: a conflict clause always contains at least one
                    // literal assigned at the current decision level, so the
                    // 1-UIP is always found before we walk off the start.
                    unreachable!("1-UIP analysis walked past the start of the trail");
                }
                trail_pos -= 1;
                if seen[trail_snapshot[trail_pos].var() as usize] {
                    break;
                }
            }

            let lit = trail_snapshot[trail_pos];
            let var = lit.var();
            seen[var as usize] = false; // consume

            let lvl = self.assignment.level_of(var);
            // `counter` counts current-level variables that are still waiting
            // to be resolved. Lower-level literals were pushed straight into
            // `learnt` by `process_reason_into` and need no resolution, but
            // they are also marked `seen` — so skip them here without touching
            // `counter` (this is the 1-UIP bookkeeping invariant).
            if lvl != current_level {
                continue;
            }

            counter -= 1;
            if counter == 0 {
                break lit;
            }

            // Expand the antecedent of this literal.
            let reason_raw = self.assignment.reason_of(var);
            let reason_cr = ClauseRef(reason_raw);
            if !reason_cr.is_sentinel() {
                self.process_reason_into(
                    reason_cr,
                    current_level,
                    &mut seen,
                    &mut learnt,
                    &mut counter,
                    Some(var),
                );
            }
        };

        // learnt clause = [¬UIP, ...lower-level literals...]
        // ¬UIP is the asserting literal (will be unit at backjump level).
        let asserting = uip.negate();

        // Backjump level = max level among learnt[1..].
        // Also move the highest-level literal to index 1 (for watched-literal setup).
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

        // Construct final clause: asserting literal first, then learnt.
        let mut clause: SmallVec<[Literal; 8]> = SmallVec::new();
        clause.push(asserting);
        clause.extend_from_slice(&learnt);

        (clause, backjump_level)
    }

    /// Helper: visit all literals in `cr`'s clause and classify them.
    ///
    /// `resolving_var` is the variable whose antecedent this clause is; that
    /// variable's literal appears in the clause as the derived literal and must
    /// be skipped so it is not re-seen (1-UIP resolution). `None` for the
    /// initial conflict clause, which is processed in full.
    fn process_reason_into(
        &mut self,
        cr: ClauseRef,
        current_level: u32,
        seen: &mut [bool],
        learnt: &mut SmallVec<[Literal; 8]>,
        counter: &mut usize,
        resolving_var: Option<Var>,
    ) {
        // Collect literals to avoid borrow conflicts.
        let lits: SmallVec<[Literal; 8]> = self.db.get(cr).lits.iter().copied().collect();
        for lit in lits {
            let var = lit.var();
            if Some(var) == resolving_var {
                continue;
            }
            if seen[var as usize] {
                continue;
            }
            let lvl = self.assignment.level_of(var);
            if lvl == 0 {
                continue;
            } // level-0 facts need no explanation
            seen[var as usize] = true;
            self.bump_var_activity(var);
            if lvl == current_level {
                *counter += 1;
            } else {
                // Lower level: goes into the learned clause as-is.
                // This literal is False at the current assignment and will remain
                // False after backjumping (it was assigned at a level <= backjump).
                learnt.push(lit);
            }
        }
    }

    // -----------------------------------------------------------------------
    // Learned clause management
    // -----------------------------------------------------------------------

    fn add_learned_clause(&mut self, lits: &[Literal]) -> ClauseRef {
        debug_assert!(lits.len() >= 2);
        let lbd = self.compute_lbd(lits);
        let sv: SmallVec<[Literal; 4]> = lits.iter().copied().collect();
        let mut clause = Clause::new(sv, true);
        clause.lbd = lbd;

        let cr = self.db.add(clause);
        // Watch lits[0] and lits[1] (lits[0] will be assigned right after this call).
        self.watches.watch(lits[0].negate(), cr);
        self.watches.watch(lits[1].negate(), cr);
        // Stage for AKX export (drained by the Reasoner between solve calls).
        self.learned_outbox.push((lits.to_vec(), lbd));
        cr
    }

    /// Drain the learned clauses (and their LBD scores) produced since the
    /// last call. Cleared by this method; used by the Reasoner to build
    /// exportable AKX clause knowledge.
    pub fn drain_learned(&mut self) -> Vec<(Vec<Literal>, u32)> {
        std::mem::take(&mut self.learned_outbox)
    }

    fn compute_lbd(&self, lits: &[Literal]) -> u32 {
        let mut levels: SmallVec<[u32; 8]> = SmallVec::new();
        for lit in lits {
            let lvl = self.assignment.level_of(lit.var());
            if !levels.contains(&lvl) {
                levels.push(lvl);
            }
        }
        levels.len() as u32
    }

    fn maybe_reduce_db(&mut self) {
        let learnt_count = self.db.learnt_count();
        if learnt_count <= self.learnt_limit {
            return;
        }

        self.db.reduce_learned(|cr, c| {
            // A clause is "locked" while it is still the reason of its first
            // literal (the watch invariant places the propagated literal at
            // lits[0]). Such clauses are antecedents still on the trail;
            // deleting one would leave analyze() dereferencing a dead
            // ClauseRef. The flag is never maintained eagerly; recomputed here.
            c.lbd > 2 && self.assignment.reason_of(c.lits[0].var()) != cr.0
        });
        // Dropped clauses leave stale entries in the two-watched-literal index;
        // propagate() would panic on a deleted ClauseRef. Rebuild the watch
        // lists from the surviving clauses (MiniSat-style reduceDB).
        self.db.rebuild_watches(&mut self.watches);
        self.learnt_limit = (self.learnt_limit as f64 * self.learnt_limit_inc) as usize;
    }

    // -----------------------------------------------------------------------
    // VSIDS
    // -----------------------------------------------------------------------

    fn bump_var_activity(&mut self, var: Var) {
        self.activity[var as usize] += self.activity_inc;
        if self.activity[var as usize] > 1e100 {
            // Rescale to prevent float overflow.
            for a in self.activity.iter_mut() {
                *a *= 1e-100;
            }
            self.activity_inc *= 1e-100;
        }
    }

    fn decay_activities(&mut self) {
        self.activity_inc /= self.activity_decay;
    }

    // -----------------------------------------------------------------------
    // Branching
    // -----------------------------------------------------------------------

    /// VSIDS: pick the highest-activity unassigned variable, positive polarity.
    fn pick_branch(&self) -> Option<Literal> {
        (1..=self.num_vars)
            .filter(|&v| !self.assignment.is_assigned(v))
            .max_by(|&a, &b| {
                self.activity[a as usize]
                    .partial_cmp(&self.activity[b as usize])
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
            .map(Literal::positive)
    }

    // -----------------------------------------------------------------------
    // Restarts (Luby schedule)
    // -----------------------------------------------------------------------

    fn maybe_restart(&mut self) {
        if self.conflicts >= self.next_restart_conflicts {
            self.do_restart();
        }
    }

    fn do_restart(&mut self) {
        self.assignment.backtrack_to(self.assumption_floor);
        self.restarts += 1;
        let next = luby_next(&mut self.luby_u, &mut self.luby_v);
        self.next_restart_conflicts = self.conflicts + next * self.luby_scale;
    }

    // -----------------------------------------------------------------------
    // Model extraction
    // -----------------------------------------------------------------------

    fn extract_model(&self) -> Model {
        let mut values = vec![false; self.num_vars as usize + 1];
        for var in 1..=self.num_vars {
            values[var as usize] = matches!(self.assignment.value_of(var), Value::True);
        }
        Model::new(values)
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
                    if lit > 0 {
                        val
                    } else {
                        !val
                    }
                });
                if !sat {
                    continue 'outer;
                }
            }
            return true; // all clauses satisfied
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

    /// Simple LCG for reproducible pseudo-random tests.
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

    /// Broader oracle sweep: several variable counts, a range of clause counts,
    /// and many seeds. For every SAT result the returned model must be a
    /// complete assignment that satisfies all clauses.
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
                        SolveResult::Unknown => {
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
        // (x1 ∨ x2) with assumption ¬x2 forces x1 in any model.
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
        // Unit clause (x1) contradicts assumption ¬x1.
        let mut s = dimacs_to_solver(1, &[vec![1]]);
        assert_eq!(
            s.solve(&[Literal::negative(1)], u64::MAX),
            SolveResult::Unsat
        );
    }

    /// Brute-force oracle for solving under a literal assumption set.
    fn brute_force_assumptions(
        num_vars: u32,
        clauses: &[Vec<i32>],
        assumptions: &[Literal],
    ) -> bool {
        'outer: for mask in 0u64..(1u64 << num_vars) {
            for &a in assumptions {
                // Bit mask is 0-indexed; DIMACS variables are 1-indexed.
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
                    if lit > 0 {
                        val
                    } else {
                        !val
                    }
                });
                if !sat {
                    continue 'outer;
                }
            }
            return true;
        }
        false
    }

    /// Random assumptions must agree with the brute-force oracle, and any SAT
    /// model must satisfy the assumptions and all clauses.
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
                SolveResult::Unknown => panic!("UNKNOWN for small formula"),
            };
            assert_eq!(
                bf, cdcl,
                "mismatch with assumptions {assumptions:?} on {clauses:?}"
            );
        }
    }

    /// Incremental use: several `solve` calls with different assumption sets
    /// on one solver must give the same answers as independent solves.
    #[test]
    fn repeated_assumption_solves_are_independent() {
        // (x1 ∨ x2) ∧ (¬x1 ∨ x3)
        let clauses = vec![vec![1, 2], vec![-1, 3]];
        let mut s = dimacs_to_solver(3, &clauses);

        // Under ¬x2: x1 forced; then x3 forced.
        match s.solve(&[Literal::negative(2)], u64::MAX) {
            SolveResult::Sat(m) => {
                assert!(m.satisfies(Literal::positive(1)));
                assert!(m.satisfies(Literal::positive(3)));
            }
            other => panic!("expected SAT, got {other:?}"),
        }

        // Under ¬x1 ∧ ¬x2: (x1∨x2) has both literals false.
        assert_eq!(
            s.solve(&[Literal::negative(1), Literal::negative(2)], u64::MAX),
            SolveResult::Unsat
        );

        // Back to a satisfiable assumption set; must still work after UNSAT.
        match s.solve(&[Literal::positive(3)], u64::MAX) {
            SolveResult::Sat(m) => {
                assert!(m.satisfies(Literal::positive(3)));
                assert!(m.verify_dimacs(&clauses));
            }
            other => panic!("expected SAT, got {other:?}"),
        }
    }

    /// G0 gate: imported clauses integrate into a live solver at level 0 with
    /// no structural changes to the trail or clause database.
    #[test]
    fn import_clauses_mid_search_g0() {
        // (¬x1 ∨ ¬x2 ∨ ¬x3) is SAT and solved without any conflicts, leaving
        // the solver in a clean, re-usable state.
        let mut s = dimacs_to_solver(3, &[vec![-1, -2, -3]]);
        assert!(matches!(s.solve(&[], 0), SolveResult::Sat(_)));

        // Import unit clauses x1, x2, x3 mid-solve — the clause is falsified.
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
    fn zero_budget_returns_unknown() {
        let (nv, clauses) = pigeonhole(3, 2);
        let mut s = dimacs_to_solver(nv, &clauses);
        assert_eq!(s.solve(&[], 0), SolveResult::Unknown);
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
            SolveResult::Unknown => panic!("expected a decision for pigeonhole(5,5)"),
        }
    }

    // -----------------------------------------------------------------------
    // Pigeonhole: pigeons(n) = n+1 pigeons in n holes — classic hard UNSAT
    // -----------------------------------------------------------------------

    /// Pigeonhole principle: variable(p, h) = pigeon p in hole h.
    fn pigeonhole(pigeons: u32, holes: u32) -> (u32, Vec<Vec<i32>>) {
        let var = |p: u32, h: u32| -> i32 { (p * holes + h + 1) as i32 };
        let num_vars = pigeons * holes;
        let mut clauses: Vec<Vec<i32>> = Vec::new();

        // Each pigeon must be in at least one hole.
        for p in 0..pigeons {
            clauses.push((0..holes).map(|h| var(p, h)).collect());
        }
        // No two pigeons share a hole.
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

    /// Regression (hard instance panic): learnt-clause reduction must neither
    /// delete a clause still used as a trail reason nor leave stale entries in
    /// the two-watched-literal index. PHP(8,7) is large enough to trigger
    /// several reductions before the root conflict is found.
    #[test]
    fn reduction_keeps_reasons_and_watches_live() {
        let (nv, clauses) = pigeonhole(8, 7);
        let mut s = dimacs_to_solver(nv, &clauses);
        // Collapse the learnt limit so reduction fires almost immediately.
        s.learnt_limit = 4;
        assert_eq!(s.solve(&[], u64::MAX), SolveResult::Unsat);
    }

    /// A wall-clock deadline must stop the search with `Unknown` even when the
    /// conflict budget is unlimited.
    #[test]
    fn deadline_returns_unknown_with_propagation() {
        let (nv, clauses) = pigeonhole(10, 9);
        let mut s = dimacs_to_solver(nv, &clauses);
        let deadline = std::time::Instant::now()
            .checked_add(std::time::Duration::from_millis(30))
            .unwrap();
        match s.solve_with_deadline(&[], u64::MAX, Some(deadline)) {
            SolveResult::Unknown => {} // expected: too hard for 30ms
            SolveResult::Unsat => {}   // allowed if the search completed
            SolveResult::Sat(_) => panic!("PHP(10,9) is UNSAT"),
        }
    }
}
