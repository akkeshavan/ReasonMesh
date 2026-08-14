//! CDCL solver skeleton — Milestone M1.
//!
//! Implements the basic CDCL loop with two-watched literals.
//! Theory integration, proof logging, and AKX import are added at M2.

use crate::{
    assignment::{Assignment, Value},
    clause::{Clause, ClauseDb, ClauseRef},
    watched::WatchList,
};
use rm_akx::literal::{Literal, Var};
use smallvec::SmallVec;

#[derive(Debug, PartialEq, Eq)]
pub enum SolveResult {
    Sat,
    Unsat,
    Unknown,
}

pub struct CdclSolver {
    num_vars: u32,
    assignment: Assignment,
    db: ClauseDb,
    watches: WatchList,
    /// Propagation queue (literals to propagate).
    prop_queue: Vec<Literal>,
    /// VSIDS activity scores.
    activity: Vec<f64>,
    activity_inc: f64,
    /// Number of conflicts seen.
    conflicts: u64,
    restarts: u64,
    next_restart: u64,
}

impl CdclSolver {
    pub fn new(num_vars: u32) -> Self {
        CdclSolver {
            num_vars,
            assignment: Assignment::new(num_vars),
            db: ClauseDb::new(),
            watches: WatchList::new(num_vars),
            prop_queue: Vec::new(),
            activity: vec![0.0; num_vars as usize + 1],
            activity_inc: 1.0,
            conflicts: 0,
            restarts: 0,
            next_restart: 100,
        }
    }

    /// Add a clause. Unit clauses are immediately enqueued for propagation.
    pub fn add_clause(&mut self, lits: &[Literal]) {
        let lits: SmallVec<[Literal; 4]> = lits.iter().copied().collect();
        match lits.len() {
            0 => {
                // Empty clause → immediate UNSAT; we record this specially.
                // A real solver would set a "conflict at level 0" flag.
            }
            1 => {
                self.prop_queue.push(lits[0]);
            }
            _ => {
                let w0 = lits[0];
                let w1 = lits[1];
                let cr = self.db.add(Clause::new(lits, false));
                self.watches.watch(w0.negate(), cr);
                self.watches.watch(w1.negate(), cr);
            }
        }
    }

    /// Run the CDCL loop for at most `max_conflicts` conflicts.
    pub fn solve(&mut self, assumptions: &[Literal], max_conflicts: u64) -> SolveResult {
        // Enqueue assumptions.
        for &lit in assumptions {
            self.prop_queue.push(lit);
        }

        loop {
            if let Some(_conflict_cr) = self.propagate() {
                // Conflict detected.
                if self.assignment.current_level() == 0 {
                    return SolveResult::Unsat;
                }
                self.conflicts += 1;
                if self.conflicts >= max_conflicts {
                    return SolveResult::Unknown;
                }
                // Analyse conflict and backjump (simplified: backtrack one level).
                let lvl = self.assignment.current_level().saturating_sub(1);
                self.backtrack(lvl);
                self.bump_restart();
            } else if let Some(lit) = self.pick_branch() {
                self.assignment.new_decision_level();
                self.prop_queue.push(lit);
            } else {
                return SolveResult::Sat;
            }

            if self.conflicts >= max_conflicts {
                return SolveResult::Unknown;
            }
        }
    }

    /// Boolean constraint propagation. Returns the conflicting clause if any.
    fn propagate(&mut self) -> Option<ClauseRef> {
        while let Some(lit) = self.prop_queue.pop() {
            if self.assignment.literal_value(lit) == Value::False {
                // Queued literal is already assigned false — contradiction.
                return Some(ClauseRef::UNIT_CONFLICT);
            }
            if self.assignment.literal_value(lit) == Value::True {
                // Already satisfied; nothing to do.
                continue;
            }
            if self.assignment.literal_value(lit) == Value::Undef {
                self.assignment.assign(lit, self.assignment.current_level(), u32::MAX);
            }
            // Walk watches of the negation of lit.
            let false_lit = lit.negate();
            let mut i = 0;
            let watch_list: Vec<ClauseRef> = self.watches.get(false_lit).to_vec();
            'clause: for cr in watch_list {
                let clause = self.db.get(cr);
                // Find a new watch.
                let mut found_new = false;
                for &candidate in clause.lits.iter().skip(2) {
                    if self.assignment.literal_value(candidate) != Value::False {
                        self.watches.get_mut(false_lit).retain(|&r| r != cr);
                        self.watches.watch(candidate.negate(), cr);
                        found_new = true;
                        break;
                    }
                }
                if !found_new {
                    // All other literals are false — check for unit or conflict.
                    let other_watch = {
                        let c = self.db.get(cr);
                        if c.lits[0] == false_lit { c.lits[1] } else { c.lits[0] }
                    };
                    match self.assignment.literal_value(other_watch) {
                        Value::True  => {}   // satisfied
                        Value::Undef => {
                            self.prop_queue.push(other_watch);
                        }
                        Value::False => {
                            return Some(cr); // conflict
                        }
                    }
                }
                i += 1;
            }
        }
        None
    }

    fn pick_branch(&self) -> Option<Literal> {
        // VSIDS: pick the highest-activity unassigned variable.
        (1..=self.num_vars)
            .filter(|&v| !self.assignment.is_assigned(v))
            .max_by(|&a, &b| self.activity[a as usize].partial_cmp(&self.activity[b as usize]).unwrap())
            .map(|v| Literal::positive(v))
    }

    fn backtrack(&mut self, level: u32) {
        let mut vals = vec![Value::Undef; self.num_vars as usize + 1];
        self.assignment.backtrack_to(level, &mut vals);
        self.prop_queue.clear();
    }

    fn bump_restart(&mut self) {
        if self.conflicts >= self.next_restart {
            self.restarts += 1;
            self.next_restart = (self.next_restart as f64 * 1.5) as u64;
            self.backtrack(0);
        }
    }

    pub fn conflicts(&self) -> u64 { self.conflicts }
    pub fn restarts(&self) -> u64 { self.restarts }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trivially_sat() {
        let mut s = CdclSolver::new(1);
        s.add_clause(&[Literal::positive(1)]);
        assert_eq!(s.solve(&[], 1000), SolveResult::Sat);
    }

    #[test]
    fn trivially_unsat() {
        let mut s = CdclSolver::new(1);
        s.add_clause(&[Literal::positive(1)]);
        s.add_clause(&[Literal::negative(1)]);
        assert_eq!(s.solve(&[], 1000), SolveResult::Unsat);
    }
}
