use rm_akx::literal::Literal;
use smallvec::SmallVec;

/// A clause in the database.
#[derive(Clone, Debug)]
pub struct Clause {
    pub lits: SmallVec<[Literal; 4]>,
    pub lbd: u32,
    pub learnt: bool,
    /// Activity counter for deletion heuristic.
    pub activity: f32,
    /// True if lits[0] is currently the reason for a propagation; must not delete.
    pub locked: bool,
}

impl Clause {
    pub fn new(lits: SmallVec<[Literal; 4]>, learnt: bool) -> Self {
        Clause {
            lits,
            lbd: 0,
            learnt,
            activity: 0.0,
            locked: false,
        }
    }
    pub fn len(&self) -> usize {
        self.lits.len()
    }
    pub fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }
}

/// Index into the clause database.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ClauseRef(pub u32);

impl ClauseRef {
    /// Antecedent for a decision literal.
    pub const DECISION: ClauseRef = ClauseRef(u32::MAX);
    /// Sentinel used for a conflict from a queued unit literal with no clause.
    pub const UNIT_CONFLICT: ClauseRef = ClauseRef(u32::MAX - 1);

    pub fn is_decision(self) -> bool {
        self.0 == u32::MAX
    }
    /// True for any sentinel value (DECISION or UNIT_CONFLICT).
    pub fn is_sentinel(self) -> bool {
        self.0 >= u32::MAX - 1
    }
}

/// Storage for all clauses (problem + learned).
pub struct ClauseDb {
    clauses: Vec<Option<Clause>>,
    learnt_count: usize,
    has_empty: bool,
}

impl ClauseDb {
    pub fn new() -> Self {
        ClauseDb {
            clauses: Vec::new(),
            learnt_count: 0,
            has_empty: false,
        }
    }

    pub fn add(&mut self, clause: Clause) -> ClauseRef {
        if clause.learnt {
            self.learnt_count += 1;
        }
        let id = ClauseRef(self.clauses.len() as u32);
        self.clauses.push(Some(clause));
        id
    }

    pub fn get(&self, r: ClauseRef) -> &Clause {
        self.clauses[r.0 as usize].as_ref().expect("clause deleted")
    }

    pub fn get_mut(&mut self, r: ClauseRef) -> &mut Clause {
        self.clauses[r.0 as usize].as_mut().expect("clause deleted")
    }

    pub fn get_ref(&self, idx: usize) -> Option<&Clause> {
        self.clauses.get(idx).and_then(|c| c.as_ref())
    }

    pub fn set_empty_clause(&mut self) {
        self.has_empty = true;
    }

    pub fn has_empty_clause(&self) -> bool {
        self.has_empty
    }

    pub fn learnt_count(&self) -> usize {
        self.learnt_count
    }

    /// Remove learned clauses where `should_delete(cr, clause)` is true.
    /// `should_delete` receives the clause ref so the caller can check whether
    /// the clause is still the reason of its first literal (locked).
    /// The caller must rebuild the watch list after calling this.
    pub fn reduce_learned(&mut self, should_delete: impl Fn(ClauseRef, &Clause) -> bool) {
        for (idx, slot) in self.clauses.iter_mut().enumerate() {
            if let Some(c) = slot {
                if c.learnt && should_delete(ClauseRef(idx as u32), c) {
                    *slot = None;
                    self.learnt_count -= 1;
                }
            }
        }
    }
}

/// Iterate the surviving (non-deleted) clauses and re-register their two
/// watched literals, exactly as `CdclSolver::add_clause` does. Must be called
/// after `ClauseDb::reduce_learned` so the watch list never references a
/// deleted clause.
impl ClauseDb {
    pub fn rebuild_watches(&self, watches: &mut super::watched::WatchList) {
        watches.clear();
        for (idx, slot) in self.clauses.iter().enumerate() {
            if let Some(c) = slot {
                watches.watch(c.lits[0].negate(), ClauseRef(idx as u32));
                watches.watch(c.lits[1].negate(), ClauseRef(idx as u32));
            }
        }
    }
}

impl Default for ClauseDb {
    fn default() -> Self {
        Self::new()
    }
}
