use rm_akx::literal::Literal;
use smallvec::SmallVec;

/// A clause stored in the clause database.
#[derive(Clone, Debug)]
pub struct Clause {
    /// Literals; watched literals are always at indices 0 and 1.
    pub lits: SmallVec<[Literal; 4]>,
    pub lbd: u32,
    pub learnt: bool,
    /// Number of times this clause was used in unit propagation.
    pub activity: f32,
}

impl Clause {
    pub fn new(lits: impl Into<SmallVec<[Literal; 4]>>, learnt: bool) -> Self {
        Clause { lits: lits.into(), lbd: 0, learnt, activity: 0.0 }
    }

    pub fn len(&self) -> usize { self.lits.len() }
    pub fn is_empty(&self) -> bool { self.lits.is_empty() }
}

/// Index into the clause database.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ClauseRef(pub u32);

impl ClauseRef {
    pub const DECISION: ClauseRef = ClauseRef(u32::MAX);
    /// Conflict from a queued unit literal with no associated clause.
    pub const UNIT_CONFLICT: ClauseRef = ClauseRef(u32::MAX - 1);
    pub fn is_decision(self) -> bool { self.0 == u32::MAX }
    pub fn is_sentinel(self) -> bool { self.0 >= u32::MAX - 1 }
}

/// Storage for all clauses (problem + learned).
pub struct ClauseDb {
    clauses: Vec<Clause>,
}

impl ClauseDb {
    pub fn new() -> Self { ClauseDb { clauses: Vec::new() } }

    pub fn add(&mut self, clause: Clause) -> ClauseRef {
        let id = ClauseRef(self.clauses.len() as u32);
        self.clauses.push(clause);
        id
    }

    pub fn get(&self, r: ClauseRef) -> &Clause {
        &self.clauses[r.0 as usize]
    }

    pub fn get_mut(&mut self, r: ClauseRef) -> &mut Clause {
        &mut self.clauses[r.0 as usize]
    }

    pub fn len(&self) -> usize { self.clauses.len() }
}

impl Default for ClauseDb {
    fn default() -> Self { Self::new() }
}
