use rm_akx::literal::{Literal, Var};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Value { Undef, True, False }

impl Value {
    pub fn from_bool(b: bool) -> Self { if b { Value::True } else { Value::False } }
    pub fn is_undef(self) -> bool { matches!(self, Value::Undef) }
}

/// Trail entry: which literal was assigned and at what decision level.
#[derive(Clone, Copy, Debug)]
pub struct TrailEntry {
    pub lit: Literal,
    pub level: u32,
    /// Index of the antecedent clause, or `u32::MAX` for decisions.
    pub reason: u32,
}

/// The partial assignment and propagation trail.
pub struct Assignment {
    values: Vec<Value>,
    trail: Vec<TrailEntry>,
    /// `trail_lim[d]` = trail index at the start of decision level d+1.
    trail_lim: Vec<usize>,
}

impl Assignment {
    pub fn new(num_vars: u32) -> Self {
        Assignment {
            values: vec![Value::Undef; num_vars as usize + 1],
            trail: Vec::new(),
            trail_lim: Vec::new(),
        }
    }

    pub fn value_of(&self, var: Var) -> Value {
        self.values[var as usize]
    }

    pub fn literal_value(&self, lit: Literal) -> Value {
        match self.values[lit.var() as usize] {
            Value::Undef => Value::Undef,
            Value::True  => if lit.is_positive() { Value::True } else { Value::False },
            Value::False => if lit.is_positive() { Value::False } else { Value::True },
        }
    }

    pub fn is_assigned(&self, var: Var) -> bool {
        !self.values[var as usize].is_undef()
    }

    pub fn assign(&mut self, lit: Literal, level: u32, reason: u32) {
        let var = lit.var() as usize;
        debug_assert!(self.values[var].is_undef());
        self.values[var] = Value::from_bool(lit.is_positive());
        self.trail.push(TrailEntry { lit, level, reason });
    }

    pub fn current_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    pub fn new_decision_level(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    pub fn trail(&self) -> &[TrailEntry] {
        &self.trail
    }

    pub fn trail_at(&self, level: u32) -> usize {
        if level == 0 { 0 } else { self.trail_lim[(level - 1) as usize] }
    }

    /// Undo all assignments above `level`.
    pub fn backtrack_to(&mut self, level: u32, values: &mut Vec<Value>) {
        let target = self.trail_at(level + 1).min(self.trail.len());
        for entry in self.trail.drain(target..) {
            self.values[entry.lit.var() as usize] = Value::Undef;
            values[entry.lit.var() as usize] = Value::Undef;
        }
        self.trail_lim.truncate(level as usize);
    }
}
