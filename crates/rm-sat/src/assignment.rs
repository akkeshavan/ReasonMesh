use rm_akx::literal::{Literal, Var};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Value {
    Undef,
    True,
    False,
}

impl Value {
    #[inline]
    pub fn from_bool(b: bool) -> Self {
        if b {
            Value::True
        } else {
            Value::False
        }
    }
    #[inline]
    pub fn is_undef(self) -> bool {
        matches!(self, Value::Undef)
    }
}

/// The assignment state and propagation trail.
///
/// Uses the MiniSAT approach: the trail itself is the propagation queue,
/// with `prop_head` as the BCP cursor.
pub struct Assignment {
    /// Current value of each variable (indexed by variable id).
    value: Vec<Value>,
    /// Decision level at which each variable was assigned. u32::MAX = unassigned.
    level: Vec<u32>,
    /// Antecedent clause index for each variable.
    /// ClauseRef::DECISION.0 for decision literals; ClauseRef::UNIT_CONFLICT.0 for assumptions.
    reason: Vec<u32>,
    /// Ordered assignment trail — also the BCP queue.
    trail: Vec<Literal>,
    /// `trail_lim[d]` = index into trail at the start of decision level d+1.
    trail_lim: Vec<usize>,
    /// BCP cursor: index of the next literal in trail to process.
    pub prop_head: usize,
}

impl Assignment {
    pub fn new(num_vars: u32) -> Self {
        let cap = num_vars as usize + 1;
        Assignment {
            value: vec![Value::Undef; cap],
            level: vec![u32::MAX; cap],
            reason: vec![u32::MAX; cap],
            trail: Vec::with_capacity(cap),
            trail_lim: Vec::new(),
            prop_head: 0,
        }
    }

    #[inline]
    pub fn value_of(&self, var: Var) -> Value {
        self.value[var as usize]
    }

    #[inline]
    pub fn literal_value(&self, lit: Literal) -> Value {
        match self.value[lit.var() as usize] {
            Value::Undef => Value::Undef,
            Value::True => {
                if lit.is_positive() {
                    Value::True
                } else {
                    Value::False
                }
            }
            Value::False => {
                if lit.is_positive() {
                    Value::False
                } else {
                    Value::True
                }
            }
        }
    }

    #[inline]
    pub fn is_assigned(&self, var: Var) -> bool {
        self.value[var as usize] != Value::Undef
    }

    /// Decision level at which `var` was assigned. Only valid when assigned.
    #[inline]
    pub fn level_of(&self, var: Var) -> u32 {
        self.level[var as usize]
    }

    /// Antecedent clause index for `var` (raw ClauseRef value).
    #[inline]
    pub fn reason_of(&self, var: Var) -> u32 {
        self.reason[var as usize]
    }

    #[inline]
    pub fn current_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    pub fn new_decision_level(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    pub fn assign(&mut self, lit: Literal, level: u32, reason: u32) {
        let var = lit.var() as usize;
        debug_assert!(
            self.value[var] == Value::Undef,
            "double-assigning var {var}"
        );
        self.value[var] = Value::from_bool(lit.is_positive());
        self.level[var] = level;
        self.reason[var] = reason;
        self.trail.push(lit);
    }

    pub fn trail(&self) -> &[Literal] {
        &self.trail
    }

    pub fn num_assigned(&self) -> usize {
        self.trail.len()
    }

    /// Undo all assignments above `level`.
    pub fn backtrack_to(&mut self, level: u32) {
        let target = if (level as usize) < self.trail_lim.len() {
            self.trail_lim[level as usize]
        } else {
            return;
        };
        for lit in self.trail.drain(target..) {
            let var = lit.var() as usize;
            self.value[var] = Value::Undef;
            self.level[var] = u32::MAX;
            self.reason[var] = u32::MAX;
        }
        self.trail_lim.truncate(level as usize);
        self.prop_head = self.prop_head.min(self.trail.len());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assign_and_backtrack() {
        let mut a = Assignment::new(4);
        a.new_decision_level();
        a.assign(Literal::positive(1), 1, u32::MAX);
        a.assign(Literal::negative(2), 1, u32::MAX);
        assert_eq!(a.value_of(1), Value::True);
        assert_eq!(a.value_of(2), Value::False);
        assert_eq!(a.level_of(1), 1);

        a.backtrack_to(0);
        assert_eq!(a.value_of(1), Value::Undef);
        assert_eq!(a.value_of(2), Value::Undef);
        assert_eq!(a.current_level(), 0);
    }

    #[test]
    fn literal_value() {
        let mut a = Assignment::new(2);
        a.assign(Literal::positive(1), 0, u32::MAX);
        assert_eq!(a.literal_value(Literal::positive(1)), Value::True);
        assert_eq!(a.literal_value(Literal::negative(1)), Value::False);
        assert_eq!(a.literal_value(Literal::positive(2)), Value::Undef);
    }
}
