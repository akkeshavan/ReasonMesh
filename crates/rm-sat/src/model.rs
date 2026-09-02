use rm_akx::literal::{Literal, Var};

/// A complete satisfying assignment returned when the solver finds SAT.
#[derive(Clone, Debug)]
pub struct Model {
    /// `values[var]` = true/false for each variable. Index 0 unused (vars start at 1).
    values: Vec<bool>,
}

impl Model {
    pub(crate) fn new(values: Vec<bool>) -> Self {
        Model { values }
    }

    pub fn num_vars(&self) -> u32 {
        (self.values.len().saturating_sub(1)) as u32
    }

    /// Value of variable `var` in this model.
    pub fn value_of(&self, var: Var) -> bool {
        self.values[var as usize]
    }

    /// Whether literal `lit` is satisfied by this model.
    pub fn satisfies(&self, lit: Literal) -> bool {
        let val = self.values[lit.var() as usize];
        if lit.is_positive() {
            val
        } else {
            !val
        }
    }

    /// Verify this model against a set of clauses (each clause is a list of DIMACS literals).
    /// Returns true iff every clause has at least one satisfied literal.
    pub fn verify_dimacs(&self, clauses: &[Vec<i32>]) -> bool {
        clauses.iter().all(|clause| {
            clause.iter().any(|&lit| {
                let var = lit.unsigned_abs() as usize;
                let val = self.values[var];
                if lit > 0 {
                    val
                } else {
                    !val
                }
            })
        })
    }
}
