//! Independent SAT model evaluator.
//!
//! A SAT result must be validated independently of the solver before it is
//! trusted (spec §8.3, §13.2). This module deliberately shares **no code** with
//! the solver internals: it consumes raw truth values plus DIMACS clauses and
//! checks satisfiability directly. A model that fails this check is a solver
//! bug, not a re-solve.
//!
//! The evaluator is pure and total: given any input it either returns a
//! definite verdict or an explicit error, never `UNKNOWN`.

use thiserror::Error;

/// Error evaluating a candidate model. Any error is treated as an invalid
/// model; the error text is for diagnostics only.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum ModelCheckError {
    #[error("model has {model_vars} variable values but the problem declares {num_vars}")]
    SizeMismatch { model_vars: usize, num_vars: u32 },
    #[error("clause references variable {ref_var} but the problem declares {num_vars}")]
    ClauseOutOfRange { ref_var: u32, num_vars: u32 },
}

/// Verify a candidate model against a DIMACS instance.
///
/// `model` is indexed by variable: `model[v]` holds the truth value of
/// variable `v` for `1 <= v <= num_vars`; index 0 is ignored.
///
/// Returns `Ok(true)` if every clause has at least one satisfied literal,
/// `Ok(false)` if any clause is falsified, or `Err` if the model or problem is
/// malformed.
pub fn check_dimacs_model(
    num_vars: u32,
    clauses: &[Vec<i32>],
    model: &[bool],
) -> Result<bool, ModelCheckError> {
    if model.len() < num_vars as usize + 1 {
        return Err(ModelCheckError::SizeMismatch {
            model_vars: model.len(),
            num_vars,
        });
    }

    for clause in clauses {
        for &lit in clause {
            let var = lit.unsigned_abs();
            if var > num_vars {
                return Err(ModelCheckError::ClauseOutOfRange {
                    ref_var: var,
                    num_vars,
                });
            }
        }
        let satisfied = clause.iter().any(|&lit| {
            let var = lit.unsigned_abs();
            let val = model[var as usize];
            if lit > 0 {
                val
            } else {
                !val
            }
        });
        if !satisfied {
            return Ok(false);
        }
    }

    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Small deterministic PRNG for generating random test CNFs.
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
            self.state >> 33
        }
    }

    #[test]
    fn accepts_valid_model() {
        // (x1 ∨ x2) ∧ (¬x1 ∨ ¬x2)
        let clauses = vec![vec![1, 2], vec![-1, -2]];
        let mut model = vec![false; 3]; // index 0 unused
        model[1] = true;
        model[2] = false;
        assert_eq!(check_dimacs_model(2, &clauses, &model), Ok(true));
    }

    #[test]
    fn rejects_falsified_clause() {
        // (x1) ∧ (¬x1)
        let clauses = vec![vec![1], vec![-1]];
        let mut model = vec![false; 2];
        model[1] = true;
        assert_eq!(check_dimacs_model(1, &clauses, &model), Ok(false));
    }

    #[test]
    fn rejects_empty_clause_as_unsatisfiable() {
        let clauses = vec![Vec::<i32>::new()];
        let model = vec![false; 2];
        assert_eq!(check_dimacs_model(1, &clauses, &model), Ok(false));
    }

    #[test]
    fn rejects_too_short_model() {
        let clauses = vec![vec![1, 2]];
        let model = vec![false; 2]; // only covers variable 1
        assert_eq!(
            check_dimacs_model(2, &clauses, &model),
            Err(ModelCheckError::SizeMismatch {
                model_vars: 2,
                num_vars: 2
            })
        );
    }

    #[test]
    fn rejects_out_of_range_clause() {
        let clauses = vec![vec![1, 3]];
        let model = vec![false; 3];
        assert_eq!(
            check_dimacs_model(2, &clauses, &model),
            Err(ModelCheckError::ClauseOutOfRange {
                ref_var: 3,
                num_vars: 2
            })
        );
    }

    /// Cross-check: solve random CNFs with the production CDCL solver and
    /// validate every returned model with this independent evaluator. Only the
    /// solver's public API is used — never its internals.
    #[test]
    fn cross_check_with_solver_models() {
        use rm_akx::literal::Literal;
        use rm_sat::{parse_dimacs, CdclSolver};

        fn random_cnf(rng: &mut Lcg, vars: u32, clauses: usize) -> String {
            let mut s = format!("p cnf {vars} {clauses}\n");
            for _ in 0..clauses {
                let k = 1 + (rng.next() % 4) as usize;
                for _ in 0..k {
                    let v = 1 + (rng.next() % vars as u64) as u32;
                    let lit = if rng.next() & 1 == 0 {
                        v as i32
                    } else {
                        -(v as i32)
                    };
                    s.push_str(&format!("{lit} "));
                }
                s.push_str("0\n");
            }
            s
        }

        let mut rng = Lcg::new(7);
        for _ in 0..200 {
            let dimacs = random_cnf(&mut rng, 5, 12);
            let cnf = parse_dimacs(&dimacs).unwrap();
            let mut solver = CdclSolver::new(cnf.num_vars);
            for clause in &cnf.clauses {
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
                solver.add_clause(&lits);
            }
            if let rm_sat::SolveResult::Sat(m) = solver.solve(&[], u64::MAX) {
                let mut raw = vec![false; cnf.num_vars as usize + 1];
                for v in 1..=cnf.num_vars {
                    raw[v as usize] = m.value_of(v);
                }
                assert_eq!(
                    check_dimacs_model(cnf.num_vars, &cnf.clauses, &raw),
                    Ok(true),
                    "solver returned a model that fails independent validation"
                );
            }
        }
    }
}
