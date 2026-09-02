//! DRUP (Delete-Reverse Unit Propagation) proof checker.
//!
//! DRUP is the simplest format for UNSAT proofs from CDCL solvers. Each line
//! of the proof is a *clause addition* step; the proof is valid iff every
//! such clause can be verified by unit propagation (UP) to contradiction from
//! the existing clause database with all literals of the new clause negated.
//! The final step must be the empty clause `[]`.
//!
//! This checker deliberately shares **no code** with the CDCL solver. It is
//! an independent, quadratic-time verifier appropriate for the proof sizes
//! produced by our solver in research experiments.
//!
//! Reference: Heule et al., "Verifying Refutations with Extended Resolution",
//! CADE 2013.

use thiserror::Error;

#[derive(Debug, Error)]
pub enum DrupError {
    #[error("proof is empty (no empty clause)")]
    EmptyProof,
    #[error("proof step {step} is not an RUP clause: {clause:?}")]
    NotRup { step: usize, clause: Vec<i32> },
    #[error("proof does not end with the empty clause")]
    NoEmptyClause,
    #[error("literal {lit} references variable {var} which exceeds num_vars={num_vars}")]
    OutOfRange { lit: i32, var: u32, num_vars: u32 },
}

/// Verify a DRUP proof.
///
/// # Arguments
/// * `num_vars` — number of variables declared in the problem.
/// * `original` — the original clause set (DIMACS integer format).
/// * `proof` — the DRUP proof steps. Each step is a clause; the last must be
///   the empty clause `[]`.
///
/// Returns `Ok(steps_verified)` on success, `Err` on any violation.
pub fn verify_drup(
    num_vars: u32,
    original: &[Vec<i32>],
    proof: &[Vec<i32>],
) -> Result<usize, DrupError> {
    if proof.is_empty() {
        return Err(DrupError::EmptyProof);
    }
    if proof.last().map(|c| !c.is_empty()).unwrap_or(true) {
        return Err(DrupError::NoEmptyClause);
    }

    // Validate literal range.
    for clause in original.iter().chain(proof.iter()) {
        for &lit in clause {
            let var = lit.unsigned_abs();
            if var > num_vars {
                return Err(DrupError::OutOfRange { lit, var, num_vars });
            }
        }
    }

    // Working clause database, starts with original clauses.
    let mut db: Vec<Vec<i32>> = original.to_vec();

    for (step_idx, clause) in proof.iter().enumerate() {
        if clause.is_empty() {
            // Empty clause: must be derivable by UP from db alone (all
            // clauses falsified with an empty assignment → UP detects it).
            if !up_derives_empty(&db, &[]) {
                return Err(DrupError::NotRup { step: step_idx, clause: clause.clone() });
            }
            // Valid proof — return count of verified steps.
            return Ok(step_idx + 1);
        }

        // RUP check: negate all literals in `clause` and run UP.
        // If UP reaches a contradiction, the clause is redundant (RUP).
        let negated: Vec<i32> = clause.iter().map(|&l| -l).collect();
        if !up_derives_empty(&db, &negated) {
            return Err(DrupError::NotRup { step: step_idx, clause: clause.clone() });
        }

        // Add the clause to the database (all future steps can use it).
        db.push(clause.clone());
    }

    Err(DrupError::NoEmptyClause)
}

/// Run unit propagation starting from `unit_lits` (already-negated literals
/// from the clause being checked) against `db`. Returns `true` if UP reaches
/// a contradiction (some clause is fully falsified).
///
/// This is a simple, correct but quadratic UP implementation. Good enough for
/// the clause sizes produced by our solver.
fn up_derives_empty(db: &[Vec<i32>], unit_lits: &[i32]) -> bool {
    // `assignment[v]` = Some(sign) when variable v is assigned:
    //   sign = true  → variable v is true  (positive literal satisfied)
    //   sign = false → variable v is false (negative literal satisfied)
    // We start with all literals in `unit_lits` assigned to false
    // (because we negated them — they are the "assume-false" assignment).
    //
    // For a literal l in a clause:
    //   l > 0: the literal is satisfied iff assignment[l] = Some(true)
    //   l < 0: the literal is satisfied iff assignment[|l|] = Some(false)
    //
    // A clause is falsified iff every literal is assigned-false.
    // A clause is unit iff exactly one literal is unassigned and the rest are false.

    // max variable index for the assignment vector
    let max_var = db
        .iter()
        .flat_map(|c| c.iter())
        .chain(unit_lits.iter())
        .map(|l| l.unsigned_abs() as usize)
        .max()
        .unwrap_or(0);

    // None = unassigned, Some(true/false) = assigned value
    let mut asgn: Vec<Option<bool>> = vec![None; max_var + 1];

    // Apply the initial unit literals (negated clause literals = assumed false).
    let mut queue: Vec<i32> = unit_lits.to_vec();
    for &lit in unit_lits {
        let v = lit.unsigned_abs() as usize;
        // lit is the negated form of the original literal; assigning it means
        // the original literal is false, i.e. its negation is true.
        // `lit > 0` means original literal was negative (var=false → we set var=true)
        // Wait — let me think carefully:
        //   original literal p (positive): we negate to -p. So -p > 0 means we
        //   need var(-p) = var(p) to be false. lit = -p < 0 → var = |lit|, we
        //   assign the variable as false (the original literal p=false).
        //
        // Simpler: lit is in the `unit_lits` set. `lit` is assigned True (as a
        // literal). A literal `lit > 0` means variable `lit` is true. `lit < 0`
        // means variable `|lit|` is false.
        let val = lit > 0;
        asgn[v] = Some(val);
    }

    // Iterative UP.
    let mut changed = true;
    while changed {
        changed = false;

        for clause in db {
            // Count falsified and unassigned literals.
            let mut unassigned_lit: Option<i32> = None;
            let mut all_false = true;
            let mut unassigned_count = 0;

            for &lit in clause {
                let v = lit.unsigned_abs() as usize;
                match asgn.get(v).copied().flatten() {
                    None => {
                        unassigned_lit = Some(lit);
                        unassigned_count += 1;
                        all_false = false;
                    }
                    Some(val) => {
                        let satisfied = if lit > 0 { val } else { !val };
                        if satisfied {
                            all_false = false;
                            unassigned_count = 0; // clause satisfied, short circuit below
                            break;
                        }
                        // else: literal is false, continue
                    }
                }
            }

            if all_false && unassigned_count == 0 {
                // Clause is fully falsified — contradiction.
                return true;
            }

            if unassigned_count == 1 {
                // Unit clause: assign the unassigned literal to true.
                let ul = unassigned_lit.unwrap();
                let v = ul.unsigned_abs() as usize;
                let val = ul > 0;
                if asgn[v].is_none() {
                    asgn[v] = Some(val);
                    queue.push(ul);
                    changed = true;
                } else if asgn[v] != Some(val) {
                    // Conflict: variable assigned opposite value.
                    return true;
                }
            }
        }
    }

    false
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trivial_unsat_empty_clause() {
        // Empty clause as the first original clause → empty proof of 1 step
        let original = vec![vec![]];
        let proof = vec![vec![]];
        assert!(verify_drup(0, &original, &proof).is_ok());
    }

    #[test]
    fn unit_propagation_refutation() {
        // (x1) ∧ (¬x1) → UNSAT
        // Original: {1} {-1}
        // Proof: just the empty clause (UP from {1} and {-1} is enough)
        let original = vec![vec![1], vec![-1]];
        let proof = vec![vec![]];
        let r = verify_drup(1, &original, &proof);
        assert!(r.is_ok(), "expected valid proof, got {r:?}");
    }

    #[test]
    fn resolution_step() {
        // (x ∨ y) ∧ (¬x ∨ y) ∧ (¬y) → UNSAT
        // Derived: (y) from first two by resolution; then empty from (y) and (¬y)
        let original = vec![vec![1, 2], vec![-1, 2], vec![-2]];
        let proof = vec![
            vec![2],  // RUP: assuming ¬y, {x,y} becomes {x} and {¬x,y} becomes {¬x}, UP gives contradiction
            vec![],   // empty clause
        ];
        let r = verify_drup(2, &original, &proof);
        assert!(r.is_ok(), "expected valid proof, got {r:?}");
    }

    #[test]
    fn invalid_rup_step_rejected() {
        // Claim (x1) is RUP from (x1 ∨ x2) — it isn't.
        let original = vec![vec![1, 2]];
        let proof = vec![vec![1], vec![]];
        assert!(matches!(verify_drup(2, &original, &proof), Err(DrupError::NotRup { .. })));
    }

    #[test]
    fn missing_empty_clause() {
        let original = vec![vec![1]];
        let proof = vec![vec![1, 2]]; // no empty clause at end
        assert!(matches!(verify_drup(2, &original, &proof), Err(DrupError::NoEmptyClause)));
    }

    #[test]
    fn empty_proof_rejected() {
        let original = vec![vec![1, 2]];
        assert!(matches!(verify_drup(2, &original, &[]), Err(DrupError::EmptyProof)));
    }

    /// Cross-check: run the CDCL solver with proof logging on unsatisfiable
    /// instances, then verify the proof with this independent checker.
    #[test]
    fn cross_check_with_cdcl_proofs() {
        use rm_sat::{parse_dimacs, CdclSolver, SolveResult};
        use rm_akx::literal::Literal;

        // Pigeonhole PHP(3,2): 3 pigeons, 2 holes — provably UNSAT.
        // p cnf 6 11 (variables x_ij for pigeon i in hole j)
        let dimacs = "p cnf 6 11\n\
            1 2 0\n\
            3 4 0\n\
            5 6 0\n\
            -1 -3 0\n\
            -1 -5 0\n\
            -3 -5 0\n\
            -2 -4 0\n\
            -2 -6 0\n\
            -4 -6 0\n\
            1 3 5 0\n\
            2 4 6 0\n";
        let cnf = parse_dimacs(dimacs).unwrap();
        let mut solver = CdclSolver::new(cnf.num_vars);
        solver.enable_proof_logging();
        for clause in &cnf.clauses {
            let lits: Vec<Literal> = clause.iter()
                .map(|&l| if l > 0 { Literal::positive(l as u32) } else { Literal::negative((-l) as u32) })
                .collect();
            solver.add_clause(&lits);
        }
        assert_eq!(solver.solve(&[], u64::MAX), SolveResult::Unsat);
        let proof = solver.take_proof_log().expect("proof log should be present");
        assert!(!proof.is_empty(), "proof should have at least the empty clause");
        let result = verify_drup(cnf.num_vars, &cnf.clauses, &proof);
        assert!(result.is_ok(), "CDCL proof failed verification: {result:?}");
    }
}
