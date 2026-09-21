//! Minimal DIMACS CNF parser.
//!
//! Input format (standard SAT competition DIMACS):
//! ```text
//! c comment
//! p cnf <num_vars> <num_clauses>
//! 1 -2 3 0
//! -4 0
//! ```
//! Each clause is a line of signed integers terminated by `0`.

use thiserror::Error;

/// Error parsing DIMACS input.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum DimacsError {
    #[error("missing `p cnf` header")]
    MissingHeader,
    #[error("malformed `p cnf` header: expected `p cnf <vars> <clauses>`")]
    MalformedHeader,
    #[error("literal 0 is not allowed inside a clause")]
    ZeroLiteral,
    #[error("declared {num_vars} variables but literal {lit} refers to variable {ref_var}")]
    VarOutOfRange {
        num_vars: u32,
        lit: i32,
        ref_var: u32,
    },
    #[error("expected {expected} clauses, found {found}")]
    WrongClauseCount { expected: u32, found: usize },
}

/// A parsed DIMACS instance: the number of variables and a list of clauses
/// (each clause is a list of nonzero signed literals).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DimacsCnf {
    pub num_vars: u32,
    pub clauses: Vec<Vec<i32>>,
}

/// Parse a DIMACS CNF instance from its textual form.
///
/// Handles both single-line clauses (`1 -2 3 0`) and multi-line clauses
/// where the terminating `0` appears on its own line. Also handles the
/// traditional SATLIB end-of-file marker `%`.
pub fn parse_dimacs(input: &str) -> Result<DimacsCnf, DimacsError> {
    let mut num_vars = None;
    let mut num_clauses = None;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    // Accumulates literals for the clause currently being built.
    // `None` = between clauses, `Some(lits)` = inside a clause.
    let mut current: Option<Vec<i32>> = None;

    for raw in input.lines() {
        let line = raw.split(';').next().unwrap_or("").trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        // Traditional DIMACS end-of-file marker: a line starting with '%'
        // (followed by an optional '0' line) signals end of input.
        if line.starts_with('%') {
            break;
        }
        if let Some(rest) = line.strip_prefix('p') {
            let rest = rest.trim();
            let mut it = rest.split_whitespace();
            if it.next() != Some("cnf") {
                return Err(DimacsError::MalformedHeader);
            }
            let vars: u32 = it
                .next()
                .and_then(|s| s.parse().ok())
                .ok_or(DimacsError::MalformedHeader)?;
            let cls: u32 = it
                .next()
                .and_then(|s| s.parse().ok())
                .ok_or(DimacsError::MalformedHeader)?;
            num_vars = Some(vars);
            num_clauses = Some(cls);
            continue;
        }

        let nv = num_vars.ok_or(DimacsError::MissingHeader)?;
        for tok in line.split_whitespace() {
            let lit: i32 = tok.parse().map_err(|_| DimacsError::MalformedHeader)?;
            if lit == 0 {
                // Terminator: commit whatever clause we were building
                // (may be empty for the empty-clause encoding `0`).
                clauses.push(current.take().unwrap_or_default());
            } else {
                let ref_var = lit.unsigned_abs();
                if ref_var > nv {
                    return Err(DimacsError::VarOutOfRange {
                        num_vars: nv,
                        lit,
                        ref_var,
                    });
                }
                current.get_or_insert_with(Vec::new).push(lit);
            }
        }
    }

    let nv = num_vars.ok_or(DimacsError::MissingHeader)?;
    if let Some(expected) = num_clauses {
        if clauses.len() != expected as usize {
            return Err(DimacsError::WrongClauseCount {
                expected,
                found: clauses.len(),
            });
        }
    }

    Ok(DimacsCnf {
        num_vars: nv,
        clauses,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_basic_cnf() {
        let dimacs = "c a comment\np cnf 3 2\n1 -2 3 0\n-1 0\n";
        let cnf = parse_dimacs(dimacs).unwrap();
        assert_eq!(cnf.num_vars, 3);
        assert_eq!(cnf.clauses, vec![vec![1, -2, 3], vec![-1]]);
    }

    #[test]
    fn parses_clause_lines_and_trailing_zeros() {
        let dimacs = "p cnf 2 3\n1 2 0\n-1 -2 0\n2 0\n";
        let cnf = parse_dimacs(dimacs).unwrap();
        assert_eq!(cnf.clauses, vec![vec![1, 2], vec![-1, -2], vec![2]]);
    }

    #[test]
    fn parses_empty_clause() {
        let dimacs = "p cnf 1 1\n0\n";
        let cnf = parse_dimacs(dimacs).unwrap();
        assert_eq!(cnf.clauses, vec![Vec::<i32>::new()]);
    }

    #[test]
    fn rejects_out_of_range_literal() {
        let dimacs = "p cnf 2 1\n3 0\n";
        let err = parse_dimacs(dimacs).unwrap_err();
        assert_eq!(
            err,
            DimacsError::VarOutOfRange {
                num_vars: 2,
                lit: 3,
                ref_var: 3
            }
        );
    }

    #[test]
    fn rejects_wrong_clause_count() {
        let dimacs = "p cnf 2 2\n1 0\n";
        let err = parse_dimacs(dimacs).unwrap_err();
        assert_eq!(
            err,
            DimacsError::WrongClauseCount {
                expected: 2,
                found: 1
            }
        );
    }

    #[test]
    fn rejects_missing_header() {
        let dimacs = "1 0\n";
        assert_eq!(
            parse_dimacs(dimacs).unwrap_err(),
            DimacsError::MissingHeader
        );
    }
}
