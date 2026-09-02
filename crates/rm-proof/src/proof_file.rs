//! ReasonMesh proof file format (`.rmproof`).
//!
//! A `.rmproof` file is a UTF-8 text file. Comment lines start with `c`.
//! The supported sections are:
//!
//! ```text
//! c reasonmesh proof v0.2
//! p cnf <num_vars> <num_clauses>
//! [clause lines: space-separated literals, terminated by 0]
//! s SAT | UNSAT
//! v <lit1> <lit2> ... 0   ; one or more model lines for SAT results
//! d <lit1> <lit2> ... 0   ; DRUP proof lines for UNSAT results
//! ```
//!
//! The clauses section may be omitted if the proof is self-contained via a
//! companion `.cnf` file; in that case the CLI resolves it by filename.
//!
//! Model lines (`v ...`) follow the DIMACS SAT competition convention: positive
//! literal = variable is true, negative literal = variable is false, `0` ends
//! the model. Multiple `v` lines are concatenated.
//!
//! DRUP proof lines (`d ...`) are clause addition steps in DRUP format.
//! The last `d` line must be the empty clause `d 0` (the contradiction).

use std::io::{BufRead, BufReader, Read};
use thiserror::Error;

/// Errors parsing or checking a proof file.
#[derive(Debug, Error)]
pub enum ProofError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("malformed proof line {line}: {msg}")]
    Malformed { line: usize, msg: String },
    #[error("proof declares {declared} variables but model has assignments up to variable {found}")]
    ModelTooLarge { declared: u32, found: u32 },
    #[error("proof is UNSAT: external DRAT checking is not yet implemented")]
    UnsatNotSupported,
    #[error("missing problem header (p cnf ...)")]
    MissingHeader,
    #[error("missing status line (s SAT / s UNSAT)")]
    MissingStatus,
    #[error("model check failed: {0}")]
    CheckFailed(#[from] crate::model::ModelCheckError),
    #[error("model is UNSATISFYING (clause falsified)")]
    BadModel,
    #[error("DRUP proof verification failed: {0}")]
    Drup(#[from] crate::drup::DrupError),
}

/// A parsed proof file, ready for validation.
#[derive(Debug)]
pub struct ProofFile {
    pub num_vars: u32,
    pub clauses: Vec<Vec<i32>>,
    pub status: Status,
    /// Model truth values (1-indexed; index 0 unused) for SAT proofs.
    pub model: Vec<bool>,
    /// DRUP proof steps for UNSAT proofs (`d` lines). Empty for SAT.
    pub drup: Vec<Vec<i32>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Sat,
    Unsat,
}

impl ProofFile {
    /// Parse an `.rmproof` file from a reader.
    pub fn parse<R: Read>(reader: R) -> Result<ProofFile, ProofError> {
        let reader = BufReader::new(reader);
        let mut num_vars: Option<u32> = None;
        let mut _num_clauses: Option<u32> = None;
        let mut clauses: Vec<Vec<i32>> = Vec::new();
        let mut status: Option<Status> = None;
        let mut model_lits: Vec<i32> = Vec::new();
        let mut drup: Vec<Vec<i32>> = Vec::new();

        for (idx, raw) in reader.lines().enumerate() {
            let lineno = idx + 1;
            let line = raw?;
            let trimmed = line.trim();

            if trimmed.is_empty() || trimmed.starts_with("c ") || trimmed == "c" {
                continue;
            }

            if let Some(rest) = trimmed.strip_prefix("p cnf ") {
                let parts: Vec<&str> = rest.split_whitespace().collect();
                if parts.len() < 2 {
                    return Err(ProofError::Malformed { line: lineno, msg: "p cnf needs two integers".into() });
                }
                num_vars = Some(parts[0].parse().map_err(|_| ProofError::Malformed { line: lineno, msg: "bad num_vars".into() })?);
                _num_clauses = Some(parts[1].parse().map_err(|_| ProofError::Malformed { line: lineno, msg: "bad num_clauses".into() })?);
                continue;
            }

            if trimmed == "s SAT" {
                status = Some(Status::Sat);
                continue;
            }
            if trimmed == "s UNSAT" {
                status = Some(Status::Unsat);
                continue;
            }

            if let Some(rest) = trimmed.strip_prefix("v ") {
                for tok in rest.split_whitespace() {
                    let lit: i32 = tok.parse().map_err(|_| ProofError::Malformed { line: lineno, msg: format!("bad literal: {tok}") })?;
                    if lit == 0 { break; }
                    model_lits.push(lit);
                }
                continue;
            }

            // DRUP proof line: "d <lit>* 0"
            if let Some(rest) = trimmed.strip_prefix("d ") {
                let lits: Vec<i32> = rest
                    .split_whitespace()
                    .take_while(|t| *t != "0")
                    .map(|t| t.parse::<i32>())
                    .collect::<Result<_, _>>()
                    .map_err(|_| ProofError::Malformed { line: lineno, msg: format!("bad drup literal in: {trimmed}") })?;
                drup.push(lits);
                continue;
            }
            // Plain "0" line = empty DRUP step (empty clause in proof)
            if trimmed == "0" && status == Some(Status::Unsat) {
                drup.push(vec![]);
                continue;
            }

            // Clause line: space-separated literals terminated by 0
            if num_vars.is_some() {
                let lits: Result<Vec<i32>, _> = trimmed
                    .split_whitespace()
                    .take_while(|t| *t != "0")
                    .map(|t| t.parse::<i32>())
                    .collect();
                match lits {
                    Ok(ls) if !ls.is_empty() => clauses.push(ls),
                    Ok(_) => {} // empty clause (line was just "0")
                    Err(_) => return Err(ProofError::Malformed { line: lineno, msg: format!("bad clause: {trimmed}") }),
                }
            }
        }

        let num_vars = num_vars.ok_or(ProofError::MissingHeader)?;
        let status = status.ok_or(ProofError::MissingStatus)?;

        // Build model array (1-indexed).
        let mut model = vec![false; num_vars as usize + 1];
        for lit in model_lits {
            let var = lit.unsigned_abs();
            if var > num_vars {
                return Err(ProofError::ModelTooLarge { declared: num_vars, found: var });
            }
            if var > 0 {
                model[var as usize] = lit > 0;
            }
        }

        Ok(ProofFile { num_vars, clauses, status, model, drup })
    }

    /// Verify the proof. Returns `Ok(())` if the proof is valid.
    pub fn verify(&self) -> Result<(), ProofError> {
        match self.status {
            Status::Unsat => {
                if self.drup.is_empty() {
                    return Err(ProofError::UnsatNotSupported);
                }
                crate::drup::verify_drup(self.num_vars, &self.clauses, &self.drup)
                    .map(|_| ())
                    .map_err(ProofError::Drup)
            }
            Status::Sat => {
                let ok = crate::model::check_dimacs_model(self.num_vars, &self.clauses, &self.model)?;
                if ok {
                    Ok(())
                } else {
                    Err(ProofError::BadModel)
                }
            }
        }
    }

    /// Serialize an UNSAT proof (original clauses + DRUP steps) to the
    /// `.rmproof` text format. Suitable for writing to a file.
    pub fn write_unsat(
        num_vars: u32,
        clauses: &[Vec<i32>],
        drup: &[Vec<i32>],
        mut out: impl std::io::Write,
    ) -> std::io::Result<()> {
        writeln!(out, "c reasonmesh proof v0.2")?;
        writeln!(out, "p cnf {} {}", num_vars, clauses.len())?;
        for clause in clauses {
            let s: Vec<String> = clause.iter().map(|l| l.to_string()).collect();
            writeln!(out, "{} 0", s.join(" "))?;
        }
        writeln!(out, "s UNSAT")?;
        for step in drup {
            if step.is_empty() {
                writeln!(out, "0")?;
            } else {
                let s: Vec<String> = step.iter().map(|l| l.to_string()).collect();
                writeln!(out, "d {} 0", s.join(" "))?;
            }
        }
        Ok(())
    }

    /// Serialize a SAT proof (original clauses + model) to the `.rmproof`
    /// text format.
    pub fn write_sat(
        num_vars: u32,
        clauses: &[Vec<i32>],
        model: &[bool],
        mut out: impl std::io::Write,
    ) -> std::io::Result<()> {
        writeln!(out, "c reasonmesh proof v0.2")?;
        writeln!(out, "p cnf {} {}", num_vars, clauses.len())?;
        for clause in clauses {
            let s: Vec<String> = clause.iter().map(|l| l.to_string()).collect();
            writeln!(out, "{} 0", s.join(" "))?;
        }
        writeln!(out, "s SAT")?;
        let lits: Vec<String> = (1..=num_vars as usize)
            .map(|v| {
                let val = model.get(v).copied().unwrap_or(false);
                if val { v.to_string() } else { format!("-{v}") }
            })
            .collect();
        writeln!(out, "v {} 0", lits.join(" "))?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    const SIMPLE_SAT: &str = "c reasonmesh proof v0.2\n\
        p cnf 2 2\n\
        1 2 0\n\
        -1 -2 0\n\
        s SAT\n\
        v 1 -2 0\n";

    #[test]
    fn parse_and_verify_sat() {
        let pf = ProofFile::parse(Cursor::new(SIMPLE_SAT)).unwrap();
        assert_eq!(pf.status, Status::Sat);
        assert_eq!(pf.num_vars, 2);
        assert_eq!(pf.clauses.len(), 2);
        assert!(pf.model[1]);
        assert!(!pf.model[2]);
        pf.verify().unwrap();
    }

    #[test]
    fn bad_model_detected() {
        // Model says x1=false but clause (x1) is falsified.
        let text = "c test\np cnf 1 1\n1 0\ns SAT\nv -1 0\n";
        let pf = ProofFile::parse(Cursor::new(text)).unwrap();
        assert!(matches!(pf.verify(), Err(ProofError::BadModel)));
    }

    #[test]
    fn unsat_status_returns_error() {
        let text = "c test\np cnf 1 2\n1 0\n-1 0\ns UNSAT\n";
        let pf = ProofFile::parse(Cursor::new(text)).unwrap();
        assert!(matches!(pf.verify(), Err(ProofError::UnsatNotSupported)));
    }

    #[test]
    fn missing_header_error() {
        let text = "s SAT\nv 1 0\n";
        assert!(matches!(ProofFile::parse(Cursor::new(text)), Err(ProofError::MissingHeader)));
    }

    #[test]
    fn missing_status_error() {
        let text = "p cnf 1 1\n1 0\nv 1 0\n";
        assert!(matches!(ProofFile::parse(Cursor::new(text)), Err(ProofError::MissingStatus)));
    }
}
