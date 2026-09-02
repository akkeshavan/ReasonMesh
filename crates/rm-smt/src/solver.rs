//! Facade over the theory solvers. For QF_BV it dispatches to the bit-blaster
//! path; the interface is shaped so additional theories (EUF, arithmetic) can
//! be added as CDCL(T) integration lands.

use rm_syntax::Script;
use rm_theory_bv::{BvModel, BvResult, BvSolver};

/// Errors from the SMT solver facade.
#[derive(Debug, thiserror::Error)]
pub enum SmtError {
    #[error("SMT-LIB parse error: {0}")]
    Parse(#[from] rm_syntax::ParseError),
    #[error("unsupported logic for the current theory set: {0}")]
    UnsupportedLogic(String),
    #[error("no assertions and no declarations; nothing to solve")]
    EmptyProblem,
    #[error("solver internal error: {0}")]
    Internal(String),
}

/// The overall SMT-LIB status.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SmtStatus {
    Sat,
    Unsat,
    Unknown,
}

/// A solved SMT problem: status plus a model when SAT.
#[derive(Clone, Debug)]
pub struct SmtResult {
    pub status: SmtStatus,
    pub model: Option<BvModel>,
    /// Raw string values per declared constant for `get-model` output.
    pub values: Vec<(String, String)>,
}

/// Facade solver for a single SMT-LIB script.
pub struct SmtSolver {
    script: Script,
}

impl SmtSolver {
    pub fn parse(text: &str) -> Result<SmtSolver, SmtError> {
        Ok(SmtSolver { script: Script::parse(text)? })
    }

    /// Which theory family the script declares.
    fn logic(&self) -> Option<&str> {
        self.script.commands.iter().find_map(|c| match c {
            rm_syntax::Command::SetLogic(name) => Some(name.as_str()),
            _ => None,
        })
    }

    /// Solve the script.
    pub fn solve(&self, max_conflicts: u64) -> Result<SmtResult, SmtError> {
        match self.logic() {
            Some("QF_BV") | None => {
                if self.script.assertions().is_empty() {
                    return Err(SmtError::EmptyProblem);
                }
                let bv = BvSolver::new(self.script.clone());
                let mut values: Vec<(String, String)> = Vec::new();
                let (status, model) = match bv.solve(max_conflicts).map_err(SmtError::Internal)? {
                    BvResult::Sat { model } => {
                        for (name, width) in bv.declared() {
                            if let Some(v) = model.value_of(&name) {
                                values.push((name, format!("(_ bv{} {width})", v.to_u64())));
                            }
                        }
                        (SmtStatus::Sat, Some(model))
                    }
                    BvResult::Unsat => (SmtStatus::Unsat, None),
                    BvResult::Unknown => (SmtStatus::Unknown, None),
                };
                Ok(SmtResult { status, model, values })
            }
            Some(other) => Err(SmtError::UnsupportedLogic(other.to_string())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn qf_bv_sat() {
        let s = SmtSolver::parse(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 8))
             (assert (bvult x #x05))
             (check-sat)",
        )
        .unwrap();
        let r = s.solve(10_000).unwrap();
        assert_eq!(r.status, SmtStatus::Sat);
        assert!(!r.values.is_empty());
    }

    #[test]
    fn qf_bv_unsat() {
        let s = SmtSolver::parse(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 4))
             (assert (= x #b0000))
             (assert (= x #b1111))
             (check-sat)",
        )
        .unwrap();
        let r = s.solve(10_000).unwrap();
        assert_eq!(r.status, SmtStatus::Unsat);
    }

    #[test]
    fn unsupported_logic_rejected() {
        let s = SmtSolver::parse("(set-logic QF_UF) (declare-const a Bool) (assert a)").unwrap();
        assert!(matches!(s.solve(1000), Err(SmtError::UnsupportedLogic(_))));
    }

    #[test]
    fn empty_problem_rejected() {
        let s = SmtSolver::parse("(set-logic QF_BV)").unwrap();
        assert!(matches!(s.solve(1000), Err(SmtError::EmptyProblem)));
    }
}
