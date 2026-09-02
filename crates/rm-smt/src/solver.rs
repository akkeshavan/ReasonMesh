//! Facade over the theory solvers. Dispatches to the bit-blaster path for
//! QF_BV and to the difference-logic path for QF_IDL/QF_RDL.

use rm_syntax::Script;
use rm_theory_bv::{BvModel, BvResult, BvSolver};
use crate::dl::{solve_qf_idl, DlStatus};
use crate::uf::{solve_qf_uf, UfStatus};

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
    raw: String,
}

impl SmtSolver {
    pub fn parse(text: &str) -> Result<SmtSolver, SmtError> {
        Ok(SmtSolver { raw: text.to_owned() })
    }

    /// Extract the set-logic name from the raw text with a simple scan.
    fn logic(&self) -> Option<String> {
        // Look for `(set-logic <symbol>)` anywhere in the text.
        let tokens = rm_syntax::lex(&self.raw).ok()?;
        let exprs = rm_syntax::parse_program(&tokens).ok()?;
        for expr in &exprs {
            let rm_syntax::SExpr::List(items) = expr else { continue };
            if items.first().and_then(|e| e.symbol()) == Some("set-logic") {
                if let Some(rm_syntax::SExpr::Atom(rm_syntax::Atom::Symbol(l))) = items.get(1) {
                    return Some(l.clone());
                }
            }
        }
        None
    }

    /// Solve the script.
    pub fn solve(&self, max_conflicts: u64) -> Result<SmtResult, SmtError> {
        match self.logic().as_deref() {
            Some("QF_BV") | None => {
                let script = Script::parse(&self.raw)?;
                if script.assertions().is_empty() {
                    return Err(SmtError::EmptyProblem);
                }
                let bv = BvSolver::new(script.clone());
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
            Some("QF_IDL") | Some("QF_RDL") => {
                match solve_qf_idl(&self.raw).map_err(SmtError::Internal)? {
                    (DlStatus::Sat, int_model) => {
                        let values = int_model
                            .into_iter()
                            .map(|(n, v)| (n, v.to_string()))
                            .collect();
                        Ok(SmtResult { status: SmtStatus::Sat, model: None, values })
                    }
                    (DlStatus::Unsat, _) => {
                        Ok(SmtResult { status: SmtStatus::Unsat, model: None, values: Vec::new() })
                    }
                    (DlStatus::Unknown, _) => {
                        Ok(SmtResult { status: SmtStatus::Unknown, model: None, values: Vec::new() })
                    }
                }
            }
            Some("QF_UF") => {
                match solve_qf_uf(&self.raw).map_err(SmtError::Internal)? {
                    uf_result if uf_result.status == UfStatus::Sat => {
                        let values = uf_result
                            .model
                            .into_iter()
                            .collect();
                        Ok(SmtResult { status: SmtStatus::Sat, model: None, values })
                    }
                    uf_result if uf_result.status == UfStatus::Unsat => {
                        Ok(SmtResult { status: SmtStatus::Unsat, model: None, values: Vec::new() })
                    }
                    _ => Ok(SmtResult { status: SmtStatus::Unknown, model: None, values: Vec::new() }),
                }
            }
            Some(other) => Err(SmtError::UnsupportedLogic(other.to_owned())),
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
    fn qf_idl_sat() {
        let s = SmtSolver::parse(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (<= (- x y) 5))
             (assert (<= (- y x) 3))
             (check-sat)",
        )
        .unwrap();
        let r = s.solve(10_000).unwrap();
        assert_eq!(r.status, SmtStatus::Sat);
    }

    #[test]
    fn qf_idl_unsat() {
        let s = SmtSolver::parse(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (<= (- x y) 1))
             (assert (<= (- y x) -3))
             (check-sat)",
        )
        .unwrap();
        let r = s.solve(10_000).unwrap();
        assert_eq!(r.status, SmtStatus::Unsat);
    }

    #[test]
    fn qf_uf_sat() {
        let s = SmtSolver::parse(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (assert (= a b))
             (check-sat)",
        )
        .unwrap();
        let r = s.solve(10_000).unwrap();
        assert_eq!(r.status, SmtStatus::Sat);
    }

    #[test]
    fn qf_uf_unsat() {
        let s = SmtSolver::parse(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (declare-fun f (U) U)
             (assert (= a b))
             (assert (not (= (f a) (f b))))
             (check-sat)",
        )
        .unwrap();
        let r = s.solve(10_000).unwrap();
        assert_eq!(r.status, SmtStatus::Unsat);
    }

    #[test]
    fn unsupported_logic_rejected() {
        let s = SmtSolver::parse("(set-logic QF_LIA) (declare-const a Int) (assert (> a 0))").unwrap();
        assert!(matches!(s.solve(1000), Err(SmtError::UnsupportedLogic(_))));
    }

    #[test]
    fn empty_problem_rejected() {
        let s = SmtSolver::parse("(set-logic QF_BV)").unwrap();
        assert!(matches!(s.solve(1000), Err(SmtError::EmptyProblem)));
    }
}
