//! QF_IDL front end for the difference-logic theory path.
//!
//! Accepts raw SMT-LIB text with `(set-logic QF_IDL)`, `(declare-const x Int)`,
//! and assertions of the forms:
//!
//!   `(<= (- x y) c)`  →  x - y ≤ c
//!   `(< (- x y) c)`   →  x - y < c  (⟺ x - y ≤ c − 1 for IDL)
//!   `(>= (- x y) c)`  →  y - x ≤ -c
//!   `(> (- x y) c)`   →  y - x ≤ -c − 1
//!   `(= (- x y) c)`   →  x - y ≤ c  AND  y - x ≤ -c
//!   `(= x y)`         →  x - y ≤ 0  AND  y - x ≤ 0
//!   `(not (= x y))`   → not currently supported (return Unknown)
//!
//! Variables may also appear directly (without `(- x y)`) when c = 0.

use rm_syntax::{lex, parse_program, Atom, SExpr};
use rm_theory_arith::{DiffLogicSolver, DlError};
use rustc_hash::FxHashMap;

/// Status returned by the QF_IDL solver.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DlStatus {
    Sat,
    Unsat,
    Unknown,
}

struct DlDecls {
    var_map: FxHashMap<String, u32>,
    next_id: u32,
    assertions: Vec<SExpr>,
    logic: Option<String>,
}

fn collect_dl_declarations(exprs: &[SExpr]) -> DlDecls {
    let mut var_map: FxHashMap<String, u32> = FxHashMap::default();
    let mut next_id: u32 = 1;
    let mut assertions: Vec<SExpr> = Vec::new();
    let mut logic: Option<String> = None;
    for expr in exprs {
        let SExpr::List(items) = expr else { continue };
        let Some(head) = items.first().and_then(|e| e.symbol()) else {
            continue;
        };
        match head {
            "set-logic" => {
                if let Some(SExpr::Atom(Atom::Symbol(l))) = items.get(1) {
                    logic = Some(l.clone());
                }
            }
            "declare-const" | "declare-fun" => {
                if let Some(SExpr::Atom(Atom::Symbol(name))) = items.get(1) {
                    let sort = items.get(2).and_then(|e| e.symbol()).unwrap_or("");
                    if sort == "Int" || sort == "Real" {
                        var_map.entry(name.clone()).or_insert_with(|| {
                            let id = next_id;
                            next_id += 1;
                            id
                        });
                    }
                }
            }
            "assert" => {
                if let Some(body) = items.get(1) {
                    assertions.push(body.clone());
                }
            }
            _ => {}
        }
    }
    DlDecls {
        var_map,
        next_id,
        assertions,
        logic,
    }
}

/// Solve a QF_IDL SMT-LIB text. Returns the status and, on SAT, a mapping
/// from variable names to their shortest-path values from the zero node.
pub fn solve_qf_idl(text: &str) -> Result<(DlStatus, Vec<(String, i64)>), String> {
    let tokens = lex(text).map_err(|e| e.to_string())?;
    let exprs = parse_program(&tokens).map_err(|e| e.to_string())?;
    let mut decls = collect_dl_declarations(&exprs);
    match decls.logic.as_deref() {
        Some("QF_IDL") | Some("QF_RDL") | None => {}
        Some(other) => return Err(format!("DL solver does not handle logic {other}")),
    }
    if decls.assertions.is_empty() {
        return Ok((DlStatus::Sat, Vec::new()));
    }
    let num_vars = decls.next_id - 1;
    let mut solver = DiffLogicSolver::new(num_vars);
    for (next_lit, assertion) in (0_u32..).zip(decls.assertions.iter()) {
        let lit = next_lit;
        if let Err(e) = assert_one(
            &mut solver,
            assertion,
            &mut decls.var_map,
            &mut decls.next_id,
            lit,
        ) {
            match e {
                AssertError::Conflict => return Ok((DlStatus::Unsat, Vec::new())),
                AssertError::Unsupported => return Ok((DlStatus::Unknown, Vec::new())),
                AssertError::Parse(msg) => return Err(msg),
            }
        }
    }
    match solver.check() {
        Ok(()) => {}
        Err(DlError::Conflict(_)) => return Ok((DlStatus::Unsat, Vec::new())),
        Err(e) => return Err(e.to_string()),
    }
    let mut model: Vec<(String, i64)> = decls
        .var_map
        .iter()
        .filter_map(|(name, &id)| solver.var_upper_bound(id).map(|v| (name.clone(), v)))
        .collect();
    model.sort_by_key(|(n, _)| n.clone());
    Ok((DlStatus::Sat, model))
}

// ---------------------------------------------------------------------------
// Internal constraint assertion
// ---------------------------------------------------------------------------

enum AssertError {
    Conflict,
    Unsupported,
    Parse(String),
}

fn assert_one(
    solver: &mut DiffLogicSolver,
    expr: &SExpr,
    var_map: &mut FxHashMap<String, u32>,
    next_id: &mut u32,
    lit: u32,
) -> Result<(), AssertError> {
    let SExpr::List(items) = expr else {
        return Ok(());
    };
    let Some(op) = items.first().and_then(|e| e.symbol()) else {
        return Ok(());
    };

    match op {
        "and" => {
            for sub in items.iter().skip(1) {
                assert_one(solver, sub, var_map, next_id, lit)?;
            }
            Ok(())
        }
        "not" => Err(AssertError::Unsupported),
        "<=" | "<" | ">=" | ">" | "=" => {
            let lhs = items
                .get(1)
                .ok_or_else(|| AssertError::Parse("missing lhs".into()))?;
            let rhs = items
                .get(2)
                .ok_or_else(|| AssertError::Parse("missing rhs".into()))?;

            match (extract_diff(lhs), extract_diff(rhs)) {
                (Some((x_name, y_name)), _) => {
                    let c = extract_integer(rhs)?;
                    let x = intern_var(x_name, var_map, next_id);
                    let y = intern_var(y_name, var_map, next_id);
                    apply_cmp(solver, op, x, y, c, lit)
                }
                (None, Some((x_name, y_name))) => {
                    let flipped = flip_op(op);
                    let c = extract_integer(lhs).unwrap_or(0);
                    let x = intern_var(x_name, var_map, next_id);
                    let y = intern_var(y_name, var_map, next_id);
                    apply_cmp(solver, flipped, x, y, c, lit)
                }
                (None, None) => {
                    let lhs_var = lhs.symbol();
                    let rhs_var = rhs.symbol().filter(|s| s.parse::<i64>().is_err());
                    match (lhs_var, rhs_var) {
                        (Some(xn), Some(yn)) => {
                            let x = intern_var(xn, var_map, next_id);
                            let y = intern_var(yn, var_map, next_id);
                            apply_cmp(solver, op, x, y, 0, lit)
                        }
                        (Some(xn), None) => {
                            let c = extract_integer(rhs)?;
                            let x = intern_var(xn, var_map, next_id);
                            apply_cmp(solver, op, x, 0, c, lit)
                        }
                        (None, Some(yn)) => {
                            let c = extract_integer(lhs)?;
                            let y = intern_var(yn, var_map, next_id);
                            apply_cmp(solver, flip_op(op), y, 0, c, lit)
                        }
                        _ => Err(AssertError::Unsupported),
                    }
                }
            }
        }
        _ => Ok(()),
    }
}

/// Apply a comparison `op` on `x op_cmp y` with bound c.
/// x, y are VarIds (0 = zero constant).
fn apply_cmp(
    solver: &mut DiffLogicSolver,
    op: &str,
    x: u32,
    y: u32,
    c: i64,
    lit: u32,
) -> Result<(), AssertError> {
    match op {
        "<=" => dl_assert(solver, x, y, c, lit),
        "<" => dl_assert(solver, x, y, c - 1, lit),
        ">=" => dl_assert(solver, y, x, -c, lit),
        ">" => dl_assert(solver, y, x, -c - 1, lit),
        "=" => {
            dl_assert(solver, x, y, c, lit)?;
            dl_assert(solver, y, x, -c, lit)
        }
        _ => Ok(()),
    }
}

fn dl_assert(
    solver: &mut DiffLogicSolver,
    x: u32,
    y: u32,
    c: i64,
    lit: u32,
) -> Result<(), AssertError> {
    solver.assert_leq(x, y, c, lit).map_err(|e| match e {
        DlError::Conflict(_) => AssertError::Conflict,
        _ => AssertError::Parse(e.to_string()),
    })
}

/// Extract `(- x y)` → Some(("x", "y")); None if pattern doesn't match.
fn extract_diff(expr: &SExpr) -> Option<(&str, &str)> {
    let SExpr::List(items) = expr else {
        return None;
    };
    if items.len() != 3 {
        return None;
    }
    if items[0].symbol() != Some("-") {
        return None;
    }
    let x = items[1].symbol()?;
    let y = items[2].symbol()?;
    Some((x, y))
}

fn extract_integer(expr: &SExpr) -> Result<i64, AssertError> {
    match expr {
        SExpr::Atom(Atom::Numeral(n)) => {
            i64::try_from(*n).map_err(|_| AssertError::Parse("numeral too large for i64".into()))
        }
        SExpr::List(items) if items.len() == 2 && items[0].symbol() == Some("-") => {
            if let SExpr::Atom(Atom::Numeral(n)) = &items[1] {
                let v =
                    i64::try_from(*n).map_err(|_| AssertError::Parse("numeral overflow".into()))?;
                Ok(-v)
            } else {
                Err(AssertError::Unsupported)
            }
        }
        SExpr::Atom(Atom::Symbol(s)) => s.parse::<i64>().map_err(|_| AssertError::Unsupported),
        _ => Err(AssertError::Unsupported),
    }
}

fn intern_var(name: &str, map: &mut FxHashMap<String, u32>, next_id: &mut u32) -> u32 {
    *map.entry(name.to_owned()).or_insert_with(|| {
        let id = *next_id;
        *next_id += 1;
        id
    })
}

fn flip_op(op: &str) -> &'static str {
    match op {
        "<=" => ">=",
        "<" => ">",
        ">=" => "<=",
        ">" => "<",
        _ => "=",
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn check(text: &str) -> DlStatus {
        solve_qf_idl(text).unwrap().0
    }

    #[test]
    fn simple_sat() {
        let (status, model) = solve_qf_idl(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (<= (- x y) 5))
             (assert (<= (- y x) 3))
             (check-sat)",
        )
        .unwrap();
        assert_eq!(status, DlStatus::Sat);
        assert!(!model.is_empty());
    }

    #[test]
    fn simple_unsat() {
        // x - y ≤ 1, y - x ≤ -3 → cycle weight -2 < 0 → UNSAT
        let status = check(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (<= (- x y) 1))
             (assert (<= (- y x) -3))
             (check-sat)",
        );
        assert_eq!(status, DlStatus::Unsat);
    }

    #[test]
    fn equality_sat() {
        // x = y and x - z ≤ 0, z - y ≤ 0
        let status = check(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (declare-const z Int)
             (assert (= x y))
             (assert (<= (- x z) 0))
             (assert (<= (- z y) 0))
             (check-sat)",
        );
        assert_eq!(status, DlStatus::Sat);
    }

    #[test]
    fn equality_unsat() {
        // x = y, but x - y ≤ -1 (contradicts x = y which asserts x - y ≤ 0 & y - x ≤ 0)
        let status = check(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (= x y))
             (assert (<= (- x y) -1))
             (check-sat)",
        );
        assert_eq!(status, DlStatus::Unsat);
    }

    #[test]
    fn strict_lt_sat() {
        let status = check(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (< (- x y) 10))
             (check-sat)",
        );
        assert_eq!(status, DlStatus::Sat);
    }

    #[test]
    fn upper_bound() {
        // x ≤ 5 (x - 0 ≤ 5)
        let (status, model) = solve_qf_idl(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (assert (<= x 5))
             (check-sat)",
        )
        .unwrap();
        assert_eq!(status, DlStatus::Sat);
        let x_val = model.iter().find(|(n, _)| n == "x").map(|(_, v)| *v);
        assert!(
            x_val.is_some_and(|v| v <= 5),
            "model x={x_val:?} should be ≤ 5"
        );
    }

    #[test]
    fn and_conjunction() {
        let status = check(
            "(set-logic QF_IDL)
             (declare-const a Int)
             (declare-const b Int)
             (assert (and (<= (- a b) 4) (<= (- b a) 2)))
             (check-sat)",
        );
        assert_eq!(status, DlStatus::Sat);
    }

    #[test]
    fn negated_constant() {
        // (assert (<= (- x y) (- 3))) → x - y ≤ -3
        // Combined with y - x ≤ 2: cycle -1 < 0 → UNSAT
        let status = check(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (<= (- x y) (- 3)))
             (assert (<= (- y x) 2))
             (check-sat)",
        );
        assert_eq!(status, DlStatus::Unsat);
    }
}
