//! QF_UF front end: uninterpreted functions + equality.
//!
//! Parses an SMT-LIB 2 script in the `QF_UF` logic, builds an e-graph from
//! all ground terms, then runs congruence closure to determine satisfiability.
//!
//! Supported assertions:
//!   `(= t1 t2)`         — assert t1 = t2
//!   `(not (= t1 t2))`   — assert t1 ≠ t2
//!   `(and φ1 φ2 …)`     — conjunction (expanded recursively)
//!
//! Declarations:
//!   `(declare-sort S 0)` — declare a sort (tracked but not type-checked here)
//!   `(declare-const a S)` / `(declare-fun f (S1 S2) S)` — declare functions
//!
//! Model for SAT: mapping from term names to their e-class representative name.

use rm_syntax::{lex, parse_program, Atom, SExpr};
use rm_theory_euf::{CongruenceClosure, EGraph};
use rustc_hash::FxHashMap;

/// Status returned by the QF_UF solver.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UfStatus {
    Sat,
    Unsat,
    Unknown,
}

/// A solved QF_UF result.
pub struct UfResult {
    pub status: UfStatus,
    /// On SAT: mapping (term_str → representative_name).
    pub model: Vec<(String, String)>,
}

/// Solve a QF_UF SMT-LIB script.
pub fn solve_qf_uf(text: &str) -> Result<UfResult, String> {
    let tokens = lex(text).map_err(|e| e.to_string())?;
    let exprs = parse_program(&tokens).map_err(|e| e.to_string())?;

    // -----------------------------------------------------------------------
    // Pass 1: collect declarations
    // -----------------------------------------------------------------------
    // function name → arity (0 = constant)
    let mut func_arity: FxHashMap<String, u32> = FxHashMap::default();
    let mut assertions: Vec<SExpr> = Vec::new();
    let mut logic: Option<String> = None;

    for expr in &exprs {
        let SExpr::List(items) = expr else { continue };
        let Some(head) = items.first().and_then(|e| e.symbol()) else { continue };

        match head {
            "set-logic" => {
                if let Some(SExpr::Atom(Atom::Symbol(l))) = items.get(1) {
                    logic = Some(l.clone());
                }
            }
            "declare-sort" => {
                // (declare-sort Name arity) — just accept, don't type-check
            }
            "declare-const" => {
                // (declare-const name sort)
                if let Some(SExpr::Atom(Atom::Symbol(name))) = items.get(1) {
                    func_arity.insert(name.clone(), 0);
                }
            }
            "declare-fun" => {
                // (declare-fun name (arg-sorts) result-sort)
                if let Some(SExpr::Atom(Atom::Symbol(name))) = items.get(1) {
                    let arity = match items.get(2) {
                        Some(SExpr::List(args)) => args.len() as u32,
                        _ => 0,
                    };
                    func_arity.insert(name.clone(), arity);
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

    // Validate logic.
    match logic.as_deref() {
        Some("QF_UF") | None => {}
        Some(other) => return Err(format!("UF solver does not handle logic {other}")),
    }

    if assertions.is_empty() {
        return Ok(UfResult { status: UfStatus::Sat, model: Vec::new() });
    }

    // -----------------------------------------------------------------------
    // Pass 2: intern all terms into the e-graph
    // -----------------------------------------------------------------------
    let mut egraph = EGraph::new();
    let mut cc = CongruenceClosure::new(64);
    // term_str → ENodeId (for model output)
    let mut term_cache: FxHashMap<String, rm_theory_euf::ENodeId> = FxHashMap::default();

    // Pre-intern all declared 0-arity constants so they exist even if only
    // referenced inside compound terms.
    for (name, arity) in &func_arity {
        if *arity == 0 {
            let id = egraph.constant(name);
            term_cache.insert(name.clone(), id);
        }
    }

    // Now intern each assertion's terms.
    for body in &assertions {
        intern_assertion_terms(body, &func_arity, &mut egraph, &mut term_cache);
    }

    // Register all e-nodes with the CC (topological order = ENodeId order).
    for id in egraph.all_ids() {
        let node = egraph.node(id).clone();
        cc.add_term(id, &node);
    }

    // -----------------------------------------------------------------------
    // Pass 3: assert equalities / disequalities
    // -----------------------------------------------------------------------
    let mut next_lit: u32 = 0;

    for body in &assertions {
        let lit = next_lit;
        next_lit += 1;
        match assert_one(&mut cc, &egraph, body, &term_cache, lit) {
            Ok(()) => {}
            Err(AssertErr::Conflict) => {
                return Ok(UfResult { status: UfStatus::Unsat, model: Vec::new() });
            }
            Err(AssertErr::Unsupported) => {
                return Ok(UfResult { status: UfStatus::Unknown, model: Vec::new() });
            }
            Err(AssertErr::Parse(msg)) => return Err(msg),
        }
    }

    // -----------------------------------------------------------------------
    // Build SAT model: each constant maps to its class representative name.
    // -----------------------------------------------------------------------
    let mut model: Vec<(String, String)> = func_arity
        .iter()
        .filter(|(_, &a)| a == 0)
        .filter_map(|(name, _)| {
            let id = *term_cache.get(name)?;
            let rep = cc.repr(id);
            // Find the name of the representative.
            let rep_name = term_cache
                .iter()
                .find(|(_, &v)| v == rep)
                .map(|(k, _)| k.clone())
                .unwrap_or_else(|| format!("class_{}", rep.0));
            Some((name.clone(), rep_name))
        })
        .collect();
    model.sort_by_key(|(n, _)| n.clone());

    Ok(UfResult { status: UfStatus::Sat, model })
}

// ---------------------------------------------------------------------------
// Recursive term interning
// ---------------------------------------------------------------------------

/// Intern all sub-terms of an assertion into the e-graph (pre-pass).
/// This ensures all ENodeIds exist before we run CC.
fn intern_assertion_terms(
    expr: &SExpr,
    func_arity: &FxHashMap<String, u32>,
    egraph: &mut EGraph,
    cache: &mut FxHashMap<String, rm_theory_euf::ENodeId>,
) {
    match expr {
        SExpr::List(items) => {
            let head = items.first().and_then(|e| e.symbol());
            match head {
                Some("=") | Some("not") | Some("and") | Some("or") => {
                    // Boolean connectives: recurse into subterms
                    for sub in items.iter().skip(1) {
                        intern_assertion_terms(sub, func_arity, egraph, cache);
                    }
                }
                Some(fname) => {
                    // Theory-level function application: intern args first, then self
                    let mut arg_ids = Vec::new();
                    for arg in items.iter().skip(1) {
                        intern_term(arg, func_arity, egraph, cache);
                        let key = sexpr_to_key(arg);
                        if let Some(&id) = cache.get(&key) {
                            arg_ids.push(id);
                        }
                    }
                    if !arg_ids.is_empty() {
                        let key = sexpr_to_key(expr);
                        if !cache.contains_key(&key) {
                            let id = egraph.apply(fname, &arg_ids);
                            cache.insert(key, id);
                        }
                    }
                }
                None => {}
            }
        }
        SExpr::Atom(Atom::Symbol(name)) => {
            if func_arity.get(name).map(|&a| a == 0).unwrap_or(false) {
                if !cache.contains_key(name) {
                    let id = egraph.constant(name);
                    cache.insert(name.clone(), id);
                }
            }
        }
        _ => {}
    }
}

/// Recursively intern a theory term (not a boolean connective) into the e-graph.
fn intern_term(
    expr: &SExpr,
    func_arity: &FxHashMap<String, u32>,
    egraph: &mut EGraph,
    cache: &mut FxHashMap<String, rm_theory_euf::ENodeId>,
) {
    let key = sexpr_to_key(expr);
    if cache.contains_key(&key) {
        return;
    }
    match expr {
        SExpr::Atom(Atom::Symbol(name)) => {
            let id = egraph.constant(name);
            cache.insert(name.clone(), id);
        }
        SExpr::List(items) => {
            let fname = match items.first().and_then(|e| e.symbol()) {
                Some(s) => s,
                None => return,
            };
            // Recurse into args first.
            for arg in items.iter().skip(1) {
                intern_term(arg, func_arity, egraph, cache);
            }
            // Collect arg IDs.
            let arg_ids: Vec<rm_theory_euf::ENodeId> = items
                .iter()
                .skip(1)
                .filter_map(|a| cache.get(&sexpr_to_key(a)).copied())
                .collect();
            let id = egraph.apply(fname, &arg_ids);
            cache.insert(key, id);
        }
        _ => {}
    }
}

/// Produce a canonical string key for an S-expression (for caching).
fn sexpr_to_key(expr: &SExpr) -> String {
    match expr {
        SExpr::Atom(Atom::Symbol(s)) => s.clone(),
        SExpr::Atom(Atom::Numeral(n)) => n.to_string(),
        SExpr::List(items) => {
            let parts: Vec<String> = items.iter().map(sexpr_to_key).collect();
            format!("({})", parts.join(" "))
        }
        _ => "_".to_owned(),
    }
}

// ---------------------------------------------------------------------------
// Assertion dispatch
// ---------------------------------------------------------------------------

enum AssertErr {
    Conflict,
    Unsupported,
    Parse(String),
}

fn assert_one(
    cc: &mut CongruenceClosure,
    egraph: &EGraph,
    expr: &SExpr,
    cache: &FxHashMap<String, rm_theory_euf::ENodeId>,
    lit: u32,
) -> Result<(), AssertErr> {
    let SExpr::List(items) = expr else {
        // bare Bool atom: true/false — treat as tautology / contradiction-free
        return Ok(());
    };
    let Some(op) = items.first().and_then(|e| e.symbol()) else {
        return Ok(());
    };

    match op {
        "and" => {
            for sub in items.iter().skip(1) {
                assert_one(cc, egraph, sub, cache, lit)?;
            }
            Ok(())
        }
        "not" => {
            // (not (= t1 t2))
            let inner = items.get(1).ok_or_else(|| AssertErr::Parse("not: missing body".into()))?;
            let SExpr::List(inner_items) = inner else { return Err(AssertErr::Unsupported); };
            if inner_items.first().and_then(|e| e.symbol()) != Some("=") {
                return Err(AssertErr::Unsupported);
            }
            let lhs = inner_items.get(1).ok_or_else(|| AssertErr::Parse("=: missing lhs".into()))?;
            let rhs = inner_items.get(2).ok_or_else(|| AssertErr::Parse("=: missing rhs".into()))?;
            let l = resolve(lhs, cache)?;
            let r = resolve(rhs, cache)?;
            cc.assert_neq(egraph, l, r, lit).map_err(|_| AssertErr::Conflict)
        }
        "=" => {
            let lhs = items.get(1).ok_or_else(|| AssertErr::Parse("=: missing lhs".into()))?;
            let rhs = items.get(2).ok_or_else(|| AssertErr::Parse("=: missing rhs".into()))?;
            let l = resolve(lhs, cache)?;
            let r = resolve(rhs, cache)?;
            cc.assert_eq(egraph, l, r, lit).map_err(|_| AssertErr::Conflict)
        }
        _ => Err(AssertErr::Unsupported),
    }
}

fn resolve(
    expr: &SExpr,
    cache: &FxHashMap<String, rm_theory_euf::ENodeId>,
) -> Result<rm_theory_euf::ENodeId, AssertErr> {
    let key = sexpr_to_key(expr);
    cache
        .get(&key)
        .copied()
        .ok_or_else(|| AssertErr::Parse(format!("term not interned: {key}")))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn check(text: &str) -> UfStatus {
        solve_qf_uf(text).unwrap().status
    }

    #[test]
    fn simple_sat() {
        // a = b, and nothing contradicts it
        let status = check(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (assert (= a b))
             (check-sat)",
        );
        assert_eq!(status, UfStatus::Sat);
    }

    #[test]
    fn simple_unsat() {
        // a = b AND a ≠ b → UNSAT
        let status = check(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (assert (= a b))
             (assert (not (= a b)))
             (check-sat)",
        );
        assert_eq!(status, UfStatus::Unsat);
    }

    #[test]
    fn congruence_sat() {
        // a = b → f(a) = f(b), no contradiction
        let status = check(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (declare-fun f (U) U)
             (assert (= a b))
             (check-sat)",
        );
        assert_eq!(status, UfStatus::Sat);
    }

    #[test]
    fn congruence_unsat() {
        // a = b, f(a) ≠ f(b) → congruence conflict
        let status = check(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (declare-fun f (U) U)
             (assert (= a b))
             (assert (not (= (f a) (f b))))
             (check-sat)",
        );
        assert_eq!(status, UfStatus::Unsat);
    }

    #[test]
    fn transitivity_sat() {
        // a=b, b=c, nothing contradicts a=c
        let status = check(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (declare-fun c () U)
             (assert (= a b))
             (assert (= b c))
             (check-sat)",
        );
        assert_eq!(status, UfStatus::Sat);
    }

    #[test]
    fn transitivity_unsat() {
        // a=b, b=c, a≠c → UNSAT
        let status = check(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (declare-fun c () U)
             (assert (= a b))
             (assert (= b c))
             (assert (not (= a c)))
             (check-sat)",
        );
        assert_eq!(status, UfStatus::Unsat);
    }

    #[test]
    fn function_arity2() {
        // f(a,b) = f(b,a) in general is not valid; assert both equal and check
        let status = check(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (declare-fun f (U U) U)
             (assert (= (f a b) (f a b)))
             (check-sat)",
        );
        assert_eq!(status, UfStatus::Sat);
    }

    #[test]
    fn model_reflects_classes() {
        let result = solve_qf_uf(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (assert (= a b))
             (check-sat)",
        )
        .unwrap();
        assert_eq!(result.status, UfStatus::Sat);
        // a and b should map to the same representative.
        let rep_a = result.model.iter().find(|(n, _)| n == "a").map(|(_, r)| r);
        let rep_b = result.model.iter().find(|(n, _)| n == "b").map(|(_, r)| r);
        assert_eq!(rep_a, rep_b, "a and b should be in the same class after assert (= a b)");
    }

    #[test]
    fn empty_problem_is_sat() {
        let result = solve_qf_uf("(set-logic QF_UF)").unwrap();
        assert_eq!(result.status, UfStatus::Sat);
    }

    #[test]
    fn nested_application_unsat() {
        // f(f(a)) = a, f(a) ≠ a, f(f(f(a))) ≠ f(a)? No — let's do a simple one:
        // f(a) = a, a ≠ f(a) → UNSAT
        let status = check(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun f (U) U)
             (assert (= (f a) a))
             (assert (not (= a (f a))))
             (check-sat)",
        );
        assert_eq!(status, UfStatus::Unsat);
    }
}
