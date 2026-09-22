//! CDCL(T) engine and Nelson-Oppen combination for QF_UFIDL.
//!
//! # Theory combination (Nelson-Oppen protocol)
//!
//! Two theories share the same arithmetic variable namespace:
//!   T1 — EUF (congruence closure, rm-theory-euf)
//!   T2 — QF_IDL (incremental Bellman-Ford, rm-theory-arith)
//!
//! When EUF derives that two arithmetic-sort variables are equal (their
//! e-classes merge), it propagates `x - y ≤ 0 ∧ y - x ≤ 0` to DL.
//! When DL's potential analysis tightens both `x - y ≤ 0` and `y - x ≤ 0`
//! to saturation, it reports `x = y` back to EUF.  The loop runs to a
//! fixed point (at most n² equality checks for n shared variables).
//!
//! # Scope
//!
//! Conjunctive QF_UFIDL (AND of theory literals) is handled with a direct
//! NO fixed-point loop — no SAT backbone needed.  General Boolean structure
//! (with disjunctions) uses a lazy CDCL(T) backbone where theory conflict
//! clauses are added as blocking clauses.  The lazy variant returns Unknown
//! for formulas that require more than `MAX_CDCLT_ITERS` SAT restarts.

use rm_akx::literal::Literal;
use rm_sat::{CdclSolver, SolveResult};
use rm_theory_arith::{DiffLogicSolver, DlError};
use rm_theory_euf::{CongruenceClosure, EGraph, ENodeId};
use rustc_hash::FxHashMap;

// ---------------------------------------------------------------------------
// Result type
// ---------------------------------------------------------------------------

/// Result of the Nelson-Oppen QF_UFIDL solve.
#[derive(Debug, PartialEq, Eq)]
pub enum NoResult {
    Sat,
    Unsat,
    /// Formula is non-conjunctive and exceeds the lazy CDCL(T) iteration budget.
    Unknown,
}

// ---------------------------------------------------------------------------
// Theory literal types
// ---------------------------------------------------------------------------

/// A unit theory literal that can be routed to EUF or DL.
#[derive(Clone, Debug)]
enum TheoryLit {
    /// EUF equality: `lhs = rhs` (polarity false → disequality).
    Eq {
        lhs: ENodeId,
        rhs: ENodeId,
        polarity: bool,
        sat_var: u32,
    },
    /// Arithmetic `x - y ≤ c`.  polarity=false means `¬(x-y≤c)` = `y-x ≤ -c-1`.
    Leq {
        x: u32,
        y: u32,
        c: i64,
        polarity: bool,
        sat_var: u32,
    },
    /// Arithmetic `x - y < c`. polarity=false means `y - x ≤ -c`.
    Lt {
        x: u32,
        y: u32,
        c: i64,
        polarity: bool,
        sat_var: u32,
    },
}

// ---------------------------------------------------------------------------
// Nelson-Oppen combined solver (conjunctive fragment)
// ---------------------------------------------------------------------------

/// Combined EUF + DL solver implementing the Nelson-Oppen protocol.
pub struct NoCombinedSolver {
    /// E-graph for term storage.
    pub egraph: EGraph,
    /// Congruence closure for EUF reasoning.
    pub cc: CongruenceClosure,
    /// Difference-logic Bellman-Ford solver.
    pub dl: DiffLogicSolver,
    /// Arithmetic variable names → (dl_var_id, uf_node_id).
    arith_terms: FxHashMap<String, (u32, ENodeId)>,
    /// Next SAT literal index (used as conflict explanation tags).
    next_sat_lit: u32,
}

impl NoCombinedSolver {
    pub fn new(num_arith_vars: u32) -> Self {
        NoCombinedSolver {
            egraph: EGraph::new(),
            cc: CongruenceClosure::new(64),
            dl: DiffLogicSolver::new(num_arith_vars),
            arith_terms: FxHashMap::default(),
            next_sat_lit: 1,
        }
    }

    fn fresh_lit(&mut self) -> u32 {
        let v = self.next_sat_lit;
        self.next_sat_lit += 1;
        v
    }

    /// Register an arithmetic variable as shared between DL and UF.
    /// Returns the UF ENodeId for the variable.
    pub fn register_shared_var(&mut self, name: &str, dl_id: u32) -> ENodeId {
        if let Some(&(_, uid)) = self.arith_terms.get(name) {
            return uid;
        }
        let uid = self.egraph.constant(name);
        let node = self.egraph.node(uid).clone();
        self.cc.add_term(uid, &node);
        self.arith_terms.insert(name.to_string(), (dl_id, uid));
        uid
    }

    /// Run the Nelson-Oppen fixed-point loop: share derived equalities between
    /// EUF and DL until no new propagations occur.
    fn no_fixed_point(&mut self) -> Result<(), ()> {
        for _ in 0..1000 {
            let new_eqs = self.dl_derived_equalities();
            if new_eqs.is_empty() {
                return Ok(());
            }
            for (xname, yname) in new_eqs {
                let xid = self.get_or_create_uf_node(&xname);
                let yid = self.get_or_create_uf_node(&yname);
                let sat_lit = self.fresh_lit();
                self.cc
                    .assert_eq(&self.egraph, xid, yid, sat_lit)
                    .map_err(|_| ())?;
            }
        }
        Ok(())
    }

    fn get_or_create_uf_node(&mut self, name: &str) -> ENodeId {
        if let Some(&(_, uid)) = self.arith_terms.get(name) {
            return uid;
        }
        let id = self.egraph.constant(name);
        let node = self.egraph.node(id).clone();
        self.cc.add_term(id, &node);
        id
    }

    /// Check which pairs of shared arithmetic variables have tight DL bounds
    /// implying equality (both x-y≤0 and y-x≤0 are derivable via shortest paths).
    fn dl_derived_equalities(&mut self) -> Vec<(String, String)> {
        let shared: Vec<(String, u32, ENodeId)> = self
            .arith_terms
            .iter()
            .map(|(n, &(dl, uid))| (n.clone(), dl, uid))
            .collect();

        let mut derived = Vec::new();
        for i in 0..shared.len() {
            for j in (i + 1)..shared.len() {
                let (xname, xi, xuid) = &shared[i];
                let (yname, yi, yuid) = &shared[j];
                let xy_leq_0 = self
                    .dl
                    .bound_between(*yi, *xi)
                    .map(|b| b <= 0)
                    .unwrap_or(false);
                let yx_leq_0 = self
                    .dl
                    .bound_between(*xi, *yi)
                    .map(|b| b <= 0)
                    .unwrap_or(false);
                if xy_leq_0 && yx_leq_0 && !self.cc.are_equal(*xuid, *yuid) {
                    derived.push((xname.clone(), yname.clone()));
                }
            }
        }
        derived
    }

    /// After EUF merges two arithmetic-sort nodes, propagate the equality
    /// to DL as x - y ≤ 0 ∧ y - x ≤ 0.
    fn euf_propagate_to_dl(&mut self) -> Result<(), ()> {
        let shared: Vec<(u32, u32, ENodeId, ENodeId)> = self
            .arith_terms
            .values()
            .flat_map(|&(xi, xuid)| {
                self.arith_terms.values().filter_map(move |&(yi, yuid)| {
                    if xi < yi {
                        Some((xi, yi, xuid, yuid))
                    } else {
                        None
                    }
                })
            })
            .collect();

        for (xi, yi, xuid, yuid) in shared {
            if self.cc.are_equal(xuid, yuid) {
                let already = self
                    .dl
                    .bound_between(yi, xi)
                    .map(|b| b <= 0)
                    .unwrap_or(false)
                    && self
                        .dl
                        .bound_between(xi, yi)
                        .map(|b| b <= 0)
                        .unwrap_or(false);
                if !already {
                    let sat = self.fresh_lit();
                    self.dl.assert_leq(xi, yi, 0, sat).map_err(|_| ())?;
                    let sat2 = self.fresh_lit();
                    self.dl.assert_leq(yi, xi, 0, sat2).map_err(|_| ())?;
                }
            }
        }
        Ok(())
    }

    /// Assert a theory literal to the appropriate solver.
    fn assert_lit(&mut self, lit: &TheoryLit) -> Result<(), ()> {
        match *lit {
            TheoryLit::Eq {
                lhs,
                rhs,
                polarity,
                sat_var,
            } => {
                if polarity {
                    self.cc
                        .assert_eq(&self.egraph, lhs, rhs, sat_var)
                        .map_err(|_| ())?;
                } else {
                    self.cc
                        .assert_neq(&self.egraph, lhs, rhs, sat_var)
                        .map_err(|_| ())?;
                }
                self.euf_propagate_to_dl()?;
            }
            TheoryLit::Leq {
                x,
                y,
                c,
                polarity,
                sat_var,
            } => {
                let res = if polarity {
                    self.dl.assert_leq(x, y, c, sat_var)
                } else {
                    self.dl.assert_leq(y, x, -c - 1, sat_var)
                };
                res.map_err(|_| ())?;
            }
            TheoryLit::Lt {
                x,
                y,
                c,
                polarity,
                sat_var,
            } => {
                let res = if polarity {
                    self.dl.assert_leq(x, y, c - 1, sat_var)
                } else {
                    self.dl.assert_leq(y, x, -c, sat_var)
                };
                res.map_err(|_| ())?;
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Parsed SMT-LIB declarations
// ---------------------------------------------------------------------------

/// Declarations extracted from a parsed SMT-LIB script.
struct SmtLibDecls {
    uf_funcs: FxHashMap<String, u32>,
    dl_vars: FxHashMap<String, u32>,
    assertions: Vec<rm_syntax::SExpr>,
    logic: Option<String>,
}

/// Parse `declare-const`, `declare-fun`, and `assert` commands from a
/// sequence of SMT-LIB s-expressions.
fn parse_smtlib_decls(exprs: &[rm_syntax::SExpr]) -> SmtLibDecls {
    use rm_syntax::{Atom, SExpr};
    let mut uf_funcs: FxHashMap<String, u32> = FxHashMap::default();
    let mut dl_vars: FxHashMap<String, u32> = FxHashMap::default();
    let mut next_dl_id: u32 = 1;
    let mut assertions = Vec::new();
    let mut logic = None;

    for expr in exprs {
        let SExpr::List(items) = expr else { continue };
        let Some(head) = items.first().and_then(|e| sexpr_symbol(e)) else {
            continue;
        };
        match head {
            "set-logic" => {
                if let Some(SExpr::Atom(Atom::Symbol(l))) = items.get(1) {
                    logic = Some(l.clone());
                }
            }
            "declare-sort" => {}
            "declare-const" => {
                if let Some(SExpr::Atom(Atom::Symbol(name))) = items.get(1) {
                    let sort = items.get(2).and_then(|e| sexpr_symbol(e)).unwrap_or("");
                    if sort == "Int" || sort == "Real" {
                        dl_vars.entry(name.clone()).or_insert_with(|| {
                            let id = next_dl_id;
                            next_dl_id += 1;
                            id
                        });
                    } else {
                        uf_funcs.insert(name.clone(), 0);
                    }
                }
            }
            "declare-fun" => {
                if let Some(SExpr::Atom(Atom::Symbol(name))) = items.get(1) {
                    let arity = match items.get(2) {
                        Some(SExpr::List(args)) => args.len() as u32,
                        _ => 0,
                    };
                    let result_sort = items.get(3).and_then(|e| sexpr_symbol(e)).unwrap_or("");
                    if result_sort == "Int" || result_sort == "Real" {
                        dl_vars.entry(name.clone()).or_insert_with(|| {
                            let id = next_dl_id;
                            next_dl_id += 1;
                            id
                        });
                    } else {
                        uf_funcs.insert(name.clone(), arity);
                    }
                }
            }
            "assert" => {
                if let Some(body) = items.get(1) {
                    assertions.push(rm_syntax::preprocess(body));
                }
            }
            _ => {}
        }
    }

    SmtLibDecls {
        uf_funcs,
        dl_vars,
        assertions,
        logic,
    }
}

/// Intern UF constants and register all arithmetic variables as shared
/// between DL and UF. Returns the UF term cache for assertion flattening.
fn intern_no_declarations(
    solver: &mut NoCombinedSolver,
    decls: &SmtLibDecls,
) -> FxHashMap<String, ENodeId> {
    let mut uf_cache: FxHashMap<String, ENodeId> = FxHashMap::default();
    for (name, arity) in &decls.uf_funcs {
        if *arity == 0 {
            let id = solver.egraph.constant(name);
            let node = solver.egraph.node(id).clone();
            solver.cc.add_term(id, &node);
            uf_cache.insert(name.clone(), id);
        }
    }
    for (name, &dl_id) in &decls.dl_vars {
        let uid = solver.register_shared_var(name, dl_id);
        uf_cache.insert(name.clone(), uid);
    }
    uf_cache
}

// ---------------------------------------------------------------------------
// Conjunctive QF_UFIDL solver (main entry point)
// ---------------------------------------------------------------------------

/// Parse and solve a QF_UFIDL (or QF_UF / QF_IDL) SMT-LIB script.
/// Returns `(verdict, dl_model)` where `dl_model` maps var names to integer values on SAT.
pub fn solve_qf_ufidl(text: &str, max_conflicts: u64) -> Result<(NoResult, Vec<(String, i64)>), String> {
    use rm_syntax::{lex, parse_program};

    let tokens = lex(text).map_err(|e| e.to_string())?;
    let exprs = parse_program(&tokens).map_err(|e| e.to_string())?;
    let decls = parse_smtlib_decls(&exprs);

    match decls.logic.as_deref() {
        Some("QF_UFIDL") | Some("QF_UF") | Some("QF_IDL") | None => {}
        Some(other) => return Err(format!("NO solver does not handle logic {other}")),
    }

    if decls.assertions.is_empty() {
        return Ok((NoResult::Sat, Vec::new()));
    }

    let num_arith = decls.dl_vars.values().copied().max().unwrap_or(0);
    let mut solver = NoCombinedSolver::new(num_arith);
    let mut uf_cache = intern_no_declarations(&mut solver, &decls);

    let mut all_literals: Vec<TheoryLit> = Vec::new();
    let mut has_disjunctions = false;
    for assertion in &decls.assertions {
        let mut lits: Vec<TheoryLit> = Vec::new();
        match flatten_assertion(
            assertion,
            true,
            &mut solver,
            &mut uf_cache,
            &decls.uf_funcs,
            &decls.dl_vars,
            &mut lits,
        ) {
            FlattenResult::Ok => all_literals.extend(lits),
            FlattenResult::Conflict => return Ok((NoResult::Unsat, Vec::new())),
            // Unsupported in the flat path → try the full CDCL(T) backbone,
            // which handles Bool atoms, implication, xor, etc.
            FlattenResult::Disjunction | FlattenResult::Unsupported => {
                has_disjunctions = true;
                break;
            }
        }
    }

    if has_disjunctions {
        return solve_with_cdclt(text, max_conflicts);
    }

    for lit in &all_literals {
        if solver.assert_lit(lit).is_err() {
            return Ok((NoResult::Unsat, Vec::new()));
        }
    }
    if solver.dl.check().is_err() || solver.no_fixed_point().is_err() {
        return Ok((NoResult::Unsat, Vec::new()));
    }
    let mut dl_model: Vec<(String, i64)> = decls
        .dl_vars
        .iter()
        .filter_map(|(name, &id)| solver.dl.var_upper_bound(id).map(|v| (name.clone(), v)))
        .collect();
    dl_model.sort_by_key(|(n, _)| n.clone());
    Ok((NoResult::Sat, dl_model))
}

// ---------------------------------------------------------------------------
// Flatten assertions into conjunctive literals
// ---------------------------------------------------------------------------

enum FlattenResult {
    Ok,
    /// Assertion is unconditionally false (e.g. `(assert false)`, `(assert (not true))`).
    Conflict,
    Disjunction,
    Unsupported,
}

fn flatten_assertion(
    expr: &rm_syntax::SExpr,
    polarity: bool,
    solver: &mut NoCombinedSolver,
    uf_cache: &mut FxHashMap<String, ENodeId>,
    uf_funcs: &FxHashMap<String, u32>,
    dl_vars: &FxHashMap<String, u32>,
    out: &mut Vec<TheoryLit>,
) -> FlattenResult {
    use rm_syntax::{Atom, SExpr};

    match expr {
        SExpr::Atom(Atom::Symbol(s)) if s == "true" => {
            if polarity { FlattenResult::Ok } else { FlattenResult::Conflict }
        }
        SExpr::Atom(Atom::Symbol(s)) if s == "false" => {
            if polarity { FlattenResult::Conflict } else { FlattenResult::Ok }
        }
        SExpr::List(items) => {
            let Some(op) = items.first().and_then(|e| sexpr_symbol(e)) else {
                return FlattenResult::Unsupported;
            };
            match op {
                "not" => {
                    let Some(inner) = items.get(1) else {
                        return FlattenResult::Unsupported;
                    };
                    flatten_assertion(inner, !polarity, solver, uf_cache, uf_funcs, dl_vars, out)
                }
                "and" if polarity => {
                    for sub in items.iter().skip(1) {
                        match flatten_assertion(
                            sub, polarity, solver, uf_cache, uf_funcs, dl_vars, out,
                        ) {
                            FlattenResult::Ok => {}
                            other => return other,
                        }
                    }
                    FlattenResult::Ok
                }
                "or" if !polarity => {
                    for sub in items.iter().skip(1) {
                        match flatten_assertion(
                            sub, false, solver, uf_cache, uf_funcs, dl_vars, out,
                        ) {
                            FlattenResult::Ok => {}
                            other => return other,
                        }
                    }
                    FlattenResult::Ok
                }
                "and" | "or" => FlattenResult::Disjunction,
                "=" => {
                    let Some(lhs) = items.get(1) else {
                        return FlattenResult::Unsupported;
                    };
                    let Some(rhs) = items.get(2) else {
                        return FlattenResult::Unsupported;
                    };

                    if let (Some(xn), Some(yn)) = (lhs.symbol(), rhs.symbol()) {
                        if let (Some(&xi), Some(&yi)) = (dl_vars.get(xn), dl_vars.get(yn)) {
                            if polarity {
                                let sat1 = solver.fresh_lit();
                                out.push(TheoryLit::Leq {
                                    x: xi,
                                    y: yi,
                                    c: 0,
                                    polarity: true,
                                    sat_var: sat1,
                                });
                                let sat2 = solver.fresh_lit();
                                out.push(TheoryLit::Leq {
                                    x: yi,
                                    y: xi,
                                    c: 0,
                                    polarity: true,
                                    sat_var: sat2,
                                });
                                return FlattenResult::Ok;
                            } else {
                                return FlattenResult::Disjunction;
                            }
                        }
                    }

                    let lhs_id = match intern_uf_term(lhs, solver, uf_cache, uf_funcs) {
                        Ok(id) => id,
                        Err(()) => return FlattenResult::Unsupported,
                    };
                    let rhs_id = match intern_uf_term(rhs, solver, uf_cache, uf_funcs) {
                        Ok(id) => id,
                        Err(()) => return FlattenResult::Unsupported,
                    };
                    let sat = solver.fresh_lit();
                    out.push(TheoryLit::Eq {
                        lhs: lhs_id,
                        rhs: rhs_id,
                        polarity,
                        sat_var: sat,
                    });
                    FlattenResult::Ok
                }
                "<=" | "<" | ">=" | ">" => {
                    match flatten_arith(items, op, polarity, solver, dl_vars, out) {
                        Ok(()) => FlattenResult::Ok,
                        Err(()) => FlattenResult::Unsupported,
                    }
                }
                _ => FlattenResult::Unsupported,
            }
        }
        _ => FlattenResult::Unsupported,
    }
}

fn flatten_arith(
    items: &[rm_syntax::SExpr],
    op: &str,
    polarity: bool,
    solver: &mut NoCombinedSolver,
    dl_vars: &FxHashMap<String, u32>,
    out: &mut Vec<TheoryLit>,
) -> Result<(), ()> {
    let lhs = items.get(1).ok_or(())?;
    let rhs = items.get(2).ok_or(())?;

    let (x, y, c, is_lt) = if let Some((xn, yn)) = extract_diff(lhs) {
        let c = extract_int(rhs).ok_or(())?;
        let x = *dl_vars.get(xn).ok_or(())?;
        let y = *dl_vars.get(yn).ok_or(())?;
        match op {
            "<=" => (x, y, c, false),
            "<" => (x, y, c, true),
            ">=" => (y, x, -c, false),
            ">" => (y, x, -c, true),
            _ => return Err(()),
        }
    } else if let Some(xn) = sexpr_symbol(lhs) {
        if let Some(&x) = dl_vars.get(xn) {
            let c = extract_int(rhs).ok_or(())?;
            match op {
                "<=" => (x, 0, c, false),
                "<" => (x, 0, c, true),
                ">=" => (0, x, -c, false),
                ">" => (0, x, -c, true),
                _ => return Err(()),
            }
        } else {
            return Err(());
        }
    } else {
        return Err(());
    };

    let sat = solver.fresh_lit();
    let lit = if is_lt {
        TheoryLit::Lt {
            x,
            y,
            c,
            polarity,
            sat_var: sat,
        }
    } else {
        TheoryLit::Leq {
            x,
            y,
            c,
            polarity,
            sat_var: sat,
        }
    };
    out.push(lit);
    Ok(())
}

// ---------------------------------------------------------------------------
// Lazy CDCL(T) for formulas with disjunctions
// ---------------------------------------------------------------------------


/// Theory atom registered with the CDCL(T) SAT backbone.
#[derive(Clone, Debug)]
enum BackboneAtom {
    Eq { lhs: ENodeId, rhs: ENodeId },
    Leq { x: u32, y: u32, c: i64 },
    Lt { x: u32, y: u32, c: i64 },
}

/// Lazy CDCL(T) solver.
///
/// Tseitin clauses are buffered during encoding; the SAT solver is created
/// just before the first `solve()` call so it is sized exactly to the actual
/// number of Boolean variables used.
struct CdclT {
    atoms: FxHashMap<u32, BackboneAtom>,
    egraph: EGraph,
    cc: CongruenceClosure,
    dl: DiffLogicSolver,
    next_var: u32,
    /// dl_var_id → variable name (for model extraction after SAT)
    dl_var_names: FxHashMap<u32, String>,
    /// (dl_var_id, uf_node_id) for Nelson-Oppen shared variables
    dl_uf_pairs: Vec<(u32, ENodeId)>,
    /// Buffered Tseitin clauses, added to `sat` during `finalize()`.
    pending_clauses: Vec<Vec<Literal>>,
    /// The SAT backbone — None until `finalize()` is called.
    sat: Option<CdclSolver>,
    /// Bool-sorted function applications (e.g. `(f a)` used as assertions) →
    /// SAT variable. These have no theory constraint; the SAT backbone handles them.
    bool_prop_atoms: FxHashMap<String, u32>,
    /// Reverse cache: (lhs, rhs) → sat_var for Eq atoms; avoids duplicating SAT
    /// variables when the same equality appears multiple times (e.g. after let expansion).
    eq_atom_cache: FxHashMap<(ENodeId, ENodeId), u32>,
    /// Reverse cache for Leq/Lt atoms (x, y, c, is_lt) → sat_var.
    arith_atom_cache: FxHashMap<(u32, u32, i64, bool), u32>,
}

impl CdclT {
    fn new(num_arith: u32) -> Self {
        CdclT {
            atoms: FxHashMap::default(),
            egraph: EGraph::new(),
            cc: CongruenceClosure::new(64),
            dl: DiffLogicSolver::new(num_arith),
            next_var: 1,
            dl_var_names: FxHashMap::default(),
            dl_uf_pairs: Vec::new(),
            pending_clauses: Vec::new(),
            sat: None,
            bool_prop_atoms: FxHashMap::default(),
            eq_atom_cache: FxHashMap::default(),
            arith_atom_cache: FxHashMap::default(),
        }
    }

    fn alloc_var(&mut self) -> u32 {
        let v = self.next_var;
        self.next_var += 1;
        v
    }

    /// Buffer a clause for later loading into the SAT solver.
    fn add_clause(&mut self, lits: &[Literal]) {
        self.pending_clauses.push(lits.to_vec());
    }

    /// Create the SAT solver with the exact variable count and load buffered clauses.
    /// Must be called exactly once, before `solve()`.
    fn finalize(&mut self) {
        let num_vars = self.next_var - 1;
        let mut sat = CdclSolver::new(num_vars);
        // BVE eliminates variables that theory atoms depend on; theory lemmas
        // added during solving reference those variables, so BVE is incompatible.
        sat.skip_bve();
        for clause in self.pending_clauses.drain(..) {
            sat.add_clause(&clause);
        }
        self.sat = Some(sat);
    }

    fn intern_const(&mut self, name: &str) -> ENodeId {
        let id = self.egraph.constant(name);
        let node = self.egraph.node(id).clone();
        self.cc.add_term(id, &node);
        id
    }

    fn intern_apply(&mut self, func: &str, args: &[ENodeId]) -> ENodeId {
        let id = self.egraph.apply(func, args);
        let node = self.egraph.node(id).clone();
        self.cc.add_term(id, &node);
        id
    }

    /// Check the SAT model against the theories.
    /// Returns None on consistency, or a conflict clause on violation.
    fn theory_check(&mut self, model: &rm_sat::Model) -> Option<Vec<Literal>> {
        // Undo the previous call's assertions first (using the level pushed by that call),
        // then push a fresh level so the NEXT call can undo this call's assertions.
        // Order matters: backtrack before push — otherwise we record undo.len()=N as the
        // target and backtrack immediately undoes nothing.
        self.cc.backtrack_to(0);
        self.dl.backtrack_to(0);
        self.cc.new_decision_level();
        self.dl.new_decision_level();

        let vars: Vec<u32> = self.atoms.keys().copied().collect();
        for v in vars {
            if v as usize > model.num_vars() as usize {
                continue;
            }
            let val = model.value_of(v);
            // Store raw literals (with polarity) as sat_lit tags so conflict
            // clauses can be correctly formed by negating them.
            let sat_raw = if val {
                Literal::positive(v).raw()
            } else {
                Literal::negative(v).raw()
            };
            let atom = self.atoms[&v].clone();
            match atom {
                BackboneAtom::Eq { lhs, rhs } => {
                    if val {
                        if let Err(e) = self.cc.assert_eq(&self.egraph, lhs, rhs, sat_raw) {
                            if let Some(c) = mk_conflict_euf(e) { return Some(c); }
                        }
                    } else if let Err(e) = self.cc.assert_neq(&self.egraph, lhs, rhs, sat_raw) {
                        if let Some(c) = mk_conflict_euf(e) { return Some(c); }
                    }
                }
                BackboneAtom::Leq { x, y, c } => {
                    let res = if val {
                        self.dl.assert_leq(x, y, c, sat_raw)
                    } else {
                        self.dl.assert_leq(y, x, -c - 1, sat_raw)
                    };
                    if let Err(e) = res {
                        return Some(mk_conflict_dl(e));
                    }
                }
                BackboneAtom::Lt { x, y, c } => {
                    let res = if val {
                        self.dl.assert_leq(x, y, c - 1, sat_raw)
                    } else {
                        self.dl.assert_leq(y, x, -c, sat_raw)
                    };
                    if let Err(e) = res {
                        return Some(mk_conflict_dl(e));
                    }
                }
            }
        }

        if let Err(e) = self.dl.check() {
            return Some(mk_conflict_dl(e));
        }

        // Nelson-Oppen: propagate DL-derived equalities to EUF.
        // If DL has tight bounds x-y≤0 and y-x≤0, assert x=y to EUF.
        for i in 0..self.dl_uf_pairs.len() {
            for j in (i + 1)..self.dl_uf_pairs.len() {
                let (xi, xuid) = self.dl_uf_pairs[i];
                let (yi, yuid) = self.dl_uf_pairs[j];
                let xy_tight = self.dl.bound_between(yi, xi).map(|b| b <= 0).unwrap_or(false);
                let yx_tight = self.dl.bound_between(xi, yi).map(|b| b <= 0).unwrap_or(false);
                if xy_tight && yx_tight && !self.cc.are_equal(xuid, yuid) {
                    // DL says xi = yi; collect the edge lits that justify both paths
                    let mut dl_lits: Vec<u32> = Vec::new();
                    if let Some(p) = self.dl.path_explanation(yi, xi) {
                        dl_lits.extend(p);
                    }
                    if let Some(p) = self.dl.path_explanation(xi, yi) {
                        dl_lits.extend(p);
                    }
                    let tag = dl_lits.first().copied().unwrap_or(0);
                    if let Err(e) = self.cc.assert_eq(&self.egraph, xuid, yuid, tag) {
                        if let Some(mut conflict) = mk_conflict_euf(e) {
                            // dl_lits are raw literals; negate to form blocking clause
                            conflict.extend(dl_lits.iter().map(|&raw| Literal::from_raw(raw).negate()));
                            conflict.sort_unstable();
                            conflict.dedup();
                            return Some(conflict);
                        }
                    }
                }
            }
        }

        None
    }

    fn solve(&mut self, max_conflicts: u64) -> NoResult {
        self.finalize();
        let batch = 500_000u64;
        let mut sat_conflicts = 0u64;
        // Each theory-check iteration counts as one unit toward the budget even if
        // the SAT solver finds a model without consuming SAT conflicts.  Without this,
        // a formula whose theory keeps generating short unit-clause conflicts can loop
        // forever because BudgetExceeded (and its `spent` increment) is never reached.
        let mut theory_iters = 0u64;
        loop {
            let budget_ok = sat_conflicts < max_conflicts
                && theory_iters < max_conflicts.saturating_add(100);
            if !budget_ok {
                return NoResult::Unknown;
            }
            // Scope the sat borrow so we can call self.theory_check after.
            let sat_result = {
                let sat = self.sat.as_mut().unwrap();
                let remaining = max_conflicts.saturating_sub(sat_conflicts);
                let this_batch = batch.min(remaining.max(1));
                let r = sat.solve(&[], this_batch);
                match r {
                    SolveResult::Unsat => return NoResult::Unsat,
                    SolveResult::BudgetExceeded => {
                        sat_conflicts += this_batch;
                        None
                    }
                    SolveResult::Unknown => return NoResult::Unknown,
                    SolveResult::Sat(ref model) => Some(model.clone()),
                }
            };
            if let Some(model) = sat_result {
                theory_iters += 1;
                if let Some(conflict) = self.theory_check(&model) {
                    if conflict.is_empty() {
                        return NoResult::Unsat;
                    }
                    self.sat.as_mut().unwrap().add_clause(&conflict);
                } else {
                    return NoResult::Sat;
                }
            }
        }
    }
}

/// Returns `None` for unexpected non-Conflict EUF errors (caller should treat as Unknown).
fn mk_conflict_euf(e: rm_theory_euf::CcError) -> Option<Vec<Literal>> {
    match e {
        rm_theory_euf::CcError::Conflict { explanation, .. } => {
            // sat_lits are stored as raw literals; negate each to form the blocking clause.
            Some(
                explanation.sat_lits()
                    .iter()
                    .map(|&raw| Literal::from_raw(raw).negate())
                    .collect(),
            )
        }
        other => {
            // Non-Conflict errors are EUF implementation bugs, not input-triggered conflicts.
            // Returning an empty vec would be misread as "empty clause = UNSAT" — unsound.
            debug_assert!(false, "unexpected EUF error (not a Conflict): {other:?}");
            None
        }
    }
}

fn mk_conflict_dl(e: DlError) -> Vec<Literal> {
    let lits = match e {
        DlError::Conflict(core) => core.sat_lits,
        _ => vec![],
    };
    // sat_lits are stored as raw literals (with polarity); negate each to form the blocking clause.
    lits.iter()
        .map(|&raw| Literal::from_raw(raw).negate())
        .collect()
}

/// Lazy CDCL(T) path for formulas with disjunctions.
/// Returns the verdict and, on SAT, a DL model (var_name → integer value).
fn solve_with_cdclt(text: &str, max_conflicts: u64) -> Result<(NoResult, Vec<(String, i64)>), String> {
    use rm_syntax::{lex, parse_program};

    let tokens = lex(text).map_err(|e| e.to_string())?;
    let exprs = parse_program(&tokens).map_err(|e| e.to_string())?;
    let decls = parse_smtlib_decls(&exprs);

    let num_arith = decls.dl_vars.values().copied().max().unwrap_or(0);
    let mut cdclt = CdclT::new(num_arith);

    let mut uf_cache: FxHashMap<String, ENodeId> = FxHashMap::default();
    for (name, arity) in &decls.uf_funcs {
        if *arity == 0 {
            let id = cdclt.intern_const(name);
            uf_cache.insert(name.clone(), id);
        }
    }
    for (name, &dl_id) in &decls.dl_vars {
        let uid = if let Some(&id) = uf_cache.get(name) {
            id
        } else {
            let id = cdclt.intern_const(name);
            uf_cache.insert(name.clone(), id);
            id
        };
        cdclt.dl_var_names.insert(dl_id, name.clone());
        cdclt.dl_uf_pairs.push((dl_id, uid));
    }

    for assertion in &decls.assertions {
        let lit = encode_bool_cdclt(
            assertion,
            &mut cdclt,
            &mut uf_cache,
            &decls.uf_funcs,
            &decls.dl_vars,
        );
        match lit {
            Ok(l) => cdclt.add_clause(&[l]),
            Err(()) => return Ok((NoResult::Unknown, Vec::new())),
        }
    }

    let verdict = cdclt.solve(max_conflicts);
    let dl_model = if verdict == NoResult::Sat {
        let mut model: Vec<(String, i64)> = cdclt
            .dl_var_names
            .iter()
            .filter_map(|(&id, name)| cdclt.dl.var_upper_bound(id).map(|v| (name.clone(), v)))
            .collect();
        model.sort_by_key(|(n, _)| n.clone());
        model
    } else {
        Vec::new()
    };
    Ok((verdict, dl_model))
}

fn encode_bool_cdclt(
    expr: &rm_syntax::SExpr,
    cdclt: &mut CdclT,
    uf_cache: &mut FxHashMap<String, ENodeId>,
    uf_funcs: &FxHashMap<String, u32>,
    dl_vars: &FxHashMap<String, u32>,
) -> Result<Literal, ()> {
    use rm_syntax::{Atom, SExpr};

    match expr {
        SExpr::Atom(Atom::Symbol(s)) if s == "true" => {
            let v = cdclt.alloc_var();
            cdclt.add_clause(&[Literal::positive(v)]);
            Ok(Literal::positive(v))
        }
        SExpr::Atom(Atom::Symbol(s)) if s == "false" => {
            let v = cdclt.alloc_var();
            cdclt.add_clause(&[Literal::negative(v)]);
            Ok(Literal::negative(v))
        }
        SExpr::List(items) => {
            let op = items.first().and_then(|e| sexpr_symbol(e)).ok_or(())?;
            match op {
                "not" => {
                    let inner = items.get(1).ok_or(())?;
                    let l = encode_bool_cdclt(inner, cdclt, uf_cache, uf_funcs, dl_vars)?;
                    Ok(l.negate())
                }
                "and" => {
                    let subs: Vec<Literal> = items
                        .iter()
                        .skip(1)
                        .map(|s| encode_bool_cdclt(s, cdclt, uf_cache, uf_funcs, dl_vars))
                        .collect::<Result<_, _>>()?;
                    let v = cdclt.alloc_var();
                    let z = Literal::positive(v);
                    for &sl in &subs {
                        cdclt.add_clause(&[z.negate(), sl]);
                    }
                    let mut cl: Vec<Literal> = subs.iter().map(|l| l.negate()).collect();
                    cl.push(z);
                    cdclt.add_clause(&cl);
                    Ok(z)
                }
                "or" => {
                    let subs: Vec<Literal> = items
                        .iter()
                        .skip(1)
                        .map(|s| encode_bool_cdclt(s, cdclt, uf_cache, uf_funcs, dl_vars))
                        .collect::<Result<_, _>>()?;
                    let v = cdclt.alloc_var();
                    let z = Literal::positive(v);
                    let mut cl = vec![z.negate()];
                    cl.extend_from_slice(&subs);
                    cdclt.add_clause(&cl);
                    for &sl in &subs {
                        cdclt.add_clause(&[sl.negate(), z]);
                    }
                    Ok(z)
                }
                "=" => {
                    let lhs = items.get(1).ok_or(())?;
                    let rhs = items.get(2).ok_or(())?;
                    // If both sides are DL arithmetic vars, encode as two Leq atoms
                    // (Tseitin AND: v ↔ (x-y≤0 ∧ y-x≤0)) instead of routing to EUF.
                    if let (Some(xn), Some(yn)) = (sexpr_symbol(lhs), sexpr_symbol(rhs)) {
                        if let (Some(&xi), Some(&yi)) = (dl_vars.get(xn), dl_vars.get(yn)) {
                            let v1 = cdclt.alloc_var();
                            cdclt.atoms.insert(v1, BackboneAtom::Leq { x: xi, y: yi, c: 0 });
                            let v2 = cdclt.alloc_var();
                            cdclt.atoms.insert(v2, BackboneAtom::Leq { x: yi, y: xi, c: 0 });
                            let v = cdclt.alloc_var();
                            let lv = Literal::positive(v);
                            let lv1 = Literal::positive(v1);
                            let lv2 = Literal::positive(v2);
                            // v → v1, v → v2, (v1 ∧ v2) → v
                            cdclt.add_clause(&[lv.negate(), lv1]);
                            cdclt.add_clause(&[lv.negate(), lv2]);
                            cdclt.add_clause(&[lv, lv1.negate(), lv2.negate()]);
                            return Ok(lv);
                        }
                    }
                    let lid = intern_uf_term_cdclt(lhs, cdclt, uf_cache, uf_funcs)?;
                    let rid = intern_uf_term_cdclt(rhs, cdclt, uf_cache, uf_funcs)?;
                    let key = if lid <= rid { (lid, rid) } else { (rid, lid) };
                    let v = if let Some(&cached) = cdclt.eq_atom_cache.get(&key) {
                        cached
                    } else {
                        let v = cdclt.alloc_var();
                        cdclt.atoms.insert(v, BackboneAtom::Eq { lhs: lid, rhs: rid });
                        cdclt.eq_atom_cache.insert(key, v);
                        v
                    };
                    Ok(Literal::positive(v))
                }
                "<=" | "<" | ">=" | ">" => encode_arith_lit_cdclt(items, op, cdclt, dl_vars),
                // Bool-sorted function application used as a propositional atom.
                // We only admit it if the arity matches a declared UF function.
                fname => {
                    let args = &items[1..];
                    let arity = uf_funcs.get(fname).copied();
                    if arity == Some(args.len() as u32) || (arity.is_none() && args.is_empty()) {
                        // Stable key for this application.
                        let key = sexpr_key(expr);
                        let v = if let Some(&existing) = cdclt.bool_prop_atoms.get(&key) {
                            existing
                        } else {
                            let v = cdclt.alloc_var();
                            cdclt.bool_prop_atoms.insert(key, v);
                            v
                        };
                        Ok(Literal::positive(v))
                    } else {
                        Err(())
                    }
                }
            }
        }
        // A bare symbol that is a Bool constant (0-arity UF function).
        SExpr::Atom(Atom::Symbol(name)) if uf_funcs.get(name.as_str()) == Some(&0) => {
            let key = name.clone();
            let v = if let Some(&existing) = cdclt.bool_prop_atoms.get(&key) {
                existing
            } else {
                let v = cdclt.alloc_var();
                cdclt.bool_prop_atoms.insert(key, v);
                v
            };
            Ok(Literal::positive(v))
        }
        _ => Err(()),
    }
}

fn encode_arith_lit_cdclt(
    items: &[rm_syntax::SExpr],
    op: &str,
    cdclt: &mut CdclT,
    dl_vars: &FxHashMap<String, u32>,
) -> Result<Literal, ()> {
    let lhs = items.get(1).ok_or(())?;
    let rhs = items.get(2).ok_or(())?;

    let (x, y, c, is_lt) = if let Some((xn, yn)) = extract_diff(lhs) {
        let c = extract_int(rhs).ok_or(())?;
        let x = *dl_vars.get(xn).ok_or(())?;
        let y = *dl_vars.get(yn).ok_or(())?;
        match op {
            "<=" => (x, y, c, false),
            "<" => (x, y, c, true),
            ">=" => (y, x, -c, false),
            ">" => (y, x, -c, true),
            _ => return Err(()),
        }
    } else if let Some(xn) = sexpr_symbol(lhs) {
        if let Some(&x) = dl_vars.get(xn) {
            let c = extract_int(rhs).ok_or(())?;
            match op {
                "<=" => (x, 0, c, false),
                "<" => (x, 0, c, true),
                ">=" => (0, x, -c, false),
                ">" => (0, x, -c, true),
                _ => return Err(()),
            }
        } else {
            return Err(());
        }
    } else {
        return Err(());
    };

    let cache_key = (x, y, c, is_lt);
    let v = if let Some(&cached) = cdclt.arith_atom_cache.get(&cache_key) {
        cached
    } else {
        let v = cdclt.alloc_var();
        let atom = if is_lt {
            BackboneAtom::Lt { x, y, c }
        } else {
            BackboneAtom::Leq { x, y, c }
        };
        cdclt.atoms.insert(v, atom);
        cdclt.arith_atom_cache.insert(cache_key, v);
        v
    };
    Ok(Literal::positive(v))
}

fn intern_uf_term_cdclt(
    expr: &rm_syntax::SExpr,
    cdclt: &mut CdclT,
    uf_cache: &mut FxHashMap<String, ENodeId>,
    _uf_funcs: &FxHashMap<String, u32>,
) -> Result<ENodeId, ()> {
    use rm_syntax::{Atom, SExpr};
    let key = sexpr_key(expr);
    if let Some(&id) = uf_cache.get(&key) {
        return Ok(id);
    }
    match expr {
        SExpr::Atom(Atom::Symbol(name)) => {
            let id = cdclt.intern_const(name);
            uf_cache.insert(name.clone(), id);
            Ok(id)
        }
        SExpr::List(items) => {
            let fname = items.first().and_then(|e| sexpr_symbol(e)).ok_or(())?;
            let args: Vec<ENodeId> = items
                .iter()
                .skip(1)
                .map(|a| intern_uf_term_cdclt(a, cdclt, uf_cache, _uf_funcs))
                .collect::<Result<_, _>>()?;
            let id = cdclt.intern_apply(fname, &args);
            uf_cache.insert(key, id);
            Ok(id)
        }
        _ => Err(()),
    }
}

// ---------------------------------------------------------------------------
// Shared parsing helpers
// ---------------------------------------------------------------------------

fn intern_uf_term(
    expr: &rm_syntax::SExpr,
    solver: &mut NoCombinedSolver,
    uf_cache: &mut FxHashMap<String, ENodeId>,
    _uf_funcs: &FxHashMap<String, u32>,
) -> Result<ENodeId, ()> {
    use rm_syntax::{Atom, SExpr};
    let key = sexpr_key(expr);
    if let Some(&id) = uf_cache.get(&key) {
        return Ok(id);
    }
    match expr {
        SExpr::Atom(Atom::Symbol(name)) => {
            let id = solver.egraph.constant(name);
            let node = solver.egraph.node(id).clone();
            solver.cc.add_term(id, &node);
            uf_cache.insert(name.clone(), id);
            Ok(id)
        }
        SExpr::List(items) => {
            let fname = items.first().and_then(|e| sexpr_symbol(e)).ok_or(())?;
            let args: Vec<ENodeId> = items
                .iter()
                .skip(1)
                .map(|a| intern_uf_term(a, solver, uf_cache, _uf_funcs))
                .collect::<Result<_, _>>()?;
            let id = solver.egraph.apply(fname, &args);
            let node = solver.egraph.node(id).clone();
            solver.cc.add_term(id, &node);
            uf_cache.insert(key, id);
            Ok(id)
        }
        _ => Err(()),
    }
}

fn extract_diff(expr: &rm_syntax::SExpr) -> Option<(&str, &str)> {
    use rm_syntax::SExpr;
    let SExpr::List(items) = expr else {
        return None;
    };
    if items.len() != 3 || sexpr_symbol(&items[0]) != Some("-") {
        return None;
    }
    Some((sexpr_symbol(&items[1])?, sexpr_symbol(&items[2])?))
}

fn extract_int(expr: &rm_syntax::SExpr) -> Option<i64> {
    use rm_syntax::{Atom, SExpr};
    match expr {
        SExpr::Atom(Atom::Numeral(n)) => i64::try_from(*n).ok(),
        SExpr::Atom(Atom::Symbol(s)) => s.parse().ok(),
        SExpr::List(items) if items.len() == 2 && sexpr_symbol(&items[0]) == Some("-") => {
            if let SExpr::Atom(Atom::Numeral(n)) = &items[1] {
                i64::try_from(*n).ok().map(|v| -v)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn sexpr_symbol(expr: &rm_syntax::SExpr) -> Option<&str> {
    use rm_syntax::{Atom, SExpr};
    match expr {
        SExpr::Atom(Atom::Symbol(s)) => Some(s.as_str()),
        _ => None,
    }
}

fn sexpr_key(expr: &rm_syntax::SExpr) -> String {
    use rm_syntax::{Atom, SExpr};
    match expr {
        SExpr::Atom(Atom::Symbol(s)) => s.clone(),
        SExpr::Atom(Atom::Numeral(n)) => n.to_string(),
        SExpr::List(items) => format!(
            "({})",
            items.iter().map(sexpr_key).collect::<Vec<_>>().join(" ")
        ),
        _ => "_".into(),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn check(text: &str) -> NoResult {
        solve_qf_ufidl(text, u64::MAX).expect("parse error").0
    }

    // ---- Pure UF ----

    #[test]
    fn uf_sat_reflexivity() {
        let r = check(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (assert (= a a))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Sat);
    }

    #[test]
    fn uf_unsat_congruence() {
        let r = check(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (declare-fun f (U) U)
             (assert (= a b))
             (assert (not (= (f a) (f b))))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Unsat);
    }

    #[test]
    fn uf_sat_no_equalities() {
        let r = check(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (check-sat)",
        );
        assert_eq!(r, NoResult::Sat);
    }

    // ---- Pure DL ----

    #[test]
    fn dl_sat_simple() {
        let r = check(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (<= (- x y) 5))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Sat);
    }

    #[test]
    fn dl_unsat_negative_cycle() {
        let r = check(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (<= (- x y) 1))
             (assert (<= (- y x) -3))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Unsat);
    }

    #[test]
    fn dl_sat_upper_bound() {
        let r = check(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (assert (<= x 10))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Sat);
    }

    // ---- Combined QF_UFIDL (Nelson-Oppen) ----

    #[test]
    fn no_sat_independent() {
        let r = check(
            "(set-logic QF_UFIDL)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-const x Int)
             (declare-const y Int)
             (assert (= a a))
             (assert (<= (- x y) 5))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Sat);
    }

    #[test]
    fn no_unsat_dl_conflict() {
        let r = check(
            "(set-logic QF_UFIDL)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-const x Int)
             (declare-const y Int)
             (assert (= a a))
             (assert (<= (- x y) 0))
             (assert (<= (- y x) -1))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Unsat);
    }

    #[test]
    fn no_unsat_uf_conflict() {
        let r = check(
            "(set-logic QF_UFIDL)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (declare-fun f (U) U)
             (declare-const x Int)
             (assert (= a b))
             (assert (not (= (f a) (f b))))
             (assert (<= x 100))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Unsat);
    }

    #[test]
    fn no_cross_theory_unsat() {
        // DL derives x = y via tight bounds → EUF must derive f(x) = f(y)
        // but we assert f(x) ≠ f(y) → conflict
        let r = check(
            "(set-logic QF_UFIDL)
             (declare-sort U 0)
             (declare-const x Int)
             (declare-const y Int)
             (declare-fun f (Int) U)
             (assert (<= (- x y) 0))
             (assert (<= (- y x) 0))
             (assert (not (= (f x) (f y))))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Unsat);
    }

    #[test]
    fn no_cross_theory_sat() {
        // DL: x - y ≤ 5 (x and y may differ) → no equality derived
        // EUF: f(x) ≠ f(y) is consistent (x and y can be different)
        let r = check(
            "(set-logic QF_UFIDL)
             (declare-sort U 0)
             (declare-const x Int)
             (declare-const y Int)
             (declare-fun f (Int) U)
             (assert (<= (- x y) 5))
             (assert (not (= (f x) (f y))))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Sat);
    }

    #[test]
    fn no_empty_assertions() {
        let r = check(
            "(set-logic QF_UFIDL)
             (check-sat)",
        );
        assert_eq!(r, NoResult::Sat);
    }

    // ---- Disjunctive formulas (CDCL(T) backbone) ----

    #[test]
    fn cdclt_dl_diseq_sat() {
        // x ≠ y is satisfiable
        let r = check(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (not (= x y)))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Sat);
    }

    #[test]
    fn cdclt_dl_diseq_unsat() {
        // x = y AND x ≠ y → UNSAT
        let r = check(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (= x y))
             (assert (not (= x y)))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Unsat);
    }

    #[test]
    fn cdclt_disjunction_dl_sat() {
        // Either x ≤ 0 or y ≤ 0 — SAT
        let r = check(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (or (<= x 0) (<= y 0)))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Sat);
    }

    #[test]
    fn cdclt_uf_disjunction_sat() {
        // Either a = b or b = c — SAT
        let r = check(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (declare-fun c () U)
             (assert (or (= a b) (= b c)))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Sat);
    }

    #[test]
    fn cdclt_uf_disjunction_unsat() {
        // (a = b OR a = c) AND f(b) ≠ f(a) AND f(c) ≠ f(a) → UNSAT by congruence
        let r = check(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-fun a () U)
             (declare-fun b () U)
             (declare-fun c () U)
             (declare-fun f (U) U)
             (assert (or (= a b) (= a c)))
             (assert (not (= (f b) (f a))))
             (assert (not (= (f c) (f a))))
             (check-sat)",
        );
        assert_eq!(r, NoResult::Unsat);
    }

    #[test]
    fn cdclt_dl_model_has_values() {
        let (verdict, model) = solve_qf_ufidl(
            "(set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (<= (- x y) 3))
             (assert (not (= x y)))
             (check-sat)",
            u64::MAX,
        )
        .unwrap();
        assert_eq!(verdict, NoResult::Sat);
        assert!(!model.is_empty(), "model should contain x and y values");
    }
}
