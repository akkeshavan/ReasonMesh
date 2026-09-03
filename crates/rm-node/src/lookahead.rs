//! Look-ahead heuristic for cube-and-conquer splitting.
//!
//! When the main solver exhausts its conflict budget (UNKNOWN), this module
//! chooses a variable to branch on and returns two SMT-LIB 2 `(assert ...)`
//! strings that together cover the full search space.
//!
//! ## Strategy
//!
//! 1. **Extract declarations** — parse `(declare-const name sort)` from the
//!    script using the SMT-LIB 2 lexer/parser.
//!
//! 2. **Score by occurrence** — count how often each variable name appears in
//!    assertion text; variables that participate in many constraints are the
//!    most central to the search.
//!
//! 3. **Probe** (when `probe_budget > 0`) — for each top-K candidate, run
//!    both branches with a small conflict budget:
//!    - UNSAT in ≤ `probe_budget` conflicts → score 100 (branch eliminated)
//!    - SAT                                 → score  10 (branch feasible)
//!    - UNKNOWN                             → score   5 (too hard to probe)
//!    The two branch scores are summed; the variable with the highest total
//!    wins.  An UNSAT probe + anything = 105+, which correctly dominates
//!    "unknown + unknown" = 10.
//!
//! 4. **Fallback** — if probing is disabled (`probe_budget = 0`) or all
//!    candidates tie, the most-frequently-occurring variable is chosen.
//!    If no variable can be found, `None` is returned and the worker reports
//!    UNKNOWN to the coordinator without a split.

use rm_syntax::{lex, parse_program, Atom, SExpr};

// ── Public API ────────────────────────────────────────────────────────────────

/// Given an SMT-LIB 2 script that returned UNKNOWN, choose a variable to split
/// on.  Returns `Some([pos_assertion, neg_assertion])` where the two strings
/// together cover the whole search space, or `None` if no suitable variable
/// is found.
///
/// `probe_budget` is the per-branch conflict budget for the look-ahead probe.
/// Pass `0` to skip probing and use the occurrence-frequency heuristic only.
pub fn pick_split(script: &str, probe_budget: u64) -> Option<[String; 2]> {
    let decls = parse_declarations(script);
    if decls.is_empty() {
        log::debug!("lookahead: no declarations found");
        return None;
    }

    // Score each variable by occurrence frequency.
    let mut scored: Vec<(Decl, usize)> = decls
        .into_iter()
        .map(|d| {
            let occ = count_occurrences(script, &d.name);
            (d, occ)
        })
        .collect();
    // Highest frequency first.
    scored.sort_by(|a, b| b.1.cmp(&a.1));
    scored.truncate(4); // probe at most 4 candidates

    if scored.is_empty() {
        return None;
    }

    if probe_budget == 0 {
        // Frequency-only heuristic: pick the most-occurring variable.
        let (best, _) = scored.remove(0);
        return Some(make_split_assertions(&best));
    }

    // Probe each candidate with both branches.
    let base = strip_check_sat(script);
    let mut best_var: Option<Decl>   = None;
    let mut best_score: i32          = -1;

    for (decl, _occ) in scored {
        let branches = make_split_assertions(&decl);
        let s0 = probe_branch(base, &branches[0], probe_budget);
        let s1 = probe_branch(base, &branches[1], probe_budget);
        let total = s0 + s1;
        log::debug!(
            "lookahead: {} → branch scores ({s0}, {s1}) = {total}",
            decl.name,
        );
        if total > best_score {
            best_score = total;
            best_var   = Some(decl);
        }
    }

    best_var.map(|d| make_split_assertions(&d))
}

// ── Declaration parsing ───────────────────────────────────────────────────────

#[derive(Clone, Debug)]
struct Decl {
    name: String,
    sort: VarSort,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum VarSort {
    Bool,
    BitVec(u32),
    Int,
}

/// Extract all `(declare-const name sort)` and nullary `(declare-fun name () sort)`
/// commands from a script.
fn parse_declarations(script: &str) -> Vec<Decl> {
    let tokens = match lex(script) {
        Ok(t)  => t,
        Err(e) => { log::debug!("lookahead lex: {e}"); return vec![]; }
    };
    let exprs = match parse_program(&tokens) {
        Ok(e)  => e,
        Err(e) => { log::debug!("lookahead parse: {e}"); return vec![]; }
    };

    let mut decls = Vec::new();
    for expr in exprs {
        let SExpr::List(ref items) = expr else { continue };
        match items.first().and_then(SExpr::symbol) {
            Some("declare-const") if items.len() == 3 => {
                if let (Some(name), Some(sort)) =
                    (items[1].symbol(), sort_of(&items[2]))
                {
                    decls.push(Decl { name: name.to_owned(), sort });
                }
            }
            Some("declare-fun") if items.len() == 4 => {
                // (declare-fun name () sort) — nullary only
                if let SExpr::List(args) = &items[2] {
                    if args.is_empty() {
                        if let (Some(name), Some(sort)) =
                            (items[1].symbol(), sort_of(&items[3]))
                        {
                            decls.push(Decl { name: name.to_owned(), sort });
                        }
                    }
                }
            }
            _ => {}
        }
    }
    decls
}

fn sort_of(expr: &SExpr) -> Option<VarSort> {
    match expr {
        SExpr::Atom(Atom::Symbol(s)) if s == "Bool" => Some(VarSort::Bool),
        SExpr::Atom(Atom::Symbol(s)) if s == "Int"  => Some(VarSort::Int),
        SExpr::List(items) if items.len() == 3
            && items[0].symbol() == Some("_")
            && items[1].symbol() == Some("BitVec") =>
        {
            if let SExpr::Atom(Atom::Numeral(n)) = &items[2] {
                Some(VarSort::BitVec(*n as u32))
            } else {
                None
            }
        }
        _ => None,
    }
}

// ── Occurrence counting ───────────────────────────────────────────────────────

/// Count the number of times `name` appears as a complete identifier token in
/// `text`.  Uses a simple byte-boundary check so "xy" does not match "xyz".
fn count_occurrences(text: &str, name: &str) -> usize {
    if name.is_empty() {
        return 0;
    }
    let bytes = text.as_bytes();
    let nbytes = name.as_bytes();
    let nlen = nbytes.len();
    let mut count = 0;
    let mut i = 0;
    while i + nlen <= bytes.len() {
        if bytes[i..i + nlen] == *nbytes {
            let before_ok = i == 0 || !is_ident_byte(bytes[i - 1]);
            let after_ok  = i + nlen == bytes.len() || !is_ident_byte(bytes[i + nlen]);
            if before_ok && after_ok {
                count += 1;
            }
        }
        i += 1;
    }
    count
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric()
        || matches!(b, b'_' | b'-' | b'.' | b'!' | b'@' | b'$' | b'%' | b'^'
                     | b'&' | b'*' | b'+' | b'=' | b'<' | b'>' | b'?' | b'/')
}

// ── Split assertion generation ────────────────────────────────────────────────

/// Build the two branch assertions for `decl`.
///
/// | Sort         | Branch 0 (lower half)                           | Branch 1 (upper half)                              |
/// |--------------|------------------------------------------------|----------------------------------------------------|
/// | Bool         | `(assert name)`                                | `(assert (not name))`                              |
/// | BitVec(w)    | `(assert (bvult name (_ bv{2^(w-1)} {w})))`  | `(assert (not (bvult name (_ bv{2^(w-1)} {w}))))` |
/// | Int          | `(assert (>= name 0))`                         | `(assert (< name 0))`                              |
fn make_split_assertions(decl: &Decl) -> [String; 2] {
    match decl.sort {
        VarSort::Bool => [
            format!("(assert {})", decl.name),
            format!("(assert (not {}))", decl.name),
        ],
        VarSort::BitVec(w) => {
            let mid = 1u128 << (w.saturating_sub(1));
            [
                format!("(assert (bvult {} (_ bv{mid} {w})))", decl.name),
                format!("(assert (not (bvult {} (_ bv{mid} {w}))))", decl.name),
            ]
        }
        VarSort::Int => [
            format!("(assert (>= {} 0))", decl.name),
            format!("(assert (< {} 0))", decl.name),
        ],
    }
}

// ── Probing ───────────────────────────────────────────────────────────────────

/// Run a single branch assertion against the base script with `budget` conflicts.
/// Returns a score: 100 = UNSAT (branch eliminated), 10 = SAT, 5 = UNKNOWN.
fn probe_branch(base_script: &str, assertion: &str, budget: u64) -> i32 {
    use rm_smt::SmtStatus;
    let script = format!("{base_script}\n{assertion}\n(check-sat)\n");
    match rm_smt::SmtSolver::parse(&script) {
        Err(_) => 5,
        Ok(s)  => match s.solve(budget) {
            Ok(r) => match r.status {
                SmtStatus::Unsat   => 100,
                SmtStatus::Sat     => 10,
                SmtStatus::Unknown => 5,
            },
            // EmptyProblem → trivially SAT
            Err(rm_smt::SmtError::EmptyProblem) => 10,
            Err(_) => 5,
        },
    }
}

/// Remove a trailing `(check-sat)` from a script string.
fn strip_check_sat(s: &str) -> &str {
    let t = s.trim_end();
    t.strip_suffix("(check-sat)").map(str::trim_end).unwrap_or(t)
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ── parse_declarations ────────────────────────────────────────────────────

    #[test]
    fn parse_bv_bool_int_decls() {
        let script =
            "(set-logic QF_BV)\n\
             (declare-const x (_ BitVec 8))\n\
             (declare-const flag Bool)\n\
             (declare-const n Int)\n\
             (declare-fun f () (_ BitVec 16))\n\
             (assert true)\n";
        let decls = parse_declarations(script);
        assert_eq!(decls.len(), 4);
        assert_eq!(decls[0].name, "x");
        assert_eq!(decls[0].sort, VarSort::BitVec(8));
        assert_eq!(decls[1].name, "flag");
        assert_eq!(decls[1].sort, VarSort::Bool);
        assert_eq!(decls[2].name, "n");
        assert_eq!(decls[2].sort, VarSort::Int);
        assert_eq!(decls[3].name, "f");
        assert_eq!(decls[3].sort, VarSort::BitVec(16));
    }

    #[test]
    fn parse_empty_script() {
        let decls = parse_declarations("(set-logic QF_BV) (check-sat)");
        assert!(decls.is_empty());
    }

    #[test]
    fn nullary_fun_parsed() {
        let decls = parse_declarations("(declare-fun g () Bool)");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].sort, VarSort::Bool);
    }

    #[test]
    fn non_nullary_fun_ignored() {
        // (declare-fun h (Int) Bool) — not nullary, should be skipped.
        let decls = parse_declarations("(declare-fun h (Int) Bool)");
        assert_eq!(decls.len(), 0);
    }

    // ── count_occurrences ─────────────────────────────────────────────────────

    #[test]
    fn occurrence_count_basic() {
        let s = "(assert (bvult x (_ bv5 8))) (assert (= x (_ bv3 8)))";
        assert_eq!(count_occurrences(s, "x"), 2);
    }

    #[test]
    fn occurrence_count_no_substring_match() {
        // "xy" must not match inside "xyz"
        let s = "(declare-const xyz Bool) (assert xyz)";
        assert_eq!(count_occurrences(s, "xy"), 0);
        assert_eq!(count_occurrences(s, "xyz"), 2);
    }

    // ── make_split_assertions ─────────────────────────────────────────────────

    #[test]
    fn split_bool() {
        let decl = Decl { name: "flag".into(), sort: VarSort::Bool };
        let [pos, neg] = make_split_assertions(&decl);
        assert_eq!(pos, "(assert flag)");
        assert_eq!(neg, "(assert (not flag))");
    }

    #[test]
    fn split_bitvec_8() {
        let decl = Decl { name: "x".into(), sort: VarSort::BitVec(8) };
        let [pos, neg] = make_split_assertions(&decl);
        assert_eq!(pos, "(assert (bvult x (_ bv128 8)))");
        assert_eq!(neg, "(assert (not (bvult x (_ bv128 8))))");
    }

    #[test]
    fn split_bitvec_1() {
        // Width-1: mid = 2^0 = 1, so split is x < 1 (i.e. x = 0b0) vs x >= 1 (i.e. x = 0b1).
        let decl = Decl { name: "b".into(), sort: VarSort::BitVec(1) };
        let [pos, neg] = make_split_assertions(&decl);
        assert_eq!(pos, "(assert (bvult b (_ bv1 1)))");
        assert_eq!(neg, "(assert (not (bvult b (_ bv1 1))))");
    }

    #[test]
    fn split_int() {
        let decl = Decl { name: "n".into(), sort: VarSort::Int };
        let [pos, neg] = make_split_assertions(&decl);
        assert_eq!(pos, "(assert (>= n 0))");
        assert_eq!(neg, "(assert (< n 0))");
    }

    // ── pick_split (no probing) ───────────────────────────────────────────────

    #[test]
    fn pick_split_frequency_heuristic() {
        // x appears 3 times, y appears once → x should be chosen.
        let script =
            "(set-logic QF_BV)\n\
             (declare-const x (_ BitVec 8))\n\
             (declare-const y (_ BitVec 8))\n\
             (assert (bvult x (_ bv100 8)))\n\
             (assert (bvugt x (_ bv50 8)))\n\
             (assert (= y (_ bv5 8)))\n\
             (check-sat)\n";
        let split = pick_split(script, 0).expect("should find a split");
        assert!(split[0].contains("x"), "expected x in pos branch, got {:?}", split[0]);
        assert!(split[1].contains("x"), "expected x in neg branch, got {:?}", split[1]);
    }

    #[test]
    fn pick_split_no_decls_returns_none() {
        let script = "(set-logic QF_BV) (assert true) (check-sat)";
        assert!(pick_split(script, 0).is_none());
    }

    // ── probe_branch ─────────────────────────────────────────────────────────

    #[test]
    fn probe_unsat_branch_scores_100() {
        // Adding (assert (bvult x #b0000)) to a script where x = #b0000
        // makes it UNSAT (can't have bvult 0 0).
        let base =
            "(set-logic QF_BV)\n\
             (declare-const x (_ BitVec 4))\n\
             (assert (= x #b0000))";
        let assertion = "(assert (bvult x #b0000))";
        let score = probe_branch(base, assertion, 10_000);
        assert_eq!(score, 100, "UNSAT branch should score 100");
    }

    #[test]
    fn probe_sat_branch_scores_10() {
        let base =
            "(set-logic QF_BV)\n\
             (declare-const x (_ BitVec 8))";
        let assertion = "(assert (bvult x (_ bv128 8)))";
        let score = probe_branch(base, assertion, 10_000);
        assert_eq!(score, 10, "SAT branch should score 10");
    }

    // ── pick_split with probing ───────────────────────────────────────────────

    #[test]
    fn pick_split_with_probing_returns_valid_split() {
        let script =
            "(set-logic QF_BV)\n\
             (declare-const x (_ BitVec 8))\n\
             (assert (bvult x (_ bv200 8)))\n\
             (check-sat)\n";
        let split = pick_split(script, 500).expect("should find a split");
        // The split assertions must partition the space.
        assert!(split[0].starts_with("(assert "));
        assert!(split[1].starts_with("(assert "));
        // Pos and neg should be complementary (neg wraps in (not ...)).
        assert!(split[1].contains("(not"), "neg branch should negate pos: {:?}", split[1]);
    }

    #[test]
    fn strip_check_sat_basic() {
        assert_eq!(strip_check_sat("(assert true)\n(check-sat)"), "(assert true)");
        assert_eq!(strip_check_sat("(check-sat)"), "");
        assert_eq!(strip_check_sat("(assert true)"), "(assert true)");
    }
}
