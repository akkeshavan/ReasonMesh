/// Bounded Variable Elimination (BVE) preprocessing.
///
/// For each variable v, collect all clauses containing +v (pos_clauses) and
/// all clauses containing ¬v (neg_clauses).  If the number of non-tautological
/// resolvents does not exceed `pos + neg + BVE_GROWTH` we eliminate v:
///   - Delete the original pos and neg clauses.
///   - Add the resolvents in their place.
///   - Store the original pos_clauses so the model can be extended later.
///
/// After CDCL finds a satisfying assignment over the reduced formula, each
/// eliminated variable is assigned by scanning its stored pos_clauses:
/// if any pos_clause has no OTHER satisfied literal, v must be True; otherwise False.
///
/// Limits:
///   BVE_GROWTH    maximum net clause increase per variable (0 = no growth)
///   BVE_RESOLVENT_CAP  skip if pos×neg exceeds this (avoids O(n²) explosions)

use crate::clause::{ClauseArena, ClauseRef};
use rm_akx::literal::{Literal, Var};

// Allow at most 2 extra clauses per elimination (slight growth tolerated for
// better reduction on structured instances like Tseitin circuits).
const BVE_GROWTH: usize = 2;
// Skip variables where pos × neg would generate too many resolvents.
const BVE_RESOLVENT_CAP: usize = 20;

/// A single eliminated variable and the clause literals needed to extend the model.
pub struct ElimEntry {
    pub var: Var,
    /// All clauses that contained the POSITIVE literal (+v) before elimination.
    /// Used to reconstruct the value of `var` after CDCL finds a solution.
    pub pos_witnesses: Vec<Vec<Literal>>,
}

/// Run BVE on the arena; returns the list of eliminated variables (in order).
///
/// All resolvents are added to the arena (preserving correct occurrence lists for
/// chained eliminations).  The caller must additionally register new binary
/// clauses with the binary propagation table and propagate new unit clauses —
/// see `CdclSolver::run_bve` which does this by scanning the arena after this fn.
pub fn run(
    db: &mut ClauseArena,
    num_vars: u32,
    assigned_at_zero: impl Fn(Var) -> bool,
) -> Vec<ElimEntry> {
    // -----------------------------------------------------------------------
    // Build occurrence lists: literal raw index → list of ClauseRef
    // -----------------------------------------------------------------------
    let lit_cap = (num_vars * 2 + 2) as usize;
    let mut occs: Vec<Vec<ClauseRef>> = vec![Vec::new(); lit_cap];

    db.for_each_clause(1, |cr, _, _, lits| {
        for &l in lits {
            let raw = l.raw() as usize;
            if raw < lit_cap {
                occs[raw].push(cr);
            }
        }
    });

    // -----------------------------------------------------------------------
    // Try to eliminate each variable
    // -----------------------------------------------------------------------
    let mut eliminated: Vec<ElimEntry> = Vec::new();

    for var in 1..=num_vars {
        if assigned_at_zero(var) {
            continue; // Already decided at level 0; skip.
        }

        let pos_lit = Literal::positive(var);
        let neg_lit = Literal::negative(var);
        let pos_raw = pos_lit.raw() as usize;
        let neg_raw = neg_lit.raw() as usize;

        // Collect non-deleted positive and negative clause offsets.
        let pos: Vec<ClauseRef> = occs[pos_raw]
            .iter()
            .copied()
            .filter(|&cr| !db.is_deleted(cr))
            .collect();
        let neg: Vec<ClauseRef> = occs[neg_raw]
            .iter()
            .copied()
            .filter(|&cr| !db.is_deleted(cr))
            .collect();

        // Skip variables that appear in only one polarity.  Pure-literal
        // elimination would delete clauses permanently, which is unsound for
        // incremental solving (future add_clause calls may add the other
        // polarity).  CDCL naturally satisfies pure literals via polarity
        // selection, so we lose nothing meaningful by skipping them here.
        if pos.is_empty() || neg.is_empty() {
            continue;
        }

        // Bounded check: skip if resolvent count could be too large.
        if pos.len() * neg.len() > BVE_RESOLVENT_CAP {
            continue;
        }

        // Generate all non-tautological resolvents.
        let mut resolvents: Vec<Vec<Literal>> = Vec::new();
        let mut feasible = true;

        'outer: for &cp in &pos {
            for &cn in &neg {
                match resolve(db, cp, cn, var) {
                    Some(r) => resolvents.push(r),
                    None => {
                        // Tautological resolvent: skip this pair but continue.
                    }
                }
                if resolvents.len() > pos.len() + neg.len() + BVE_GROWTH {
                    feasible = false;
                    break 'outer;
                }
            }
        }

        if !feasible {
            continue;
        }

        // Elimination is profitable: commit.
        let witnesses = pos
            .iter()
            .map(|&cr| db.lits(cr).to_vec())
            .collect::<Vec<_>>();

        // Delete original clauses.
        for &cr in pos.iter().chain(neg.iter()) {
            db.mark_deleted(cr);
        }

        // Remove deleted entries from occs (keep the occurrence lists clean
        // so later variables see accurate counts).
        occs[pos_raw].retain(|cr| !db.is_deleted(*cr));
        occs[neg_raw].retain(|cr| !db.is_deleted(*cr));

        // Add all resolvents to the arena and register their occurrences.
        // The caller (run_bve) is responsible for:
        //   - scanning new arena entries of len=1 and propagating them at level 0
        //   - scanning new arena entries of len=2 and inserting them into the
        //     binary propagation table so BCP can see them
        for r in resolvents {
            let lbd = if r.is_empty() { 0 } else { (r.len() as u32).min(4) };
            let cr = db.add(&r, false, lbd);
            for &l in &r {
                let raw = l.raw() as usize;
                if raw < lit_cap {
                    occs[raw].push(cr);
                }
            }
        }

        eliminated.push(ElimEntry {
            var,
            pos_witnesses: witnesses,
        });
    }

    eliminated
}

/// Resolve clause `cp` (containing +v) with `cn` (containing ¬v).
/// Returns `None` if the resolvent is a tautology.
fn resolve(db: &ClauseArena, cp: ClauseRef, cn: ClauseRef, var: Var) -> Option<Vec<Literal>> {
    let pos_v = Literal::positive(var);
    let neg_v = Literal::negative(var);

    let lits_p = db.lits(cp);
    let lits_n = db.lits(cn);

    // Merge the two literal sets, excluding +v and ¬v.
    let mut result: Vec<Literal> = Vec::with_capacity(lits_p.len() + lits_n.len() - 2);

    for &l in lits_p {
        if l == pos_v {
            continue;
        }
        result.push(l);
    }
    for &l in lits_n {
        if l == neg_v {
            continue;
        }
        // Tautology check: if ¬l is already in result, resolvent is a tautology.
        if result.contains(&l.negate()) {
            return None;
        }
        // Duplicate check: skip if already present.
        if !result.contains(&l) {
            result.push(l);
        }
    }

    Some(result)
}

/// Extend a model (given as a mutable bool slice indexed by variable) with the
/// BVE-eliminated variables.  Must be called in REVERSE elimination order.
pub fn extend_model(values: &mut [bool], entries: &[ElimEntry]) {
    for entry in entries.iter().rev() {
        let v = entry.var as usize;
        // Set var = True if any pos_witness has no other satisfied literal.
        let must_true = entry.pos_witnesses.iter().any(|clause| {
            !clause.iter().any(|&l| {
                if l.var() == entry.var {
                    return false; // Ignore the eliminated literal itself.
                }
                let vv = l.var() as usize;
                if vv >= values.len() {
                    return false;
                }
                if l.is_positive() { values[vv] } else { !values[vv] }
            })
        });
        values[v] = must_true;
    }
}
