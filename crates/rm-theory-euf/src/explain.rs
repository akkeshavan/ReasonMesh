//! Equality explanation: reconstructs a minimal proof path between two
//! equal terms for conflict clause generation.
//!
//! The explanation algorithm walks the "union forest" storing the equality
//! assertions that drove each merge. For a conflict a≠b when a=b was derived,
//! it produces the set of input equalities that together imply a=b.

use crate::egraph::ENodeId;

/// A single literal in an explanation: the equality `lhs = rhs` that was
/// asserted (by the SAT solver or as a theory axiom).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExplanationLit {
    pub lhs: ENodeId,
    pub rhs: ENodeId,
    /// SAT literal index that asserted this equality, if any.
    pub sat_lit: Option<u32>,
}

impl ExplanationLit {
    pub fn eq(lhs: ENodeId, rhs: ENodeId, sat_lit: Option<u32>) -> Self {
        ExplanationLit { lhs, rhs, sat_lit }
    }
}

/// An explanation: the set of equalities that together imply `lhs = rhs`.
#[derive(Clone, Debug)]
pub struct Explanation {
    pub lhs: ENodeId,
    pub rhs: ENodeId,
    pub premises: Vec<ExplanationLit>,
}

impl Explanation {
    /// Extract the SAT literal indices involved in this explanation.
    /// These become the CDCL(T) conflict clause (negated).
    pub fn sat_lits(&self) -> Vec<u32> {
        self.premises
            .iter()
            .filter_map(|l| l.sat_lit)
            .collect()
    }
}
