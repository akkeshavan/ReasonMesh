//! Bound representation for AKX `BoundKnowledge` production.

use serde::{Deserialize, Serialize};

/// The kind of arithmetic bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BoundKind {
    /// x - y ≤ c  (difference constraint)
    DiffLeq,
    /// x ≤ c      (upper bound on a single variable)
    UpperBound,
    /// x ≥ c      (lower bound on a single variable)
    LowerBound,
}

/// An arithmetic bound, ready for encoding as AKX `BoundKnowledge`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Bound {
    pub kind: BoundKind,
    /// Left-hand side variable index.
    pub lhs: u32,
    /// Right-hand side variable index (for `DiffLeq`).
    pub rhs: Option<u32>,
    /// The bound value, stored as rational p/q (q=1 for integers).
    pub numerator: i64,
    pub denominator: i64,
}

impl Bound {
    pub fn diff_leq(x: u32, y: u32, c: i64) -> Self {
        Bound {
            kind: BoundKind::DiffLeq,
            lhs: x,
            rhs: Some(y),
            numerator: c,
            denominator: 1,
        }
    }

    /// Encode as bytes for `BoundKnowledge.value_bytes`.
    pub fn to_bytes(&self) -> Vec<u8> {
        // Simple deterministic encoding: kind tag + fields as little-endian.
        let mut buf = Vec::with_capacity(24);
        buf.push(self.kind as u8);
        buf.extend_from_slice(&self.lhs.to_le_bytes());
        buf.extend_from_slice(&self.rhs.unwrap_or(0).to_le_bytes());
        buf.extend_from_slice(&self.numerator.to_le_bytes());
        buf.extend_from_slice(&self.denominator.to_le_bytes());
        buf
    }
}
