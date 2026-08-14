use serde::{Deserialize, Serialize};
use std::fmt;

pub type Var = u32;

/// A propositional literal: a variable with a sign.
///
/// Encoding: `Literal(2*var)` is positive, `Literal(2*var + 1)` is negative.
/// This gives O(1) negation via XOR 1 and branchless var extraction via >> 1.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Literal(u32);

impl Literal {
    #[inline]
    pub fn new(var: Var, positive: bool) -> Self {
        Literal(var * 2 + (!positive) as u32)
    }

    #[inline]
    pub fn positive(var: Var) -> Self {
        Literal(var * 2)
    }

    #[inline]
    pub fn negative(var: Var) -> Self {
        Literal(var * 2 + 1)
    }

    #[inline]
    pub fn var(self) -> Var {
        self.0 >> 1
    }

    #[inline]
    pub fn is_positive(self) -> bool {
        self.0 & 1 == 0
    }

    #[inline]
    pub fn is_negative(self) -> bool {
        self.0 & 1 == 1
    }

    #[inline]
    pub fn negate(self) -> Self {
        Literal(self.0 ^ 1)
    }

    #[inline]
    pub fn raw(self) -> u32 {
        self.0
    }

    /// Construct directly from a raw encoded value. Use with care.
    #[inline]
    pub fn from_raw(raw: u32) -> Self {
        Literal(raw)
    }
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_positive() {
            write!(f, "x{}", self.var())
        } else {
            write!(f, "¬x{}", self.var())
        }
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        for var in 0..1000u32 {
            let pos = Literal::positive(var);
            let neg = Literal::negative(var);
            assert_eq!(pos.var(), var);
            assert_eq!(neg.var(), var);
            assert!(pos.is_positive());
            assert!(neg.is_negative());
            assert_eq!(pos.negate(), neg);
            assert_eq!(neg.negate(), pos);
        }
    }

    #[test]
    fn xor_negate() {
        let l = Literal::positive(42);
        assert_eq!(l.negate().negate(), l);
    }
}
