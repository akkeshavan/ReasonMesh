//! Cube-splitting coverage certificates (§8.4).
//!
//! When a partition node with cube `asmpts` is split into children
//! `asmpts ∪ {l_i}`, the split is sound only if the literals cover every
//! satisfying extension of `asmpts`:
//!
//! ```text
//! l_1 ∨ l_2 ∨ … ∨ l_k   is a tautology, or derivable from F ∧ asmpts
//! ```
//!
//! The simplest sound certificate is the syntactic tautology check: the
//! disjunction contains a variable in both polarities. This crate currently
//! verifies that form; it is the case-split used by cube-and-conquer.

use rm_akx::Literal;
use std::collections::HashSet;
use thiserror::Error;

/// Errors from certificate construction/verification.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum CoverageError {
    #[error("split literals do not cover the parent search region")]
    NotCovering,
    #[error("duplicate split literal")]
    DuplicateLiteral,
    #[error("empty split")]
    EmptySplit,
}

/// A certificate that a set of child cubes covers the parent region.
///
/// `literals` is the covering set `{l_1, …, l_k}`; children are
/// `asmpts ∪ {l_i}`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoverageCertificate {
    pub literals: Vec<Literal>,
}

impl CoverageCertificate {
    /// Construct a certificate from a covering literal set, verifying the
    /// syntactic tautology condition `l_1 ∨ … ∨ l_k`. Returns an error if the
    /// literals do not cover the space (no variable appears in both
    /// polarities, or duplicates/empty).
    pub fn tautology(literals: Vec<Literal>) -> Result<Self, CoverageError> {
        if literals.is_empty() {
            return Err(CoverageError::EmptySplit);
        }
        let mut seen: HashSet<Literal> = HashSet::default();
        for &l in &literals {
            if !seen.contains(&l) {
                seen.insert(l);
            } else {
                return Err(CoverageError::DuplicateLiteral);
            }
        }
        // Coverage: every variable appearing must appear in both polarities.
        let mut covered_vars: HashSet<u32> = HashSet::default();
        for &l in &literals {
            covered_vars.insert(l.var());
        }
        for v in &covered_vars {
            let has_pos = literals.iter().any(|&x| x.var() == *v && x.is_positive());
            let has_neg = literals.iter().any(|&x| x.var() == *v && x.is_negative());
            if !(has_pos && has_neg) {
                return Err(CoverageError::NotCovering);
            }
        }
        Ok(CoverageCertificate { literals })
    }

    /// Verify the certificate covers `asmpts`'s region. Currently the pure
    /// syntactic check (no theory involvement), so this just re-validates the
    /// certificate's internal coverage condition.
    pub fn verify(&self, _asmpts: &[Literal], literals: &[Literal]) -> Result<(), CoverageError> {
        if self.literals != literals {
            return Err(CoverageError::NotCovering);
        }
        // Re-run the covering check to guard against stale certificates.
        let _ = Self::tautology(literals.to_vec())?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn complementary_pair_covers() {
        let cert = CoverageCertificate::tautology(vec![Literal::positive(1), Literal::negative(1)])
            .unwrap();
        assert_eq!(cert.literals.len(), 2);
    }

    #[test]
    fn all_polarities_of_each_var() {
        let cert = CoverageCertificate::tautology(vec![
            Literal::positive(1),
            Literal::negative(1),
            Literal::positive(2),
            Literal::negative(2),
        ])
        .unwrap();
        assert_eq!(cert.literals.len(), 4);
    }

    #[test]
    fn single_polarity_does_not_cover() {
        assert!(matches!(
            CoverageCertificate::tautology(vec![Literal::positive(1)]),
            Err(CoverageError::NotCovering)
        ));
    }

    #[test]
    fn duplicate_literal_rejected() {
        assert!(matches!(
            CoverageCertificate::tautology(vec![
                Literal::positive(1),
                Literal::positive(1),
                Literal::negative(1),
            ]),
            Err(CoverageError::DuplicateLiteral)
        ));
    }

    #[test]
    fn empty_split_rejected() {
        assert!(matches!(
            CoverageCertificate::tautology(vec![]),
            Err(CoverageError::EmptySplit)
        ));
    }

    #[test]
    fn mismatched_certificate_rejected_on_verify() {
        let cert = CoverageCertificate::tautology(vec![Literal::positive(1), Literal::negative(1)])
            .unwrap();
        assert!(matches!(
            cert.verify(&[], &[Literal::positive(1)]),
            Err(CoverageError::NotCovering)
        ));
    }
}
