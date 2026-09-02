//! SMT-LIB 2.7 sort system: `Bool`, `(_ BitVec n)`, and user-declared
//! function sorts for QF_BV.

use serde::{Deserialize, Serialize};
use std::fmt;

/// An SMT-LIB sort expression.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SortExpr {
    Bool,
    /// `(_ BitVec n)` — an `n`-bit bit-vector sort.
    BitVec(u32),
}

impl SortExpr {
    /// Parse a sort from an s-expression, returning the parsed sort.
    pub fn parse(expr: &super::SExpr) -> Result<SortExpr, super::ParseError> {
        match expr {
            super::SExpr::Atom(super::Atom::Symbol(s)) if s == "Bool" => Ok(SortExpr::Bool),
            super::SExpr::List(items) if items.first().is_some_and(|i| i.symbol() == Some("_")) => {
                // (_ BitVec n)
                if items.get(1).is_some_and(|i| i.symbol() == Some("BitVec")) {
                    let n = match items.get(2) {
                        Some(super::SExpr::Atom(super::Atom::Numeral(n))) => {
                            u32::try_from(*n).map_err(|_| super::ParseError::SortWidth(*n))?
                        }
                        _ => {
                            return Err(super::ParseError::InvalidSort {
                                text: "(_ BitVec n) requires a numeral width".into(),
                            })
                        }
                    };
                    Ok(SortExpr::BitVec(n))
                } else {
                    Err(super::ParseError::InvalidSort {
                        text: "unknown indexed sort".into(),
                    })
                }
            }
            _ => Err(super::ParseError::InvalidSort {
                text: "expected Bool or (_ BitVec n)".into(),
            }),
        }
    }

    /// Returns the width of a bit-vector sort, if any.
    pub fn as_bitvec(&self) -> Option<u32> {
        match self {
            SortExpr::BitVec(n) => Some(*n),
            SortExpr::Bool => None,
        }
    }
}

impl fmt::Display for SortExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SortExpr::Bool => write!(f, "Bool"),
            SortExpr::BitVec(n) => write!(f, "(_ BitVec {n})"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse_expr, lex, Atom, SExpr};

    fn parse_sort(s: &str) -> Result<SortExpr, super::super::ParseError> {
        let toks = lex(s).unwrap();
        let (expr, _) = parse_expr(&toks).unwrap();
        SortExpr::parse(&expr)
    }

    #[test]
    fn parse_bool_and_bitvec() {
        assert_eq!(parse_sort("Bool").unwrap(), SortExpr::Bool);
        assert_eq!(parse_sort("(_ BitVec 8)").unwrap(), SortExpr::BitVec(8));
        assert_eq!(parse_sort("(_ BitVec 64)").unwrap(), SortExpr::BitVec(64));
    }

    #[test]
    fn reject_malformed() {
        assert!(parse_sort("(_ BitVec)").is_err());
        assert!(parse_sort("Int").is_err());
        assert!(parse_sort("(_ BitVec big)").is_err());
    }

    #[test]
    fn display_roundtrip() {
        assert_eq!(SortExpr::BitVec(16).to_string(), "(_ BitVec 16)");
        assert_eq!(SortExpr::Bool.to_string(), "Bool");
        let _ = SExpr::Atom(Atom::Numeral(1)); // keep import used
    }
}
