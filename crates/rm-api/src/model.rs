//! Satisfying assignment returned by the solver when the result is SAT.

use std::collections::HashMap;

/// A variable assignment from a satisfying run.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Bool(bool),
    Int(i64),
    /// Bit-vector value with its declared width in bits.
    BitVec { bits: u64, width: u32 },
}

/// A satisfying model: maps each declared constant name to its assigned value.
#[derive(Clone, Debug, Default)]
pub struct Model {
    values: HashMap<String, Value>,
}

impl Model {
    pub(crate) fn from_raw(pairs: Vec<(String, String)>) -> Self {
        let mut values = HashMap::with_capacity(pairs.len());
        for (name, raw) in pairs {
            if let Some(v) = parse_value(&raw) {
                values.insert(name, v);
            }
        }
        Model { values }
    }

    pub fn get(&self, name: &str) -> Option<&Value> {
        self.values.get(name)
    }

    pub fn get_bool(&self, name: &str) -> Option<bool> {
        match self.values.get(name)? {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn get_int(&self, name: &str) -> Option<i64> {
        match self.values.get(name)? {
            Value::Int(n) => Some(*n),
            _ => None,
        }
    }

    pub fn get_bitvec(&self, name: &str) -> Option<(u64, u32)> {
        match self.values.get(name)? {
            Value::BitVec { bits, width } => Some((*bits, *width)),
            _ => None,
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&str, &Value)> {
        self.values.iter().map(|(k, v)| (k.as_str(), v))
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
}

/// Parse a raw SMT-LIB model value string into a typed [`Value`].
fn parse_value(raw: &str) -> Option<Value> {
    let s = raw.trim();
    if s == "true" { return Some(Value::Bool(true)); }
    if s == "false" { return Some(Value::Bool(false)); }

    // `(_ bv<n> <w>)` from QF_BV
    if let Some(rest) = s.strip_prefix("(_ bv") {
        let rest = rest.strip_suffix(')')?;
        let mut parts = rest.split_whitespace();
        let bits: u64 = parts.next()?.parse().ok()?;
        let width: u32 = parts.next()?.parse().ok()?;
        return Some(Value::BitVec { bits, width });
    }

    // `#b...` binary literal
    if let Some(rest) = s.strip_prefix("#b") {
        let bits = u64::from_str_radix(rest, 2).ok()?;
        let width = rest.len() as u32;
        return Some(Value::BitVec { bits, width });
    }

    // `#x...` hex literal
    if let Some(rest) = s.strip_prefix("#x") {
        let bits = u64::from_str_radix(rest, 16).ok()?;
        let width = rest.len() as u32 * 4;
        return Some(Value::BitVec { bits, width });
    }

    // Integer: plain decimal, possibly wrapped in `(- n)` for negatives
    if let Some(inner) = s.strip_prefix("(- ").and_then(|r| r.strip_suffix(')')) {
        let n: i64 = inner.trim().parse().ok()?;
        return Some(Value::Int(-n));
    }
    if let Ok(n) = s.parse::<i64>() {
        return Some(Value::Int(n));
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_bv_canonical() {
        assert_eq!(
            parse_value("(_ bv42 8)"),
            Some(Value::BitVec { bits: 42, width: 8 })
        );
    }

    #[test]
    fn parse_bv_binary() {
        assert_eq!(
            parse_value("#b1010"),
            Some(Value::BitVec { bits: 10, width: 4 })
        );
    }

    #[test]
    fn parse_bv_hex() {
        assert_eq!(
            parse_value("#xff"),
            Some(Value::BitVec { bits: 255, width: 8 })
        );
    }

    #[test]
    fn parse_int_positive() {
        assert_eq!(parse_value("7"), Some(Value::Int(7)));
    }

    #[test]
    fn parse_int_negative() {
        assert_eq!(parse_value("(- 3)"), Some(Value::Int(-3)));
    }

    #[test]
    fn parse_bool() {
        assert_eq!(parse_value("true"), Some(Value::Bool(true)));
        assert_eq!(parse_value("false"), Some(Value::Bool(false)));
    }
}
