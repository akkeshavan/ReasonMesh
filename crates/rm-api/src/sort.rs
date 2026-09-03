//! Sort (type) system for the programmatic API.

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sort {
    Bool,
    Int,
    BitVec(u32),
}

impl Sort {
    pub fn smtlib(&self) -> String {
        match self {
            Sort::Bool => "Bool".to_owned(),
            Sort::Int => "Int".to_owned(),
            Sort::BitVec(w) => format!("(_ BitVec {w})"),
        }
    }
}
