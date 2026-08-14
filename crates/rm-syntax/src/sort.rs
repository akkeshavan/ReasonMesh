use serde::{Deserialize, Serialize};

#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum Sort {
    Bool,
    BitVec(u32),
    Int,
    Real,
    Array { index: Box<Sort>, element: Box<Sort> },
    Uninterpreted(String),
}
