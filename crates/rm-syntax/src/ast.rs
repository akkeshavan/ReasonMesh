use serde::{Deserialize, Serialize};

/// An SMT-LIB symbol (interned string index).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct Symbol(pub u32);

/// A top-level SMT-LIB command.
#[derive(Clone, Debug)]
pub enum Command {
    SetLogic(String),
    DeclareConst { name: Symbol, sort: String },
    Assert(Term),
    CheckSat,
    GetModel,
    Exit,
}

/// A simplified term representation (to be expanded at M4).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Term {
    BoolLit(bool),
    Var(Symbol),
    App { head: Symbol, args: Vec<Term> },
}
