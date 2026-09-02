//! SMT-LIB 2.7 command and term parser (QF_BV fragment).

use super::ast::{BvOp, Term, TermInner};
use super::sort::SortExpr;
use super::s_expr::{Atom, SExpr};
use super::ParseError;

/// A parsed SMT-LIB command. Only the subset needed for QF_BV solving.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Command {
    SetLogic(String),
    /// `(declare-fun name (sorts...) sort)` — a constant or function symbol.
    DeclareFun { name: String, args: Vec<SortExpr>, result: SortExpr },
    /// `(assert term)`
    Assert(Term),
    /// `(check-sat)`
    CheckSat,
    /// `(exit)`
    Exit,
    /// `(get-model)` — accepted and ignored by the solver, kept for tooling.
    GetModel,
    /// Commands we tolerate but ignore (push/pop/set-option, etc.).
    Other(String),
}

/// A whole SMT-LIB script.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Script {
    pub commands: Vec<Command>,
    pub symbol_table: Symbols,
}

/// Symbol table of declared constants used to annotate terms with sorts.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Symbols {
    pub constants: std::collections::HashMap<String, SortExpr>,
}

impl Script {
    /// Parse a script. Declaration commands are collected first so that
    /// variable references in `assert` terms resolve to their declared sorts.
    pub fn parse(text: &str) -> Result<Script, ParseError> {
        let tokens = super::s_expr::lex(text).map_err(ParseError::Lex)?;
        let exprs = super::s_expr::parse_program(&tokens).map_err(ParseError::SExpr)?;
        let mut commands = Vec::new();
        for expr in &exprs {
            commands.push(parse_command_skeleton(expr)?);
        }
        // Build the constant symbol table from declarations.
        let mut constants: std::collections::HashMap<String, SortExpr> = std::collections::HashMap::new();
        for cmd in &commands {
            if let Command::DeclareFun { name, args, result } = cmd {
                if args.is_empty() {
                    constants.entry(name.clone()).or_insert(result.clone());
                }
            }
        }
        let symbols = Symbols { constants };
        // Re-parse command bodies now that sorts are known.
        let mut resolved = Vec::with_capacity(commands.len());
        for (expr, cmd) in exprs.iter().zip(&commands) {
            resolved.push(parse_command_body(expr, cmd, &symbols)?);
        }
        Ok(Script { commands: resolved, symbol_table: symbols })
    }

    /// All declared constant symbols and their sorts.
    pub fn symbols(&self) -> &Symbols {
        &self.symbol_table
    }

    /// The assertions in the script.
    pub fn assertions(&self) -> Vec<&Term> {
        self.commands
            .iter()
            .filter_map(|c| match c {
                Command::Assert(t) => Some(t),
                _ => None,
            })
            .collect()
    }
}

fn describe(expr: &SExpr) -> String {
    match expr {
        SExpr::Atom(a) => match a {
            Atom::Symbol(s) => format!("symbol {s:?}"),
            Atom::Keyword(k) => format!("keyword {k:?}"),
            Atom::Numeral(n) => format!("numeral {n}"),
            Atom::Hex(h) => format!("hex #{h}"),
            Atom::Bin(b) => format!("binary #{b}"),
            Atom::Str(s) => format!("string {s:?}"),
        },
        SExpr::List(_) => "a list".into(),
    }
}

fn unexpected(offset: usize, message: impl Into<String>) -> ParseError {
    ParseError::UnexpectedToken { offset, message: message.into() }
}

fn parse_command_skeleton(expr: &SExpr) -> Result<Command, ParseError> {
    let items = match expr {
        SExpr::List(items) => items,
        _ => return Err(unexpected(0, format!("expected a command, found {}", describe(expr)))),
    };
    if items.is_empty() {
        return Err(unexpected(0, "empty command ()"));
    }
    let name = match &items[0] {
        SExpr::Atom(Atom::Symbol(s)) => s.as_str(),
        _ => {
            return Err(unexpected(
                0,
                format!("command must begin with a symbol, found {}", describe(&items[0])),
            ))
        }
    };

    match name {
        "set-logic" => {
            require_len(items, 2, "set-logic")?;
            Ok(Command::SetLogic(expect_symbol(&items[1], "logic name")?))
        }
        "declare-fun" | "declare-const" | "define-fun" => {
            match name {
                "declare-const" => {
                    require_len(items, 3, "declare-const")?;
                    let name = expect_symbol(&items[1], "constant name")?;
                    let result = parse_sort(&items[2])?;
                    Ok(Command::DeclareFun { name, args: vec![], result })
                }
                "define-fun" => {
                    let name = expect_symbol(&items[1], "function name")?;
                    let args = parse_bound_sorts(&items[2])?;
                    let result = parse_sort(&items[3])?;
                    Ok(Command::DeclareFun { name, args, result })
                }
                _ => {
                    require_len(items, 4, "declare-fun")?;
                    let name = expect_symbol(&items[1], "function name")?;
                    let args = parse_sort_list(&items[2])?;
                    let result = parse_sort(&items[3])?;
                    Ok(Command::DeclareFun { name, args, result })
                }
            }
        }
        "assert" => {
            require_len(items, 2, "assert")?;
            // Skeleton pass leaves a placeholder; the body pass re-parses the
            // term once the constant symbol table is built.
            Ok(Command::Assert(bool_leaf()))
        }
        "check-sat" => Ok(Command::CheckSat),
        "exit" => Ok(Command::Exit),
        "get-model" => Ok(Command::GetModel),
        other => Ok(Command::Other(other.to_string())),
    }
}

/// Re-parse a command body now that the symbol table is known.
fn parse_command_body(expr: &SExpr, skeleton: &Command, symbols: &Symbols) -> Result<Command, ParseError> {
    match skeleton {
        Command::Assert(_) => {
            let items = match expr {
                SExpr::List(items) => items,
                _ => unreachable!(),
            };
            Ok(Command::Assert(parse_term(&items[1], symbols)?))
        }
        other => Ok(other.clone()),
    }
}

fn require_len(items: &[SExpr], expected: usize, cmd: &str) -> Result<(), ParseError> {
    if items.len() != expected {
        return Err(unexpected(
            0,
            format!("{cmd} expects {expected} arguments, got {} form", items.len()),
        ));
    }
    Ok(())
}

fn expect_symbol(expr: &SExpr, what: &str) -> Result<String, ParseError> {
    match expr {
        SExpr::Atom(Atom::Symbol(s)) => Ok(s.clone()),
        _ => Err(unexpected(0, format!("expected {what}, found {}", describe(expr)))),
    }
}

fn expect_numeral(expr: &SExpr, what: &str) -> Result<u64, ParseError> {
    match expr {
        SExpr::Atom(Atom::Numeral(n)) => {
            u64::try_from(*n).map_err(|_| unexpected(0, format!("{what} too large")))
        }
        _ => Err(unexpected(
            0,
            format!("expected {what} (a numeral), found {}", describe(expr)),
        )),
    }
}

fn parse_sort(expr: &SExpr) -> Result<SortExpr, ParseError> {
    SortExpr::parse(expr)
}

fn parse_sort_list(expr: &SExpr) -> Result<Vec<SortExpr>, ParseError> {
    let items = match expr {
        SExpr::List(items) => items,
        _ => return Err(unexpected(0, format!("expected a sort list, found {}", describe(expr)))),
    };
    items.iter().map(parse_sort).collect()
}

/// `(define-fun name ((x sort)...) sort body)`: parse the `(x sort)` args.
fn parse_bound_sorts(expr: &SExpr) -> Result<Vec<SortExpr>, ParseError> {
    let items = match expr {
        SExpr::List(items) => items,
        _ => return Err(unexpected(0, "expected a bound-var list")),
    };
    let mut sorts = Vec::new();
    for item in items {
        let pair = match item {
            SExpr::List(pair) if pair.len() == 2 => pair,
            _ => return Err(unexpected(0, "expected (symbol sort) binding")),
        };
        sorts.push(parse_sort(&pair[1])?);
    }
    Ok(sorts)
}

/// Parse `#b0101`, `#x0F`, and `(_ bvN M)` into a bit-vector literal.
fn parse_bv_literal(expr: &SExpr) -> Result<Option<Term>, ParseError> {
    match expr {
        SExpr::Atom(Atom::Bin(bits)) => {
            let width = bits.len() as u32;
            // In SMT-LIB the leftmost digit is the most significant bit.
            let bits: Vec<bool> = bits
                .chars()
                .rev()
                .map(|c| c == '1')
                .collect();
            Ok(Some(Term {
                sort: SortExpr::BitVec(width),
                inner: TermInner::BvLiteral { bits, width },
            }))
        }
        SExpr::Atom(Atom::Hex(hex)) => {
            let width = (hex.len() * 4) as u32;
            let mut bits = Vec::with_capacity(width as usize);
            for c in hex.chars().rev() {
                let d = c.to_digit(16).unwrap();
                for b in 0..4 {
                    bits.push(d & (1 << b) != 0);
                }
            }
            Ok(Some(Term {
                sort: SortExpr::BitVec(width),
                inner: TermInner::BvLiteral { bits, width },
            }))
        }
        SExpr::List(items)
            if items.len() == 3
                && items[0].symbol() == Some("_")
                && matches!(&items[1], SExpr::Atom(Atom::Symbol(s)) if s.starts_with("bv"))
                && items[1].symbol().unwrap().len() > 2 =>
        {
            let SExpr::Atom(Atom::Symbol(sym)) = &items[1] else { unreachable!() };
            let value: u128 = sym[2..]
                .parse()
                .map_err(|_| ParseError::UndefinedSymbol(sym.clone()))?;
            let width = expect_numeral(&items[2], "bit-vector width")? as u32;
            let mut bits = Vec::with_capacity(width as usize);
            let mut v = value;
            for _ in 0..width {
                bits.push(v & 1 == 1);
                v >>= 1;
            }
            Ok(Some(Term {
                sort: SortExpr::BitVec(width),
                inner: TermInner::BvLiteral { bits, width },
            }))
        }
        _ => Ok(None),
    }
}

/// Parse an indexed operator application `(_ extract i j args...)`.
fn parse_indexed(inner: &[SExpr], args: &[SExpr], symbols: &Symbols) -> Result<Term, ParseError> {
    let name = expect_symbol(&inner[1], "indexed operator name")?;
    match name.as_str() {
        "extract" => {
            if inner.len() != 4 || args.len() != 1 {
                return Err(unexpected(0, "extract takes (_ extract i j term)"));
            }
            let high = expect_numeral(&inner[2], "extract high")? as u32;
            let low = expect_numeral(&inner[3], "extract low")? as u32;
            let arg = parse_term(&args[0], symbols)?;
            unary_bv_expand(BvOp::Extract { high, low }, arg)
        }
        "zero_extend" | "sign_extend" => {
            if inner.len() != 3 || args.len() != 1 {
                return Err(unexpected(0, format!("{name} takes (_ {name} n term)")));
            }
            let amount = expect_numeral(&inner[2], "extend amount")? as u32;
            let arg = parse_term(&args[0], symbols)?;
            let op = if name == "zero_extend" {
                BvOp::ZeroExtend { amount }
            } else {
                BvOp::SignExtend { amount }
            };
            unary_bv_expand(op, arg)
        }
        other => Err(ParseError::UndefinedSymbol(format!("_ {other}"))),
    }
}

/// Result width for a unary BV op applied to an argument of width `w`.
fn unary_result_width(op: BvOp, w: u32) -> Option<u32> {
    match op {
        BvOp::Extract { high, low } => Some(high - low + 1),
        BvOp::ZeroExtend { amount } | BvOp::SignExtend { amount } => Some(w + amount),
        _ => Some(w),
    }
}

/// A unary BV operator keeps its operand width (except extract/extend).
fn unary_bv_expand(op: BvOp, arg: Term) -> Result<Term, ParseError> {
    match arg.sort {
        SortExpr::BitVec(w) => Ok(Term {
            sort: SortExpr::BitVec(unary_result_width(op, w).unwrap()),
            inner: TermInner::BvOp(op, vec![arg]),
        }),
        _ => Err(ParseError::SortMismatch {
            expected: "bit-vector".into(),
            got: format!("{}", arg.sort),
        }),
    }
}

fn is_bv_op(name: &str) -> bool {
    matches!(
        name,
        "bvnot" | "bvneg" | "bvadd" | "bvsub" | "bvmul" | "bvudiv" | "bvurem" | "bvsdiv"
            | "bvsrem" | "bvsmod" | "bvand" | "bvor" | "bvxor" | "bvshl" | "bvlshr" | "bvashr"
            | "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
            | "concat"
    )
}

fn bv_op_from(name: &str) -> BvOp {
    use BvOp::*;
    match name {
        "bvnot" => BvNot,
        "bvneg" => BvNeg,
        "bvadd" => BvAdd,
        "bvsub" => BvSub,
        "bvmul" => BvMul,
        "bvudiv" => BvUdiv,
        "bvurem" => BvUrem,
        "bvsdiv" => BvSdiv,
        "bvsrem" => BvSrem,
        "bvsmod" => BvSmod,
        "bvand" => BvAnd,
        "bvor" => BvOr,
        "bvxor" => BvXor,
        "bvshl" => BvShl,
        "bvlshr" => BvLshr,
        "bvashr" => BvAshr,
        "bvult" => BvUlt,
        "bvule" => BvUle,
        "bvugt" => BvUgt,
        "bvuge" => BvUge,
        "bvslt" => BvSlt,
        "bvsle" => BvSle,
        "bvsgt" => BvSgt,
        "bvsge" => BvSge,
        "concat" => Concat,
        _ => unreachable!(),
    }
}

fn bool_leaf() -> Term {
    Term { sort: SortExpr::Bool, inner: TermInner::True }
}

fn parse_term(expr: &SExpr, symbols: &Symbols) -> Result<Term, ParseError> {
    if let Some(lit) = parse_bv_literal(expr)? {
        return Ok(lit);
    }
    if let SExpr::Atom(Atom::Symbol(s)) = expr {
        return match s.as_str() {
            "true" => Ok(bool_leaf()),
            "false" => Ok(Term { sort: SortExpr::Bool, inner: TermInner::False }),
            name => {
                let sort = symbols
                    .constants
                    .get(name)
                    .cloned()
                    .unwrap_or(SortExpr::Bool);
                Ok(Term { sort, inner: TermInner::Variable(name.to_string()) })
            }
        };
    }

    let items = match expr {
        SExpr::List(items) => items,
        _ => unreachable!(),
    };
    if items.is_empty() {
        return Err(unexpected(0, "empty term ()"));
    }

    // Indexed application `(_ name ...)`.
    if matches!(&items[0], SExpr::List(inner) if inner.first().is_some_and(|e| e.symbol() == Some("_"))) {
        let SExpr::List(inner) = &items[0] else { unreachable!() };
        return parse_indexed(inner, &items[1..], symbols);
    }

    let head = match &items[0] {
        SExpr::Atom(Atom::Symbol(s)) => s.as_str(),
        _ => {
            return Err(unexpected(
                0,
                format!("expected operator, found {}", describe(&items[0])),
            ))
        }
    };

    if "not" == head {
        require_len(items, 2, "not")?;
        let inner = Box::new(parse_term(&items[1], symbols)?);
        return Ok(Term { sort: SortExpr::Bool, inner: TermInner::Not(inner) });
    }
    if "and" == head || "or" == head {
        let terms: Vec<Term> = items[1..].iter().map(|t| parse_term(t, symbols)).collect::<Result<_, _>>()?;
        let inner = if head == "and" { TermInner::And(terms) } else { TermInner::Or(terms) };
        return Ok(Term { sort: SortExpr::Bool, inner });
    }
    if "=>" == head {
        require_len(items, 3, "=>")?;
        // Implication desugars to (or (not a) b).
        let a = parse_term(&items[1], symbols)?;
        let b = parse_term(&items[2], symbols)?;
        let na = Term { sort: SortExpr::Bool, inner: TermInner::Not(Box::new(a)) };
        return Ok(Term {
            sort: SortExpr::Bool,
            inner: TermInner::Or(vec![na, b]),
        });
    }
    if "xor" == head {
        require_len(items, 3, "xor")?;
        // a xor b == (not (= a b)) at the Boolean level.
        let a = parse_term(&items[1], symbols)?;
        let b = parse_term(&items[2], symbols)?;
        let eq = Term { sort: SortExpr::Bool, inner: TermInner::Eq(Box::new(a), Box::new(b)) };
        return Ok(Term {
            sort: SortExpr::Bool,
            inner: TermInner::Not(Box::new(eq)),
        });
    }
    if "=" == head || "distinct" == head || "ite" == head {
        return parse_bool_core(head, &items[1..], symbols);
    }

    if is_bv_op(head) {
        return parse_bv_app(bv_op_from(head), &items[1..], symbols);
    }

    // User function call.
    let args: Vec<Term> = items[1..].iter().map(|t| parse_term(t, symbols)).collect::<Result<_, _>>()?;
    Ok(Term {
        sort: SortExpr::Bool,
        inner: TermInner::FunCall(head.to_string(), args),
    })
}

fn parse_bool_core(name: &str, args: &[SExpr], symbols: &Symbols) -> Result<Term, ParseError> {
    match name {
        "=" | "distinct" => {
            if args.len() < 2 {
                return Err(unexpected(0, format!("{name} needs at least 2 arguments")));
            }
            let terms: Vec<Term> = args.iter().map(|a| parse_term(a, symbols)).collect::<Result<_, _>>()?;
            let mut walker: Option<Term> = None;
            for t in terms {
                if let Some(acc) = walker {
                    let eq = Term {
                        sort: SortExpr::Bool,
                        inner: TermInner::Eq(Box::new(acc), Box::new(t)),
                    };
                    walker = Some(if name == "distinct" {
                        Term { sort: SortExpr::Bool, inner: TermInner::Not(Box::new(eq)) }
                    } else {
                        eq
                    });
                } else {
                    walker = Some(t);
                }
            }
            Ok(walker.unwrap())
        }
        "ite" => {
            if args.len() != 3 {
                return Err(unexpected(0, "ite takes 3 arguments"));
            }
            let c = parse_term(&args[0], symbols)?;
            let t = parse_term(&args[1], symbols)?;
            let e = parse_term(&args[2], symbols)?;
            let sort = t.sort.clone();
            Ok(Term { sort, inner: TermInner::Ite(Box::new(c), Box::new(t), Box::new(e)) })
        }
        _ => unreachable!(),
    }
}

/// Validate and build a plain BV op application. All operands share a width,
/// except `concat` (variadic) whose width is the sum.
fn parse_bv_app(op: BvOp, args: &[SExpr], symbols: &Symbols) -> Result<Term, ParseError> {
    if args.is_empty() {
        return Err(unexpected(0, format!("{} needs arguments", op.name())));
    }
    let terms: Vec<Term> = args.iter().map(|a| parse_term(a, symbols)).collect::<Result<_, _>>()?;
    let widths: Vec<Option<u32>> = terms.iter().map(|t| t.sort.as_bitvec()).collect();
    if widths.iter().any(|w| w.is_none()) {
        return Err(ParseError::SortMismatch {
            expected: "bits-vector operands".into(),
            got: "non-bit-vector operand".into(),
        });
    }
    let result_width = if op == BvOp::Concat {
        widths.iter().map(|w| w.unwrap()).sum()
    } else {
        let first = widths[0].unwrap();
        for (i, w) in widths.iter().enumerate() {
            if *w != Some(first) {
                return Err(ParseError::SortMismatch {
                    expected: format!("bit-vectors of equal width {first}"),
                    got: format!("argument {i} has width {}", widths[i].unwrap()),
                });
            }
        }
        first
    };
    Ok(Term {
        sort: if op.returns_bool() { SortExpr::Bool } else { SortExpr::BitVec(result_width) },
        inner: TermInner::BvOp(op, terms),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn script(s: &str) -> Script {
        Script::parse(s).unwrap()
    }

    #[test]
    fn parse_simple_script() {
        let s = script(
            "; comment\n(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert (= x #x05))\n(check-sat)\n(exit)\n",
        );
        assert_eq!(s.commands.len(), 5);
        match &s.commands[0] {
            Command::SetLogic(name) => assert_eq!(name, "QF_BV"),
            _ => panic!(),
        }
        match &s.commands[1] {
            Command::DeclareFun { name, args, result } => {
                assert_eq!(name, "x");
                assert!(args.is_empty());
                assert_eq!(*result, SortExpr::BitVec(8));
            }
            _ => panic!(),
        }
        assert!(matches!(s.commands[4], Command::Exit));
    }

    #[test]
    fn parse_bv_ops() {
        let s = script(
            "(set-logic QF_BV)\n\
             (declare-const a (_ BitVec 4))\n\
             (declare-const b (_ BitVec 4))\n\
             (assert (bvult (bvadd a b) #b1111))\n\
             (check-sat)\n",
        );
        assert!(matches!(s.commands[3], Command::Assert(_)));
    }

    #[test]
    fn ite_and_extract_sorts() {
        let s = script(
            "(declare-const a (_ BitVec 4))\n\
             (declare-const b (_ BitVec 4))\n\
             (declare-const c Bool)\n\
             (assert (= (ite c a b) ((_ zero_extend 4) (bvand a b))))\n",
        );
        // The ite result sort must be BitVec(4); extending gives BitVec(8).
        match &s.commands[3] {
            Command::Assert(t) => match &t.inner {
                TermInner::Eq(lhs, rhs) => {
                    assert_eq!(lhs.sort, SortExpr::BitVec(4));
                    assert!(matches!(rhs.inner, TermInner::BvOp(BvOp::ZeroExtend { amount: 4 }, _)));
                }
                _ => panic!(),
            },
            _ => panic!(),
        }
    }

    #[test]
    fn imply_rewrites_to_or() {
        // (assert (=> a b)) — desugars to (or (not a) b).
        let s = Script::parse("(assert (=> a b))").unwrap();
        let Command::Assert(t) = &s.commands[0] else { panic!() };
        match &t.inner {
            TermInner::Or(disjuncts) => {
                assert_eq!(disjuncts.len(), 2);
                assert!(matches!(disjuncts[0].inner, TermInner::Not(_)));
                assert!(matches!(&disjuncts[1].inner, TermInner::Variable(v) if v == "b"));
            }
            other => panic!("expected Or, got {:?}", other),
        }
    }

    #[test]
    fn bv_literal_forms() {
        let s = script("(assert (= #b1010 #xA))");
        match &s.commands[0] {
            Command::Assert(t) => match &t.inner {
                TermInner::Eq(l, r) => {
                    assert_eq!(l.sort, SortExpr::BitVec(4));
                    assert_eq!(r.sort, SortExpr::BitVec(4));
                }
                _ => panic!(),
            },
            _ => panic!(),
        }
    }

    #[test]
    fn parse_concat() {
        let s = script(
            "(declare-fun hi () (_ BitVec 4))\n\
             (declare-fun lo () (_ BitVec 4))\n\
             (assert (= (concat hi lo) #x00))\n",
        );
        match &s.commands[2] {
            Command::Assert(t) => match &t.inner {
                TermInner::Eq(lhs, _) => match &lhs.inner {
                    TermInner::BvOp(BvOp::Concat, args) => assert_eq!(args.len(), 2),
                    other => panic!("expected concat, got {:?}", other),
                },
                _ => panic!(),
            },
            _ => panic!(),
        }
    }

    #[test]
    fn rejects_bad_width_mix() {
        // 4-bit bvadd with an 8-bit operand is ill-sorted.
        assert!(Script::parse("(assert (= (bvadd #x1 #x00) #x00))").is_err());
    }

    #[test]
    fn exit_terminates() {
        let s = script("(exit)");
        assert_eq!(s.commands, vec![Command::Exit]);
    }
}