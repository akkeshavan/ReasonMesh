/// S-expression preprocessing: strip term annotations and expand let bindings.
///
/// Two passes are performed:
/// - `(! term :attr val ...)` → `term`   (SMT-LIB term attributes, e.g. :named)
/// - `(let ((x1 e1) ...) body)` → body with x_i substituted by e_i
///
/// These are applied recursively bottom-up so nested lets and annotations are
/// handled correctly.
use std::collections::HashMap;

use crate::{Atom, SExpr};

pub fn preprocess(expr: &SExpr) -> SExpr {
    preprocess_env(expr, &HashMap::new())
}

fn preprocess_env(expr: &SExpr, env: &HashMap<String, SExpr>) -> SExpr {
    match expr {
        SExpr::List(items) => {
            let head = items.first().and_then(|e| e.symbol());
            match head {
                Some("!") => {
                    // (! term :attr val ...) → term
                    if let Some(term) = items.get(1) {
                        preprocess_env(term, env)
                    } else {
                        expr.clone()
                    }
                }
                Some("let") => {
                    // (let ((x1 e1) (x2 e2) ...) body)
                    if let (Some(SExpr::List(bindings)), Some(body)) =
                        (items.get(1), items.get(2))
                    {
                        let mut new_env = env.clone();
                        for binding in bindings {
                            if let SExpr::List(bv) = binding {
                                if let (
                                    Some(SExpr::Atom(Atom::Symbol(name))),
                                    Some(val),
                                ) = (bv.first(), bv.get(1))
                                {
                                    let expanded = preprocess_env(val, env);
                                    new_env.insert(name.clone(), expanded);
                                }
                            }
                        }
                        preprocess_env(body, &new_env)
                    } else {
                        SExpr::List(items.iter().map(|e| preprocess_env(e, env)).collect())
                    }
                }
                _ => SExpr::List(items.iter().map(|e| preprocess_env(e, env)).collect()),
            }
        }
        SExpr::Atom(Atom::Symbol(name)) => {
            if let Some(val) = env.get(name.as_str()) {
                val.clone()
            } else {
                expr.clone()
            }
        }
        _ => expr.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{lex, parse_expr};

    fn parse(s: &str) -> SExpr {
        let toks = lex(s).unwrap();
        parse_expr(&toks).unwrap().0
    }

    #[test]
    fn strip_named_annotation() {
        let e = parse("(! (= a b) :named foo)");
        let r = preprocess(&e);
        assert_eq!(r, parse("(= a b)"));
    }

    #[test]
    fn expand_let_simple() {
        let e = parse("(let ((x a)) (= x b))");
        let r = preprocess(&e);
        assert_eq!(r, parse("(= a b)"));
    }

    #[test]
    fn expand_let_nested() {
        let e = parse("(let ((x (f a))) (let ((y (g x))) (= x y)))");
        let r = preprocess(&e);
        assert_eq!(r, parse("(= (f a) (g (f a)))"));
    }
}
