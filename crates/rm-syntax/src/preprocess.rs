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

/// Preprocess without size limit (for small/trusted inputs).
pub fn preprocess(expr: &SExpr) -> SExpr {
    let mut count = 0usize;
    preprocess_env(expr, &HashMap::new(), &mut count, usize::MAX)
        .expect("unbounded preprocess should not return None")
}

/// Preprocess with a node-count limit.  Returns `None` when let expansion
/// would exceed `max_nodes` cloned SExpr nodes — caller should treat the
/// problem as Unknown (too large to encode).
pub fn preprocess_bounded(expr: &SExpr, max_nodes: usize) -> Option<SExpr> {
    let mut count = 0usize;
    preprocess_env(expr, &HashMap::new(), &mut count, max_nodes)
}

fn node_count(expr: &SExpr) -> usize {
    match expr {
        SExpr::List(items) => 1 + items.iter().map(node_count).sum::<usize>(),
        _ => 1,
    }
}

fn preprocess_env(
    expr: &SExpr,
    env: &HashMap<String, SExpr>,
    count: &mut usize,
    limit: usize,
) -> Option<SExpr> {
    *count += 1;
    if *count > limit {
        return None;
    }
    match expr {
        SExpr::List(items) => {
            let head = items.first().and_then(|e| e.symbol());
            match head {
                Some("!") => {
                    if let Some(term) = items.get(1) {
                        preprocess_env(term, env, count, limit)
                    } else {
                        Some(expr.clone())
                    }
                }
                Some("let") => {
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
                                    let expanded = preprocess_env(val, env, count, limit)?;
                                    new_env.insert(name.clone(), expanded);
                                }
                            }
                        }
                        preprocess_env(body, &new_env, count, limit)
                    } else {
                        let children = items
                            .iter()
                            .map(|e| preprocess_env(e, env, count, limit))
                            .collect::<Option<Vec<_>>>()?;
                        Some(SExpr::List(children))
                    }
                }
                _ => {
                    let children = items
                        .iter()
                        .map(|e| preprocess_env(e, env, count, limit))
                        .collect::<Option<Vec<_>>>()?;
                    Some(SExpr::List(children))
                }
            }
        }
        SExpr::Atom(Atom::Symbol(name)) => {
            if let Some(val) = env.get(name.as_str()) {
                // Count the actual size of the cloned subtree, not just 1.
                // The original "+1 per reference" was wrong: a 10K-node let-value
                // referenced 10K times produces 100M nodes but only 10K increments,
                // completely bypassing the limit and causing multi-GB allocations.
                *count = count.saturating_add(node_count(val));
                if *count > limit {
                    return None;
                }
                Some(val.clone())
            } else {
                Some(expr.clone())
            }
        }
        _ => Some(expr.clone()),
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
