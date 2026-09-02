//! S-expression lexer and parser for SMT-LIB 2.7 input.

use std::fmt;

/// A single lexical token. Offsets are byte offsets into the source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    Lparen(usize),
    Rparen(usize),
    /// A quoted or plain symbol, e.g. `x`, `bvadd`, `=>`, `|hello world|`.
    Symbol(String, usize),
    /// A keyword, e.g. `:logic`, `:named`.
    Keyword(String, usize),
    /// A decimal numeral.
    Numeral(u128, usize),
    /// A `#x...` hex literal (kept as text so widths can be arbitrary).
    Hex(String, usize),
    /// A `#b...` binary literal (kept as text so widths can be arbitrary).
    Bin(String, usize),
    /// A double-quoted string literal.
    Str(String, usize),
}

impl Token {
    pub fn offset(&self) -> usize {
        match self {
            Token::Lparen(o)
            | Token::Rparen(o)
            | Token::Symbol(_, o)
            | Token::Keyword(_, o)
            | Token::Numeral(_, o)
            | Token::Hex(_, o)
            | Token::Bin(_, o)
            | Token::Str(_, o) => *o,
        }
    }

    pub fn describe(&self) -> String {
        match self {
            Token::Lparen(_) => "'('".into(),
            Token::Rparen(_) => "')'".into(),
            Token::Symbol(s, _) => format!("symbol {s:?}"),
            Token::Keyword(k, _) => format!("keyword {k:?}"),
            Token::Numeral(n, _) => format!("numeral {n}"),
            Token::Hex(h, _) => format!("hex #{h}"),
            Token::Bin(b, _) => format!("binary #{b}"),
            Token::Str(s, _) => format!("string {s:?}"),
        }
    }
}

/// Errors raised by the lexer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LexError {
    /// An unterminated string literal starting at this offset.
    UnterminatedString(usize),
    /// An unterminated quoted symbol starting at this offset.
    UnterminatedSymbol(usize),
    /// An unexpected/invalid character at this offset.
    UnexpectedChar(char, usize),
    /// A numeral overflowed our u128 storage.
    NumeralOverflow(usize),
    /// A `#x` or `#b` literal with no digits.
    EmptyRadix(usize),
    /// `#` not followed by `x` or `b`.
    BadRadix(usize),
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LexError::UnterminatedString(o) => write!(f, "unterminated string at offset {o}"),
            LexError::UnterminatedSymbol(o) => write!(f, "unterminated quoted symbol at offset {o}"),
            LexError::UnexpectedChar(c, o) => write!(f, "unexpected character {c:?} at offset {o}"),
            LexError::NumeralOverflow(o) => write!(f, "numeral overflow at offset {o}"),
            LexError::EmptyRadix(o) => write!(f, "empty #x/#b literal at offset {o}"),
            LexError::BadRadix(o) => write!(f, "'#' must be followed by 'x' or 'b' at offset {o}"),
        }
    }
}

impl std::error::Error for LexError {}

fn is_symbol_start(c: char) -> bool {
    c.is_ascii_alphabetic()
        || matches!(c, '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '-' | '+' | '=' | '<'
            | '>' | '.' | '?' | '/')
}

fn is_symbol_char(c: char) -> bool {
    is_symbol_start(c) || c.is_ascii_digit()
}

/// Tokenize a whole SMT-LIB source string.
pub fn lex(src: &str) -> Result<Vec<Token>, LexError> {
    let mut tokens = Vec::new();
    let mut chars = src.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        match c {
            ' ' | '\t' | '\r' | '\n' => {}
            ';' => {
                for (_, c2) in chars.by_ref() {
                    if c2 == '\n' {
                        break;
                    }
                }
            }
            '(' => tokens.push(Token::Lparen(i)),
            ')' => tokens.push(Token::Rparen(i)),
            '0'..='9' => {
                let mut n = (c as u128) - ('0' as u128);
                loop {
                    match chars.peek() {
                        Some((_, d)) if d.is_ascii_digit() => {
                            n = n
                                .checked_mul(10)
                                .and_then(|x| x.checked_add((*d as u128) - ('0' as u128)))
                                .ok_or(LexError::NumeralOverflow(i))?;
                            chars.next();
                        }
                        _ => break,
                    }
                }
                tokens.push(Token::Numeral(n, i));
            }
            '#' => {
                let radix = chars.next().ok_or(LexError::BadRadix(i))?;
                match radix.1 {
                    'x' => {
                        let mut s = String::new();
                        while let Some((_, d)) = chars.peek() {
                            if d.is_ascii_hexdigit() {
                                s.push(*d);
                                chars.next();
                            } else {
                                break;
                            }
                        }
                        if s.is_empty() {
                            return Err(LexError::EmptyRadix(i));
                        }
                        tokens.push(Token::Hex(s, i));
                    }
                    'b' => {
                        let mut s = String::new();
                        while let Some((_, d)) = chars.peek() {
                            if *d == '0' || *d == '1' {
                                s.push(*d);
                                chars.next();
                            } else {
                                break;
                            }
                        }
                        if s.is_empty() {
                            return Err(LexError::EmptyRadix(i));
                        }
                        tokens.push(Token::Bin(s, i));
                    }
                    _ => return Err(LexError::BadRadix(i)),
                }
            }
            ':' => {
                let mut s = String::new();
                while let Some((_, d)) = chars.peek() {
                    if is_symbol_char(*d) {
                        s.push(*d);
                        chars.next();
                    } else {
                        break;
                    }
                }
                tokens.push(Token::Keyword(s, i));
            }
            '|' => {
                let mut s = String::new();
                let mut closed = false;
                for (_, c2) in chars.by_ref() {
                    if c2 == '|' {
                        closed = true;
                        break;
                    }
                    s.push(c2);
                }
                if !closed {
                    return Err(LexError::UnterminatedSymbol(i));
                }
                tokens.push(Token::Symbol(s, i));
            }
            '"' => {
                let mut s = String::new();
                let mut closed = false;
                while let Some((_, c2)) = chars.next() {
                    if c2 == '"' {
                        if matches!(chars.peek(), Some((_, '"'))) {
                            s.push('"');
                            chars.next();
                            continue;
                        }
                        closed = true;
                        break;
                    }
                    s.push(c2);
                }
                if !closed {
                    return Err(LexError::UnterminatedString(i));
                }
                tokens.push(Token::Str(s, i));
            }
            c if is_symbol_start(c) => {
                let mut end = i + c.len_utf8();
                while let Some((j, d)) = chars.peek() {
                    if is_symbol_char(*d) {
                        end = j + d.len_utf8();
                        chars.next();
                    } else {
                        break;
                    }
                }
                tokens.push(Token::Symbol(src[i..end].to_string(), i));
            }
            other => return Err(LexError::UnexpectedChar(other, i)),
        }
    }
    Ok(tokens)
}

/// A nested S-expression as produced by the tokenizer-free recursive parser.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SExpr {
    Atom(Atom),
    List(Vec<SExpr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Atom {
    Symbol(String),
    Keyword(String),
    Numeral(u128),
    Hex(String),
    Bin(String),
    Str(String),
}

impl SExpr {
    pub fn symbol(&self) -> Option<&str> {
        match self {
            SExpr::Atom(Atom::Symbol(s)) => Some(s),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SExprError {
    pub offset: usize,
    pub message: String,
}

impl std::fmt::Display for SExprError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (at offset {})", self.message, self.offset)
    }
}

impl std::error::Error for SExprError {}

/// Parse a flat token stream into a single top-level s-expression. Returns
/// the expression, the tokens consumed (exactly one list-or-atom), and the
/// remaining tokens.
pub fn parse_expr(tokens: &[Token]) -> Result<(SExpr, usize), SExprError> {
    let mut idx = 0;
    let expr = parse_expr_from(tokens, &mut idx)?;
    Ok((expr, idx))
}

fn parse_expr_from(tokens: &[Token], idx: &mut usize) -> Result<SExpr, SExprError> {
    match tokens.get(*idx) {
        None => Err(SExprError {
            offset: 0,
            message: "unexpected end of input".into(),
        }),
        Some(Token::Rparen(o)) => Err(SExprError {
            offset: *o,
            message: "unexpected ')'".into(),
        }),
        Some(Token::Lparen(_)) => {
            let mut items = Vec::new();
            *idx += 1;
            loop {
                match tokens.get(*idx) {
                    None => return Err(SExprError { offset: 0, message: "unclosed '('".into() }),
                    Some(Token::Rparen(_)) => {
                        *idx += 1;
                        return Ok(SExpr::List(items));
                    }
                    _ => {
                        let item = parse_expr_from(tokens, idx)?;
                        items.push(item);
                    }
                }
            }
        }
        Some(tok) => {
            let atom = match tok {
                Token::Symbol(s, _) => Atom::Symbol(s.clone()),
                Token::Keyword(k, _) => Atom::Keyword(k.clone()),
                Token::Numeral(n, _) => Atom::Numeral(*n),
                Token::Hex(h, _) => Atom::Hex(h.clone()),
                Token::Bin(b, _) => Atom::Bin(b.clone()),
                Token::Str(s, _) => Atom::Str(s.clone()),
                _ => unreachable!(),
            };
            *idx += 1;
            Ok(SExpr::Atom(atom))
        }
    }
}

/// Parse a stream of top-level s-expressions until the input is exhausted or
/// a stop condition (function token) is reached.
pub fn parse_program(tokens: &[Token]) -> Result<Vec<SExpr>, SExprError> {
    let mut out = Vec::new();
    let mut idx = 0;
    while idx < tokens.len() {
        let (expr, consumed) = parse_expr(&tokens[idx..])?;
        out.push(expr);
        idx += consumed;
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lexer_basics() {
        let toks = lex("(assert (= x #b1010)) ; comment\n; more\n(exit)").unwrap();
        assert_eq!(toks[0], Token::Lparen(0));
        assert!(toks.contains(&Token::Symbol("assert".into(), 1)));
        assert!(toks.contains(&Token::Bin("1010".into(), 13)));
        assert!(toks.iter().any(|t| matches!(t, Token::Symbol(s, _) if s == "exit")));
    }

    #[test]
    fn lexer_hex() {
        let toks = lex("#xDeadBeef").unwrap();
        assert_eq!(toks, vec![Token::Hex("DeadBeef".into(), 0)]);
    }

    #[test]
    fn lexer_string_and_quote_escape() {
        let toks = lex("\"a\"\"b\" \"plain\"").unwrap();
        assert_eq!(toks[0], Token::Str("a\"b".into(), 0));
        assert_eq!(toks[1], Token::Str("plain".into(), 7));
    }

    #[test]
    fn lexer_quoted_symbol() {
        let toks = lex("|my var|").unwrap();
        assert_eq!(toks, vec![Token::Symbol("my var".into(), 0)]);
    }

    #[test]
    fn lexer_keyword_and_numeral() {
        let toks = lex(":named (assert 42)").unwrap();
        assert_eq!(toks[0], Token::Keyword("named".into(), 0));
        assert_eq!(toks[3], Token::Numeral(42, 15));
    }

    #[test]
    fn lexer_errors() {
        assert_eq!(lex("\"unclosed").unwrap_err(), LexError::UnterminatedString(0));
        assert_eq!(lex("|unclosed").unwrap_err(), LexError::UnterminatedSymbol(0));
        assert_eq!(lex("#z101").unwrap_err(), LexError::BadRadix(0));
        assert_eq!(lex("#x").unwrap_err(), LexError::EmptyRadix(0));
        assert!(matches!(lex("a{b"), Err(LexError::UnexpectedChar('{', 1))));
    }

    #[test]
    fn sexpr_parse_and_offsets() {
        let toks = lex("(f a (g b c))").unwrap();
        let (expr, consumed) = parse_expr(&toks).unwrap();
        assert_eq!(consumed, toks.len());
        match expr {
            SExpr::List(items) => {
                assert_eq!(items.len(), 3);
                assert_eq!(items[0].symbol(), Some("f"));
                assert!(matches!(items[2], SExpr::List(_)));
            }
            _ => panic!("expected list"),
        }
    }

    #[test]
    fn sexpr_unbalanced() {
        let toks = lex("(a").unwrap();
        assert!(parse_expr(&toks).is_err());
        let toks = lex(")").unwrap();
        assert!(parse_expr(&toks).is_err());
    }

    #[test]
    fn program_parses_multiple_commands() {
        let toks = lex("(set-logic QF_BV) (assert true) (check-sat)").unwrap();
        let exprs = parse_program(&toks).unwrap();
        assert_eq!(exprs.len(), 3);
    }
}