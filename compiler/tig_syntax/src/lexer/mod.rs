pub mod token;

use crate::T;
use std::{iter::from_fn, str::Chars};
use tig_common::{SmolStr, Span};
use token::{Token, TokenKind};

#[derive(Debug)]
struct Lexer<'a> {
    chars: Chars<'a>,
    offset: u32,
}

pub fn tokenize(input: impl AsRef<str>) -> Vec<Token> {
    let mut l = Lexer {
        chars: input.as_ref().chars(),
        offset: 0,
    };
    let l = &mut l;

    let mut tokens = from_fn(|| {
        skip_whitespace(l);
        let start = l.offset;

        macro_rules! mt {
            ($l:expr, $res:expr, $(($mchar:expr, $mres:expr)),+ $(,)?) => {
                match peek_nth(l, 1) {
                    $($mchar => {
                        next_char($l);
                        $mres
                    }),+
                    _ => $res,
                }
            };
        }

        let kind = match peek_char(l) {
            '=' => T![=],
            '<' => mt!(l, T![<], ('>', T![<>]), ('=', T![<=])),
            '>' => mt!(l, T![>], ('=', T![>=])),
            ':' => mt!(l, T![:], ('=', T![:=])),
            '(' => T!['('],
            ')' => T![')'],
            '{' => T!['{'],
            '}' => T!['}'],
            '[' => T!['['],
            ']' => T![']'],
            '+' => T![+],
            '-' => T![-],
            '*' => T![*],
            '/' => T![/],
            ',' => T![,],
            '.' => T![.],
            ';' => T![;],
            '&' => T![&],
            '|' => T![|],
            '"' => TokenKind::String(eat_string(l)),
            '\0' if at_eof(l) => return None,
            c @ '_' => {
                if peek_nth(l, 1) == 'm'
                    && peek_nth(l, 2) == 'a'
                    && peek_nth(l, 3) == 'i'
                    && peek_nth(l, 4) == 'n'
                {
                    l.chars.next();
                    l.chars.next();
                    l.chars.next();
                    l.chars.next();
                    l.chars.next();
                    l.offset += 5;
                    TokenKind::Ident("_main".into())
                } else {
                    TokenKind::Unknown(c)
                }
            }
            c if c.is_ascii_digit() => TokenKind::Int(eat_int(l)),
            c if can_start_ident(c) => {
                let ident = eat_ident(l);
                match ident.as_str() {
                    "array" => TokenKind::Array,
                    "if" => TokenKind::If,
                    "then" => TokenKind::Then,
                    "else" => TokenKind::Else,
                    "while" => TokenKind::While,
                    "for" => TokenKind::For,
                    "to" => TokenKind::To,
                    "do" => TokenKind::Do,
                    "let" => TokenKind::Let,
                    "in" => TokenKind::In,
                    "end" => TokenKind::End,
                    "of" => TokenKind::Of,
                    "break" => TokenKind::Break,
                    "nil" => TokenKind::Nil,
                    "function" => TokenKind::Function,
                    "var" => TokenKind::Var,
                    "type" => TokenKind::Type,
                    "import" => TokenKind::Import,
                    "primitive" => TokenKind::Primitive,
                    _ => TokenKind::Ident(ident),
                }
            }
            c => TokenKind::Unknown(c),
        };

        if should_advance(&kind) {
            next_char(l);
        }

        let end = l.offset;
        Some(Token {
            span: Span::new(start, end),
            kind,
        })
    })
    .collect::<Vec<_>>();

    let eof_span = tokens
        .iter()
        .last()
        .map(|t| Span::new(t.span.hi - 1, t.span.hi))
        .unwrap_or_else(|| Span::new(0, 1));
    tokens.push(Token {
        span: eof_span,
        kind: T![eof],
    });

    tokens
}

/// Checks if the character can start an identifier.
///
/// `[\w]`
fn can_start_ident(c: char) -> bool {
    c.is_alphabetic()
}

/// Checks if the character can be included in an identifier.
///
/// `[\w\d_]`
fn is_ident(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Advance the input stream
fn skip_whitespace(l: &mut Lexer) {
    while peek_char(l).is_whitespace() {
        next_char(l);
    }
}

/// Gets the next character from the input stream and increments offset.
fn next_char(l: &mut Lexer) -> char {
    let c = l.chars.next().unwrap_or('\0');
    l.offset += c.len_utf8() as u32;
    c
}

/// Peeks the first character in the input stream.
#[inline]
fn peek_nth(l: &Lexer, n: usize) -> char {
    l.chars.clone().nth(n).unwrap_or('\0')
}

/// Peeks the first character in the input stream.
#[inline]
fn peek_char(l: &Lexer) -> char {
    peek_nth(l, 0)
}

/// There are no more characters in the input stream.
fn at_eof(l: &Lexer) -> bool {
    l.chars.clone().next().is_none()
}

fn eat_while<F: Fn(char) -> bool>(l: &mut Lexer, test: F) -> SmolStr {
    let iter = l.chars.clone();
    let mut count = 0;

    while test(peek_char(l)) {
        next_char(l);
        count += 1;
    }

    SmolStr::new(iter.take(count).collect::<String>())
}

/// Consume an identifier from the input stream.
///
/// # Assumptions
///  * The first character can start an identifier.
fn eat_ident(l: &mut Lexer) -> SmolStr {
    eat_while(l, is_ident)
}

/// Consume an integer from the input stream.
///
/// # Assumptions
///  * The first character is an ascii digit.
fn eat_int(l: &mut Lexer) -> SmolStr {
    eat_while(l, |c| c.is_ascii_digit())
}

/// Consume a string from the input stream.
///
/// # Assumptions
///  * The first character is an ascii digit.
fn eat_string(l: &mut Lexer) -> SmolStr {
    let iter = l.chars.clone();
    next_char(l);
    let mut count = 1;

    loop {
        match peek_char(l) {
            '"' => {
                next_char(l);
                count += 1;
                break;
            }
            // TODO: Signal an error
            '\0' => break,
            '\\' => {
                // TODO: Handle EOF after \
                // TODO: Handle multicharacer escape sequences
                next_char(l);
                count += 1;
                break;
            }
            _ => {}
        }
        next_char(l);
        count += 1;
    }

    SmolStr::new(iter.take(count).collect::<String>())
}

/// Returns whether the lexer should consume the next character in the input stream, or it has
/// already been consumed.
fn should_advance(kind: &TokenKind) -> bool {
    use TokenKind::*;
    !(matches!(kind, Ident(_) | Int(_) | String(_)) || kind.is_keyword())
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! tok {
        ($kind:expr, $lo:expr, $hi:expr $(,)?) => {
            Token {
                span: Span::new($lo as u32, $hi as u32),
                kind: $kind,
            }
        };
    }

    fn check(input: &str, expected: &[Token]) {
        let tokens = tokenize(input);
        assert_eq!(&tokens, expected);
    }

    #[test]
    fn test_single_tokens() {
        check(
            "(){}[]+-*/,.:;=<&|>",
            &[
                tok!(T!['('], 0, 1),
                tok!(T![')'], 1, 2),
                tok!(T!['{'], 2, 3),
                tok!(T!['}'], 3, 4),
                tok!(T!['['], 4, 5),
                tok!(T![']'], 5, 6),
                tok!(T![+], 6, 7),
                tok!(T![-], 7, 8),
                tok!(T![*], 8, 9),
                tok!(T![/], 9, 10),
                tok!(T![,], 10, 11),
                tok!(T![.], 11, 12),
                tok!(T![:], 12, 13),
                tok!(T![;], 13, 14),
                tok!(T![=], 14, 15),
                tok!(T![<], 15, 16),
                tok!(T![&], 16, 17),
                tok!(T![|], 17, 18),
                tok!(T![>], 18, 19),
                tok!(T![eof], 18, 19),
            ],
        );
    }

    #[test]
    fn test_multi_tokens() {
        check(
            ":= <> <= >=",
            &[
                tok!(T![:=], 0, 2),
                tok!(T![<>], 3, 5),
                tok!(T![<=], 6, 8),
                tok!(T![>=], 9, 11),
                tok!(T![eof], 10, 11),
            ],
        );
    }

    #[test]
    fn test_identifiers() {
        check(
            "my_func a",
            &[
                tok!(T![ident "my_func"], 0, 7),
                tok!(T![ident "a"], 8, 9),
                tok!(T![eof], 8, 9),
            ],
        );
    }

    #[test]
    fn test_integers() {
        check(
            "0 100",
            &[
                tok!(T![int "0"], 0, 1),
                tok!(T![int "100"], 2, 5),
                tok!(T![eof], 4, 5),
            ],
        );
    }

    #[test]
    fn test_strings() {
        check(
            r#""Hello, world!""#,
            &[
                tok!(T![str "\"Hello, world!\""], 0, 15),
                tok!(T![eof], 14, 15),
            ],
        );
    }

    #[test]
    fn test_keywords() {
        check(
            "array if then else while for to do let in end of break nil function var type import primitive _main",
            &[
            tok!(T![array], 0, 5),
            tok!(T![if], 6, 8),
            tok!(T![then], 9, 13),
            tok!(T![else], 14, 18),
            tok!(T![while], 19, 24),
            tok!(T![for], 25, 28),
            tok!(T![to], 29, 31),
            tok!(T![do], 32, 34),
            tok!(T![let], 35, 38),
            tok!(T![in], 39, 41),
            tok!(T![end], 42, 45),
            tok!(T![of], 46, 48),
            tok!(T![break], 49, 54),
            tok!(T![nil], 55, 58),
            tok!(T![function], 59, 67),
            tok!(T![var], 68, 71),
            tok!(T![type], 72, 76),
            tok!(T![import], 77, 83),
            tok!(T![primitive], 84, 93),
            tok!(T![ident "_main"], 94, 99),
            tok!(T![eof], 98, 99),
            ],
        );
    }
}
