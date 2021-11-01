pub mod token;

use std::{iter::from_fn, str::Chars};
use tig_common::{SmolStr, Span};
use token::{Token, TokenKind};
use crate::T;

pub fn tokenize(input: impl AsRef<str>) -> Vec<Token> {
    let mut chars = input.as_ref().chars();
    let mut offset = 0u32;

    let mut tokens = from_fn(|| {
        skip_whitespace(&mut chars, &mut offset);
        let start = offset;

        macro_rules! mt {
            ($chars:expr, $offset:expr, $res:expr, $(($mchar:expr, $mres:expr));+ $(;)?) => {
                match peek_nth(&$chars, 1) {
                    $($mchar => {
                        next_char(&mut $chars, &mut $offset);
                        $mres
                    }),+
                    _ => $res,
                }
            };
        }

        let kind = match peek_char(&chars) {
            '=' => T![=],
            ':' => mt!(chars, offset, T![:], ('=', T![:=])),
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
            '\0' if at_eof(&chars) => return None,
            c @ '_' => {
                if peek_nth(&chars, 1) == 'm'
                    && peek_nth(&chars, 2) == 'a'
                    && peek_nth(&chars, 3) == 'i'
                    && peek_nth(&chars, 4) == 'n'
                {
                    chars.next();
                    chars.next();
                    chars.next();
                    chars.next();
                    chars.next();
                    offset += 5;
                    TokenKind::Ident("_main".into())
                } else {
                    TokenKind::Unknown(c)
                }
            }
            c if c.is_ascii_digit() => TokenKind::Int(eat_int(&mut chars, &mut offset)),
            c if can_start_ident(c) => {
                let ident = eat_ident(&mut chars, &mut offset);
                match ident.as_str() {
                    "function" => T![function],
                    "nil" => T![nil],
                    "var" => T![var],
                    "type" => T![type],
                    _ => T![ident ident],
                }
            }
            c => TokenKind::Unknown(c),
        };

        if should_advance(&kind) {
            next_char(&mut chars, &mut offset);
        }

        let end = offset;
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
fn skip_whitespace(chars: &mut Chars, offset: &mut u32) {
    while peek_char(chars).is_whitespace() {
        next_char(chars, offset);
    }
}

/// Gets the next character from the input stream and increments offset.
fn next_char(chars: &mut Chars, offset: &mut u32) -> char {
    let c = chars.next().unwrap_or('\0');
    *offset += c.len_utf8() as u32;
    c
}

/// Peeks the first character in the input stream.
#[inline]
fn peek_nth(chars: &Chars, n: usize) -> char {
    chars.clone().nth(n).unwrap_or('\0')
}

/// Peeks the first character in the input stream.
#[inline]
fn peek_char(chars: &Chars) -> char {
    peek_nth(chars, 0)
}

/// There are no more characters in the input stream.
fn at_eof(chars: &Chars) -> bool {
    chars.clone().next().is_none()
}

fn eat_while<F: Fn(char) -> bool>(chars: &mut Chars, offset: &mut u32, test: F) -> SmolStr {
    let iter = chars.clone();
    let mut count = 0;

    while test(peek_char(chars)) {
        next_char(chars, offset);
        count += 1;
    }

    SmolStr::new(iter.take(count).collect::<String>())
}

/// Consume an identifier from the input stream.
///
/// # Assumptions
///  * The first character can start an identifier.
fn eat_ident(chars: &mut Chars, offset: &mut u32) -> SmolStr {
    eat_while(chars, offset, is_ident)
}

/// Consume an integer from the input stream.
///
/// # Assumptions
///  * The first character is an ascii digit.
fn eat_int(chars: &mut Chars, offset: &mut u32) -> SmolStr {
    eat_while(chars, offset, |c| c.is_ascii_digit())
}

/// Returns whether the lexer should consume the next character in the input stream, or it has
/// already been consumed.
fn should_advance(kind: &TokenKind) -> bool {
    use TokenKind::*;
    !(matches!(kind, Ident(_) | Int(_)) || kind.is_keyword())
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
            "(){}[]+-*/:",
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
                tok!(T![:], 10, 11),
                tok!(T![eof], 10, 11),
            ],
        );
    }

    #[test]
    fn test_multi_tokens() {
        check(":=", &[tok!(T![:=], 0, 2), tok!(T![eof], 1, 2)]);
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
    fn test_keywords() {
        check(
            "function nil _main var type",
            &[
                tok!(T![function], 0, 8),
                tok!(T![nil], 9, 12),
                tok!(T![ident "_main"], 13, 18),
                tok!(T![var], 19, 22),
                tok!(T![type], 23, 27),
                tok!(T![eof], 26, 27),
            ],
        );
    }
}
