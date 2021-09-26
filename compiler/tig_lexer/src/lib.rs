pub mod token;

use smol_str::SmolStr;
use tig_common::Span;
pub use token::{Token, TokenKind};
use std::{iter::from_fn, str::Chars};

pub fn tokenize(input: impl AsRef<str>) -> Vec<Token> {
    let mut chars = input.as_ref().chars();
    let mut offset = 0u32;

    let mut tokens = from_fn(|| {
        skip_whitespace(&mut chars, &mut offset);
        let start = offset;

        let kind = match peek_char(&chars) {
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
            c if can_start_ident(c) => {
                let ident = eat_ident(&mut chars, &mut offset);
                match ident.as_str() {
                    "function" => T![function],
                    "_main" => T![_main],
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
    }).collect::<Vec<_>>();

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
/// `[\w_]`
fn can_start_ident(c: char) -> bool {
    c.is_alphabetic() || c == '_'
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
fn peek_char(chars: &Chars) -> char {
    chars.clone().next().unwrap_or('\0')
}

/// There are no more characters in the input stream.
fn at_eof(chars: &Chars) -> bool {
    chars.clone().next().is_none()
}

/// Consume an identifier from the input stream.
///
/// # Assumptions
///  * The first character can start an identifier.
fn eat_ident(chars: &mut Chars, offset: &mut u32) -> SmolStr {
    let iter = chars.clone();
    let mut count = 0;

    while is_ident(peek_char(&chars)) {
        next_char(chars, offset);
        count += 1;
    }

    SmolStr::new(iter.take(count).collect::<String>())
}

/// Returns whether the lexer should consume the next character in the input stream, or it has
/// already been consumed.
fn should_advance(kind: &TokenKind) -> bool {
    use TokenKind::*;
    !(matches!(kind, Ident(_)) || kind.is_keyword())
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! tok {
        ($kind:expr, $lo:expr, $hi:expr $(,)?) => {
            Token { span: Span::new($lo as u32, $hi as u32), kind: $kind }
        };
    }

    fn check(input: &str, expected: &[Token]) {
        let tokens = tokenize(input);
        assert_eq!(&tokens, expected);
    }

    #[test]
    fn test_single_tokens() {
        check(
            "(){}[]+-*/",
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
                tok!(T![eof], 9, 10),
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
    fn test_keywords() {
        check(
            "function _main",
            &[
                tok!(T![function], 0, 8),
                tok!(T![_main], 9, 14),
                tok!(T![eof], 13, 14),
            ],
        );
    }
}
