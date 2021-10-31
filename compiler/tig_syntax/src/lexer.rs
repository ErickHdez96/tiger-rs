use crate::T;
use std::fmt;
use std::iter::from_fn;
use std::str::Chars;
use tig_common::{SmolStr, Spanned};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token {
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    Dot,
    Comma,
    Colon,
    Semicolon,

    Plus,
    Minus,
    Star,
    Slash,

    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
    Ampersand,
    Pipe,
    Assign,

    Number(SmolStr),
    Ident(SmolStr),
    String(SmolStr),

    Array,
    If,
    Then,
    Else,
    While,
    For,
    To,
    Do,
    Let,
    In,
    End,
    Of,
    Break,
    Nil,
    Function,
    Var,
    Type,
    Import,
    Primitive,

    Unknown(char),
}

impl Token {
    pub fn is_keyword(&self) -> bool {
        use Token::*;
        matches!(
            self,
            Array
                | If
                | Then
                | Else
                | While
                | For
                | To
                | Do
                | Let
                | In
                | End
                | Of
                | Break
                | Nil
                | Function
                | Var
                | Type
                | Import
                | Primitive
        )
    }

    pub fn consumed_input(&self) -> bool {
        use Token::*;
        matches!(self, Number(_) | Ident(_) | String(_)) || self.is_keyword()
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::LParen => write!(f, "("),
            Self::RParen => write!(f, ")"),
            Self::LBrace => write!(f, "{{"),
            Self::RBrace => write!(f, "}}"),
            Self::LBracket => write!(f, "["),
            Self::RBracket => write!(f, "]"),
            Self::Dot => write!(f, "."),
            Self::Comma => write!(f, ","),
            Self::Semicolon => write!(f, ";"),
            Self::Colon => write!(f, ":"),
            Self::Plus => write!(f, "+"),
            Self::Minus => write!(f, "-"),
            Self::Star => write!(f, "*"),
            Self::Slash => write!(f, "/"),
            Self::Eq => write!(f, "="),
            Self::Neq => write!(f, "<>"),
            Self::Lt => write!(f, "<"),
            Self::Lte => write!(f, "<="),
            Self::Gt => write!(f, ">"),
            Self::Gte => write!(f, ">="),
            Self::Ampersand => write!(f, "&"),
            Self::Pipe => write!(f, "|"),
            Self::Assign => write!(f, ":="),
            Self::Number(i) | Self::Ident(i) => write!(f, "{}", i),
            Self::String(s) => write!(f, "{}", s),
            Self::Unknown(c) => write!(f, "{}", c),
            Self::Array => write!(f, "array"),
            Self::If => write!(f, "if"),
            Self::Then => write!(f, "then"),
            Self::Else => write!(f, "else"),
            Self::While => write!(f, "while"),
            Self::For => write!(f, "for"),
            Self::To => write!(f, "to"),
            Self::Do => write!(f, "do"),
            Self::Let => write!(f, "let"),
            Self::In => write!(f, "in"),
            Self::End => write!(f, "end"),
            Self::Of => write!(f, "of"),
            Self::Break => write!(f, "break"),
            Self::Nil => write!(f, "nil"),
            Self::Function => write!(f, "function"),
            Self::Var => write!(f, "var"),
            Self::Type => write!(f, "type"),
            Self::Import => write!(f, "import"),
            Self::Primitive => write!(f, "primitive"),
        }
    }
}

struct Lexer<'a> {
    chars: Chars<'a>,
    offset: usize,
}

pub fn tokenize(input: &str) -> Vec<Spanned<Token>> {
    let mut l = Lexer {
        chars: input.chars(),
        offset: 0,
    };
    let l = &mut l;

    from_fn(move || {
        skip_whitespace(l);

        // multi token
        macro_rules! mt {
            ($lexer:expr, $tk:expr, $(($c:expr, $t:expr)),+ $(,)?) => {
                match peek_nth($lexer, 1) {
                    $($c => {
                        next($lexer);
                        $t
                    }),+
                    _ => $tk,
                }
            };
        }

        let start = l.offset;
        let kind = match peek(l) {
            '(' => T!['('],
            ')' => T![')'],
            '{' => T!['{'],
            '}' => T!['}'],
            '[' => T!['['],
            ']' => T![']'],
            '.' => T![.],
            ',' => T![,],
            ':' => mt!(l, T![:], ('=', T![:=])),
            ';' => T![;],
            '+' => T![+],
            '-' => T![-],
            '*' => T![*],
            '/' => T![/],
            '=' => T![=],
            '<' => mt!(l, T![<], ('>', T![<>]), ('=', T![<=])),
            '>' => mt!(l, T![>], ('=', T![>=])),
            '&' => T![&],
            '|' => T![|],
            '\0' if at_eof(l) => return None,
            '"' => eat_string(l),
            c if c.is_ascii_digit() => eat_number(l),
            c if c.is_alphabetic() => eat_ident(l),
            c => Token::Unknown(c),
        };
        if !kind.consumed_input() {
            next(l);
        }
        let end = l.offset;

        Some((kind, start..end))
    })
    .into_iter()
    .collect::<Vec<_>>()
}

fn skip_whitespace(l: &mut Lexer) {
    while peek(l).is_whitespace() {
        next(l);
    }
}

fn at_eof(l: &Lexer) -> bool {
    l.chars.clone().next().is_none()
}

fn next(l: &mut Lexer) -> char {
    match l.chars.next() {
        Some(c) => {
            l.offset += c.len_utf8();
            c
        }
        None => '\0',
    }
}

fn peek_nth(l: &Lexer, n: usize) -> char {
    l.chars.clone().nth(n).unwrap_or('\0')
}

fn peek(l: &Lexer) -> char {
    peek_nth(l, 0)
}

fn eat_string(l: &mut Lexer) -> Token {
    let backup = l.chars.clone();
    next(l);
    let mut chars_consumed = 1;

    loop {
        match next(l) {
            '"' => {
                chars_consumed += 1;
                break;
            }
            '\0' => break,
            '\\' => {
                next(l);
                chars_consumed += 1;
            }
            _ => {}
        }
        chars_consumed += 1;
    }

    Token::String(backup.take(chars_consumed).collect::<String>().into())
}

fn eat_number(l: &mut Lexer) -> Token {
    let backup = l.chars.clone();
    let mut chars_consumed = 0;

    while peek(l).is_ascii_digit() {
        chars_consumed += 1;
        next(l);
    }

    Token::Number(backup.take(chars_consumed).collect::<String>().into())
}

fn eat_ident(l: &mut Lexer) -> Token {
    let is_ident = |c: char| c.is_alphanumeric() || c == '_';
    let backup = l.chars.clone();
    let mut chars_consumed = 0;

    while is_ident(peek(l)) {
        chars_consumed += 1;
        next(l);
    }

    let ident: SmolStr = backup.take(chars_consumed).collect::<String>().into();

    match ident.as_str() {
        "array" => Token::Array,
        "if" => Token::If,
        "then" => Token::Then,
        "else" => Token::Else,
        "while" => Token::While,
        "for" => Token::For,
        "to" => Token::To,
        "do" => Token::Do,
        "let" => Token::Let,
        "in" => Token::In,
        "end" => Token::End,
        "of" => Token::Of,
        "break" => Token::Break,
        "nil" => Token::Nil,
        "function" => Token::Function,
        "var" => Token::Var,
        "type" => Token::Type,
        "import" => Token::Import,
        "primitive" => Token::Primitive,
        _ => Token::Ident(ident),
    }
}

#[macro_export]
macro_rules! T {
    ('(' $(,)?) => {
        Token::LParen
    };
    (')' $(,)?) => {
        Token::RParen
    };
    ('{' $(,)?) => {
        Token::LBrace
    };
    ('}' $(,)?) => {
        Token::RBrace
    };
    ('[' $(,)?) => {
        Token::LBracket
    };
    (']' $(,)?) => {
        Token::RBracket
    };

    (. $(,)?) => {
        Token::Dot
    };
    (, $(,)?) => {
        Token::Comma
    };
    (; $(,)?) => {
        Token::Semicolon
    };
    (: $(,)?) => {
        Token::Colon
    };

    (+ $(,)?) => {
        Token::Plus
    };
    (- $(,)?) => {
        Token::Minus
    };
    (* $(,)?) => {
        Token::Star
    };
    (/ $(,)?) => {
        Token::Slash
    };

    (= $(,)?) => {
        Token::Eq
    };
    (<> $(,)?) => {
        Token::Neq
    };
    (< $(,)?) => {
        Token::Lt
    };
    (<= $(,)?) => {
        Token::Lte
    };
    (> $(,)?) => {
        Token::Gt
    };
    (>= $(,)?) => {
        Token::Gte
    };
    (& $(,)?) => {
        Token::Ampersand
    };
    (| $(,)?) => {
        Token::Pipe
    };
    (:= $(,)?) => {
        Token::Assign
    };

    (n, $number:expr $(,)?) => {
        Token::Number($number.into())
    };
    (ident, $ident:expr $(,)?) => {
        Token::Ident($ident.into())
    };
    (str, $str:expr $(,)?) => {
        Token::String($str.into())
    };

    (array $(,)?) => {
        Token::Array
    };
    (if $(,)?) => {
        Token::If
    };
    (then $(,)?) => {
        Token::Then
    };
    (else $(,)?) => {
        Token::Else
    };
    (while $(,)?) => {
        Token::While
    };
    (for $(,)?) => {
        Token::For
    };
    (to $(,)?) => {
        Token::To
    };
    (do $(,)?) => {
        Token::Do
    };
    (let $(,)?) => {
        Token::Let
    };
    (in $(,)?) => {
        Token::In
    };
    (end $(,)?) => {
        Token::End
    };
    (of $(,)?) => {
        Token::Of
    };
    (break $(,)?) => {
        Token::Break
    };
    (nil $(,)?) => {
        Token::Nil
    };
    (function $(,)?) => {
        Token::Function
    };
    (var $(,)?) => {
        Token::Var
    };
    (type $(,)?) => {
        Token::Type
    };
    (import $(,)?) => {
        Token::Import
    };
    (primitive $(,)?) => {
        Token::Primitive
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::T;

    fn check(input: &str, expected: &[Spanned<Token>]) {
        let tokens = tokenize(input);
        assert_eq!(tokens.len(), expected.len());
        for ((tt, ts), (et, es)) in tokens.iter().zip(expected.iter()) {
            assert_eq!(tt, et);
            assert_eq!(ts, es);
        }
    }

    #[test]
    fn lexes_symbols() {
        check(
            "(){}[].,:;+-*/=><&|",
            &[
                (T!['('], 0..1),
                (T![')'], 1..2),
                (T!['{'], 2..3),
                (T!['}'], 3..4),
                (T!['['], 4..5),
                (T![']'], 5..6),
                (T![.], 6..7),
                (T![,], 7..8),
                (T![:], 8..9),
                (T![;], 9..10),
                (T![+], 10..11),
                (T![-], 11..12),
                (T![*], 12..13),
                (T![/], 13..14),
                (T![=], 14..15),
                (T![>], 15..16),
                (T![<], 16..17),
                (T![&], 17..18),
                (T![|], 18..19),
            ],
        );
    }

    #[test]
    fn lexes_multisymbols() {
        check(
            "<> <= >= :=",
            &[
                (T![<>], 0..2),
                (T![<=], 3..5),
                (T![>=], 6..8),
                (T![:=], 9..11),
            ],
        );
    }

    #[test]
    fn lexes_numbers() {
        check("1 100", &[(T![n, "1"], 0..1), (T![n, "100"], 2..5)]);
    }

    #[test]
    fn lexes_strings() {
        check(
            r#""Hello, \"tiger\"!""#,
            &[(T![str, "\"Hello, \\\"tiger\\\"!\""], 0..19)],
        );
    }

    #[test]
    fn lexes_identifiers() {
        check(
            "hi a_number",
            &[(T![ident, "hi"], 0..2), (T![ident, "a_number"], 3..11)],
        );
    }

    #[test]
    fn lexes_keywords() {
        check(
            "array if then else while for to do let in end of break nil function var type import primitive",
            &[
                (T![array], 0..5),
                (T![if], 6..8),
                (T![then], 9..13),
                (T![else], 14..18),
                (T![while], 19..24),
                (T![for], 25..28),
                (T![to], 29..31),
                (T![do], 32..34),
                (T![let], 35..38),
                (T![in], 39..41),
                (T![end], 42..45),
                (T![of], 46..48),
                (T![break], 49..54),
                (T![nil], 55..58),
                (T![function], 59..67),
                (T![var], 68..71),
                (T![type], 72..76),
                (T![import], 77..83),
                (T![primitive], 84..93),
            ],
        );
    }
}
