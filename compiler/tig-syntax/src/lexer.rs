use std::str::Chars;
use std::{fmt, iter};

use crate::T;
use tig_common::{SmolStr, SourceFile, Span};

/// The result of tokenizing an input string.
///
/// The tokens and possible error are public, that way the caller can report the error
/// and continue parsing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexerResult {
    pub tokens: Vec<Token>,
    pub unterminated_comment: Option<Span>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnterminatedCommentError(Span);

impl fmt::Display for UnterminatedCommentError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Unterminated comment: ({}, {})", self.0.lo, self.0.hi)
    }
}

impl std::error::Error for UnterminatedCommentError {}

impl LexerResult {
    /// Return the tokens if there was no error while lexing.
    pub fn tokens(self) -> Result<Vec<Token>, UnterminatedCommentError> {
        match self.unterminated_comment {
            None => Ok(self.tokens),
            Some(span) => Err(UnterminatedCommentError(span)),
        }
    }
}

/// Transform an input string into a list of `Token`s.
///
/// Integers and strings are not validatd, meaning that integers can be incredibly big,
/// and strings can be unterminated. The parser should validate them.
///
/// The only error is possibly an unterminated comment.
pub fn tokenize(input: &str) -> LexerResult {
    tokenize_with_offset(input, 0)
}

/// Same as `tokenize`.
pub fn tokenize_source_file(file: &SourceFile) -> LexerResult {
    assert!(file.offset() < (u32::MAX as usize));
    tokenize_with_offset(file.content(), file.offset() as u32)
}

/// Same as `tokenize`, but allows to start at an arbitrary offset, useful when compiling multiple
/// files.
pub fn tokenize_with_offset(input: &str, offset: u32) -> LexerResult {
    let lex = &mut Lexer {
        input: input.chars(),
        offset,
        unterminated_comment: None,
    };

    let mut tokens: Vec<Token> = iter::from_fn(|| {
        skip_trivia(lex);

        let start = lex.offset;
        // For easier lexing of identifiers, keywords, numbers, and strings.
        let checkpoint = lex.input.clone();
        let c = next(lex);

        // Multi token
        macro_rules! mt {
            ($lex:expr, $current_kind:expr, $(($next_token:expr; $kind:expr)),+ $(,)?) => {
                match peek($lex) {
                    $($next_token => { next($lex); $kind }),+
                    _ => $current_kind,
                }
            };
        }

        let kind = match c {
            ',' => T![,],
            ':' => mt!(lex, T![:], ('='; T![:=])),
            ';' => T![;],
            '.' => T![.],
            '+' => T![+],
            '-' => T![-],
            '*' => T![*],
            '/' => T![/],
            '=' => T![=],
            '<' => mt!(lex, T![<], ('>'; T![<>]), ('='; T![<=])),
            '>' => mt!(lex, T![>], ('='; T![>=])),
            '&' => T![&],
            '|' => T![|],
            '(' => T!['('],
            ')' => T![')'],
            '{' => T!['{'],
            '}' => T!['}'],
            '[' => T!['['],
            ']' => T![']'],
            '_' => {
                if peek_nth(lex, 0) == 'm'
                    && peek_nth(lex, 1) == 'a'
                    && peek_nth(lex, 2) == 'i'
                    && peek_nth(lex, 3) == 'n'
                {
                    next(lex);
                    next(lex);
                    next(lex);
                    next(lex);
                    TokenKind::Id("_main".into())
                } else {
                    TokenKind::Unknown(c)
                }
            }
            '"' => {
                let (value, terminated) = eat_string(lex, checkpoint);

                TokenKind::String { value, terminated }
            }
            c if ('0'..='9').contains(&c) => TokenKind::Integer(eat_integer(lex, checkpoint)),
            c if starts_ident(c) => {
                let ident = eat_identifier(lex, checkpoint);

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
                    "class" => TokenKind::Class,
                    "extends" => TokenKind::Extends,
                    "new" => TokenKind::New,
                    _ => T![id, ident],
                }
            }
            '\0' if at_eof(lex) => return None,
            c => TokenKind::Unknown(c),
        };

        let span = Span::new(start, lex.offset);
        Some(Token { span, kind })
    })
    .collect();

    let eof_span = tokens
        .iter()
        .last()
        .map(|t| Span::new(t.span.hi - 1, t.span.hi))
        .unwrap_or_else(|| Span::new(0, 1));
    tokens.push(Token {
        span: eof_span,
        kind: TokenKind::Eof,
    });

    LexerResult {
        tokens,
        unterminated_comment: lex.unterminated_comment,
    }
}

#[derive(Debug)]
struct Lexer<'a> {
    input: Chars<'a>,
    offset: u32,
    unterminated_comment: Option<Span>,
}

fn skip_trivia(l: &mut Lexer) {
    loop {
        match peek(l) {
            c if c.is_whitespace() => {
                next(l);
            }
            '/' if peek_nth(l, 1) == '*' => {
                eat_comment(l);
            }
            _ => break,
        }
    }
}

fn eat_comment(l: &mut Lexer) {
    let start = l.offset;
    next(l);
    next(l);

    loop {
        match peek(l) {
            '/' if peek_nth(l, 1) == '*' => {
                eat_comment(l);
            }
            '*' if peek_nth(l, 1) == '/' => {
                next(l);
                next(l);
                break;
            }
            '\0' => {
                if l.unterminated_comment.is_some() {
                    break;
                }
                // It doesn't matter if we stop lexing early, we have already reached the end
                // of the input, it will terminate on its own.
                l.unterminated_comment = Some(Span::new(start, l.offset));
                break;
            }
            _ => {
                next(l);
            }
        }
    }
}

fn eat_identifier(l: &mut Lexer, checkpoint: Chars) -> String {
    let mut length = 1;

    while is_ident(peek(l)) {
        next(l);
        length += 1;
    }

    checkpoint.take(length).collect()
}

fn eat_integer(l: &mut Lexer, checkpoint: Chars) -> SmolStr {
    let mut length = 1;

    while peek(l) >= '0' && peek(l) <= '9' {
        next(l);
        length += 1;
    }

    checkpoint.take(length).collect()
}

fn eat_string(l: &mut Lexer, checkpoint: Chars) -> (SmolStr, bool) {
    let mut length = 1;

    while peek(l) != '"' && peek(l) != '\0' {
        // Escape validation is done in the parser.
        if peek(l) == '\\' {
            next(l);
            length += 1;
        }

        next(l);
        length += 1;
    }

    let terminated = if peek(l) == '"' {
        next(l);
        length += 1;
        true
    } else {
        false
    };

    (checkpoint.take(length).collect(), terminated)
}

fn next(l: &mut Lexer) -> char {
    let c = l.input.next().unwrap_or('\0');
    l.offset = l
        .offset
        .checked_add(1)
        .expect("Source code larger than 4 GiB is not supported.");
    c
}

fn peek(l: &Lexer) -> char {
    l.input.clone().next().unwrap_or('\0')
}

fn peek_nth(l: &Lexer, n: usize) -> char {
    l.input.clone().nth(n).unwrap_or('\0')
}

fn at_eof(l: &Lexer) -> bool {
    l.input.clone().next().is_none()
}

fn starts_ident(c: char) -> bool {
    ('a'..='z').contains(&c) || ('A'..='Z').contains(&c)
}

fn is_ident(c: char) -> bool {
    ('a'..='z').contains(&c) || ('A'..='Z').contains(&c) || ('0'..='9').contains(&c) || c == '_'
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub span: Span,
    pub kind: TokenKind,
}

impl Token {
    pub fn dummy() -> Self {
        Token {
            span: Span::new(0, 0),
            kind: T![dummy],
        }
    }
}

impl Default for Token {
    fn default() -> Self {
        Self::dummy()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenKind {
    /// ,
    Comma,
    /// :
    Colon,
    /// ;
    Semicolon,
    /// .
    Period,
    /// +
    Plus,
    /// -
    Minus,
    /// *
    Star,
    /// /
    Slash,
    /// =
    Eq,
    /// <
    Lt,
    /// >
    Gt,
    /// &
    Amp,
    /// |
    Pipe,

    /// <>
    Neq,
    /// <=
    Lte,
    /// >=
    Gte,
    /// :=
    Assign,

    /// '('
    LParen,
    /// ')'
    RParen,
    /// '{'
    LBrace,
    /// '}'
    RBrace,
    /// '['
    LBracket,
    /// ']'
    RBracket,

    Id(SmolStr),

    Integer(SmolStr),

    String {
        value: SmolStr,
        terminated: bool,
    },

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
    Class,
    Extends,
    New,

    /// <eof>
    Eof,
    Dummy,
    Unknown(char),
}

impl TokenKind {
    pub fn to_kind_string(&self) -> String {
        match self {
            TokenKind::Id(_) => "identifier".to_string(),
            TokenKind::Integer(_) => "integer".to_string(),
            TokenKind::String { .. } => "string".to_string(),
            _ => self.to_string(),
        }
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TokenKind::Comma => ",",
                TokenKind::Colon => ":",
                TokenKind::Semicolon => ";",
                TokenKind::Period => ".",
                TokenKind::Plus => "+",
                TokenKind::Minus => "-",
                TokenKind::Star => "*",
                TokenKind::Slash => "/",
                TokenKind::Eq => "=",
                TokenKind::Lt => "<",
                TokenKind::Gt => ">",
                TokenKind::Amp => "&",
                TokenKind::Pipe => "|",
                TokenKind::Neq => "<>",
                TokenKind::Lte => "<=",
                TokenKind::Gte => ">=",
                TokenKind::Assign => ":=",
                TokenKind::LParen => "(",
                TokenKind::RParen => ")",
                TokenKind::LBrace => "{",
                TokenKind::RBrace => "}",
                TokenKind::LBracket => "[",
                TokenKind::RBracket => "]",
                TokenKind::Id(s) | TokenKind::Integer(s) | TokenKind::String { value: s, .. } =>
                    return write!(f, "{}", s),
                TokenKind::Array => "array",
                TokenKind::If => "if",
                TokenKind::Then => "then",
                TokenKind::Else => "else",
                TokenKind::While => "while",
                TokenKind::For => "for",
                TokenKind::To => "to",
                TokenKind::Do => "do",
                TokenKind::Let => "let",
                TokenKind::In => "in",
                TokenKind::End => "end",
                TokenKind::Of => "of",
                TokenKind::Break => "break",
                TokenKind::Nil => "nil",
                TokenKind::Function => "function",
                TokenKind::Var => "var",
                TokenKind::Type => "type",
                TokenKind::Import => "import",
                TokenKind::Primitive => "primitive",
                TokenKind::Class => "class",
                TokenKind::Extends => "extends",
                TokenKind::New => "new",
                TokenKind::Eof => "<eof>",
                TokenKind::Dummy => "<dummy>",
                TokenKind::Unknown(c) => return write!(f, "{}", c),
            }
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! tok {
        ($lo:expr, $hi:expr, $t:expr) => {
            Token {
                span: Span::new($lo, $hi),
                kind: $t,
            }
        };
    }

    #[test]
    fn test_single_tokens() {
        let input = ", : ; ( ) [ ] { } . + - * / = < > & |";
        let tokens = tokenize(input).tokens().unwrap();
        let expected = vec![
            tok!(0, 1, T![,]),
            tok!(2, 3, T![:]),
            tok!(4, 5, T![;]),
            tok!(6, 7, T!['(']),
            tok!(8, 9, T![')']),
            tok!(10, 11, T!['[']),
            tok!(12, 13, T![']']),
            tok!(14, 15, T!['{']),
            tok!(16, 17, T!['}']),
            tok!(18, 19, T![.]),
            tok!(20, 21, T![+]),
            tok!(22, 23, T![-]),
            tok!(24, 25, T![*]),
            tok!(26, 27, T![/]),
            tok!(28, 29, T![=]),
            tok!(30, 31, T![<]),
            tok!(32, 33, T![>]),
            tok!(34, 35, T![&]),
            tok!(36, 37, T![|]),
            tok!(36, 37, T![eof]),
        ];

        for (t, e) in tokens.iter().zip(expected.iter()) {
            assert_eq!(t, e);
        }
        assert_eq!(tokens.len(), expected.len());
    }

    #[test]
    fn test_multi_tokens() {
        let input = "<> <= >= :=";
        let tokens = tokenize(input).tokens().unwrap();
        let expected = vec![
            tok!(0, 2, T![<>]),
            tok!(3, 5, T![<=]),
            tok!(6, 8, T![>=]),
            tok!(9, 11, T![:=]),
            tok!(10, 11, T![eof]),
        ];

        for (t, e) in tokens.iter().zip(expected.iter()) {
            assert_eq!(t, e);
        }
        assert_eq!(tokens.len(), expected.len());
    }

    #[test]
    fn test_identifiers() {
        let input = "_main x factorial Try_123";
        let tokens = tokenize(input).tokens().unwrap();
        let expected = vec![
            tok!(0, 5, T![_main]),
            tok!(6, 7, T![id, "x"]),
            tok!(8, 17, T![id, "factorial"]),
            tok!(18, 25, T![id, "Try_123"]),
            tok!(24, 25, T![eof]),
        ];

        for (t, e) in tokens.iter().zip(expected.iter()) {
            assert_eq!(t, e);
        }
        assert_eq!(tokens.len(), expected.len());
    }

    #[test]
    fn test_integers() {
        let input = "0 1234 01";
        let tokens = tokenize(input).tokens().unwrap();
        let expected = vec![
            tok!(0, 1, T![int, "0"]),
            tok!(2, 6, T![int, "1234"]),
            tok!(7, 9, T![int, "01"]),
            tok!(8, 9, T![eof]),
        ];

        for (t, e) in tokens.iter().zip(expected.iter()) {
            assert_eq!(t, e);
        }
        assert_eq!(tokens.len(), expected.len());
    }

    #[test]
    fn test_strings() {
        let input = "\
        \"Hello, World!\" \
        \"\\n\" \
        ";
        let tokens = tokenize(input).tokens().unwrap();
        let expected = vec![
            tok!(0, 15, T![str, r#""Hello, World!""#]),
            tok!(16, 20, T![str, r#""\n""#]),
            tok!(19, 20, T![eof]),
        ];

        for (t, e) in tokens.iter().zip(expected.iter()) {
            assert_eq!(t, e);
        }
        assert_eq!(tokens.len(), expected.len());
    }

    #[test]
    fn test_comments() {
        let input = "/* Comment 1 /* 2 */ 1 */";
        let tokens = tokenize(input).tokens().unwrap();
        let expected = vec![tok!(0, 1, T![eof])];

        assert_eq!(tokens.len(), expected.len());
    }

    #[test]
    fn test_unterminated_comments() {
        let input = "/* Comment 1 /* 2 / 1 */";
        let error = tokenize(input)
            .tokens()
            .expect_err("Should have returned an error");
        assert_eq!(error.0, Span::new(0, 24));

        let input = "/* Comment 1 /* 2 / 1 *";
        let error = tokenize(input)
            .tokens()
            .expect_err("Should have returned an error");
        assert_eq!(error.0, Span::new(13, 23));
    }

    #[test]
    fn test_keywords() {
        let input = "array if then else";
        let tokens = tokenize(input).tokens().unwrap();
        let expected = vec![
            tok!(0, 5, T![array]),
            tok!(6, 8, T![if]),
            tok!(9, 13, T![then]),
            tok!(14, 18, T![else]),
            tok!(17, 18, T![eof]),
        ];

        for (t, e) in tokens.iter().zip(expected.iter()) {
            assert_eq!(t, e);
        }
        assert_eq!(tokens.len(), expected.len());
    }
}

#[macro_export]
macro_rules! T {
    (eof) => {
        TokenKind::Eof
    };
    (dummy) => {
        TokenKind::Dummy
    };
    (_main) => {
        TokenKind::Id("_main".into())
    };
    (id, $id:expr) => {
        TokenKind::Id($id.into())
    };
    (int, $int:expr) => {
        TokenKind::Integer($int.into())
    };
    (str, $str:expr) => {
        TokenKind::String {
            value: $str.into(),
            terminated: true,
        }
    };
    (raw_str, $str:expr, $terminated:expr) => {
        TokenKind::String {
            value: $str.into(),
            terminated: $terminated,
        }
    };
    (array) => {
        TokenKind::Array
    };
    (if) => {
        TokenKind::If
    };
    (then) => {
        TokenKind::Then
    };
    (else) => {
        TokenKind::Else
    };
    (while) => {
        TokenKind::While
    };
    (for) => {
        TokenKind::For
    };
    (to) => {
        TokenKind::To
    };
    (do) => {
        TokenKind::Do
    };
    (let) => {
        TokenKind::Let
    };
    (in) => {
        TokenKind::In
    };
    (end) => {
        TokenKind::End
    };
    (of) => {
        TokenKind::Of
    };
    (break) => {
        TokenKind::Break
    };
    (nil) => {
        TokenKind::Nil
    };
    (function) => {
        TokenKind::Function
    };
    (var) => {
        TokenKind::Var
    };
    (type) => {
        TokenKind::Type
    };
    (import) => {
        TokenKind::Import
    };
    (primitive) => {
        TokenKind::Primitive
    };
    (class) => {
        TokenKind::Class
    };
    (extends) => {
        TokenKind::Extends
    };
    (new) => {
        TokenKind::New
    };

    (,) => {
        TokenKind::Comma
    };
    (:) => {
        TokenKind::Colon
    };
    (;) => {
        TokenKind::Semicolon
    };
    (.) => {
        TokenKind::Period
    };
    (+) => {
        TokenKind::Plus
    };
    (-) => {
        TokenKind::Minus
    };
    (*) => {
        TokenKind::Star
    };
    (/) => {
        TokenKind::Slash
    };
    (=) => {
        TokenKind::Eq
    };
    (<) => {
        TokenKind::Lt
    };
    (>) => {
        TokenKind::Gt
    };
    (&) => {
        TokenKind::Amp
    };
    (|) => {
        TokenKind::Pipe
    };

    (<>) => {
        TokenKind::Neq
    };
    (<=) => {
        TokenKind::Lte
    };
    (>=) => {
        TokenKind::Gte
    };
    (:=) => {
        TokenKind::Assign
    };

    ('(') => {
        TokenKind::LParen
    };
    (')') => {
        TokenKind::RParen
    };
    ('{') => {
        TokenKind::LBrace
    };
    ('}') => {
        TokenKind::RBrace
    };
    ('[') => {
        TokenKind::LBracket
    };
    (']') => {
        TokenKind::RBracket
    };
}
