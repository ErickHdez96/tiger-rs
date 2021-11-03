use std::fmt::Display;

use tig_common::{SmolStr, Span};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub span: Span,
    pub kind: TokenKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    Eof,
    Unknown(char),
    Dummy,

    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
    Assign,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    Plus,
    Minus,
    Star,
    Slash,

    Comma,
    Dot,
    Colon,
    Semicolon,

    Ampersand,
    Pipe,

    Ident(SmolStr),
    Int(SmolStr),
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
}

impl Token {
    pub fn dummy() -> Self {
        Token {
            span: Span { lo: 0, hi: 1 },
            kind: TokenKind::Dummy,
        }
    }
}

impl TokenKind {
    pub fn is_keyword(&self) -> bool {
        use TokenKind::*;
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
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TokenKind::Eof => "<eof>",
                TokenKind::Unknown(c) => return c.fmt(f),
                TokenKind::Dummy => "<dummy>",
                TokenKind::Eq => "=",
                TokenKind::Neq => "<>",
                TokenKind::Lt => "<",
                TokenKind::Lte => "<=",
                TokenKind::Gt => ">",
                TokenKind::Gte => ">=",
                TokenKind::Assign => ":=",
                TokenKind::LParen => "(",
                TokenKind::RParen => ")",
                TokenKind::LBrace => "{",
                TokenKind::RBrace => "}",
                TokenKind::LBracket => "[",
                TokenKind::RBracket => "]",
                TokenKind::Plus => "+",
                TokenKind::Minus => "-",
                TokenKind::Star => "*",
                TokenKind::Slash => "/",
                TokenKind::Comma => ",",
                TokenKind::Dot => ".",
                TokenKind::Colon => ":",
                TokenKind::Semicolon => ";",
                TokenKind::Ampersand => "&",
                TokenKind::Pipe => "|",
                TokenKind::Ident(id) => id.as_str(),
                TokenKind::Int(n) => n.as_str(),
                TokenKind::String(s) => s.as_str(),
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
            }
        )
    }
}

#[macro_export]
macro_rules! T {
    (=) => {
        TokenKind::Eq
    };
    (<>) => {
        TokenKind::Neq
    };
    (<) => {
        TokenKind::Lt
    };
    (<=) => {
        TokenKind::Lte
    };
    (>) => {
        TokenKind::Gt
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

    (,) => {
        TokenKind::Comma
    };
    (.) => {
        TokenKind::Dot
    };
    (;) => {
        TokenKind::Semicolon
    };
    (:) => {
        TokenKind::Colon
    };

    (&) => {
        TokenKind::Ampersand
    };
    (|) => {
        TokenKind::Pipe
    };

    (ident $id:expr) => {
        TokenKind::Ident($id.into())
    };
    (int $int:expr) => {
        TokenKind::Int($int.into())
    };
    (str $str:expr) => {
        TokenKind::String($str.into())
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

    (eof) => {
        TokenKind::Eof
    };
}
