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

    Colon,

    Ident(SmolStr),
    Int(SmolStr),

    Function,
    Nil,
    Var,
    Type,
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
        matches!(self, Function | Nil | Var | Type)
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
                TokenKind::Colon => ":",
                TokenKind::Ident(id) => id.as_str(),
                TokenKind::Int(n) => n.as_str(),
                TokenKind::Function => "function",
                TokenKind::Nil => "nil",
                TokenKind::Var => "var",
                TokenKind::Type => "type",
            }
        )
    }
}

#[macro_export]
macro_rules! T {
    (=) => {
        TokenKind::Eq
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

    (:) => {
        TokenKind::Colon
    };

    (ident $id:expr) => {
        TokenKind::Ident($id.into())
    };
    (int $int:expr) => {
        TokenKind::Int($int.into())
    };
    (function) => {
        TokenKind::Function
    };
    (nil) => {
        TokenKind::Nil
    };
    (var) => {
        TokenKind::Var
    };
    (type) => {
        TokenKind::Type
    };

    (eof) => {
        TokenKind::Eof
    };
}
