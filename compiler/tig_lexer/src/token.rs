use smol_str::SmolStr;
use tig_common::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub span: Span,
    pub kind: TokenKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    Eof,
    Unknown(char),

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

    Ident(SmolStr),

    Function,
    Main,
}

impl TokenKind {
    pub fn is_keyword(&self) -> bool {
        use TokenKind::*;
        matches!(self, Function | Main)
    }
}

#[macro_export]
macro_rules! T {
    ('(') => { TokenKind::LParen };
    (')') => { TokenKind::RParen };
    ('{') => { TokenKind::LBrace };
    ('}') => { TokenKind::RBrace };
    ('[') => { TokenKind::LBracket };
    (']') => { TokenKind::RBracket };

    (+) => { TokenKind::Plus };
    (-) => { TokenKind::Minus };
    (*) => { TokenKind::Star };
    (/) => { TokenKind::Slash };

    (ident $id:expr) => { TokenKind::Ident($id.into()) };
    (_main) => { TokenKind::Main };
    (function) => { TokenKind::Function };

    (eof) => { TokenKind::Eof };
}
