use std::fmt;

use tig_common::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParserError {
    pub msg: String,
    pub span: Span,
}

impl ParserError {
    pub fn new(msg: impl Into<String>, span: Span) -> Self {
        Self {
            msg: msg.into(),
            span,
        }
    }
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {}): {}", self.span.lo, self.span.hi, self.msg)
    }
}

impl std::error::Error for ParserError {}
