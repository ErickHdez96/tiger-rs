use tig_common::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpannedError {
    pub span: Span,
    pub msg: String,
}

impl SpannedError {
    pub fn new(span: Span, msg: impl Into<String>) -> Self {
        Self {
            span,
            msg: msg.into(),
        }
    }
}

#[macro_export]
macro_rules! SError {
    ($span:expr, $($fmt_arg:tt)+) => {
        SpannedError {
            span: $span.into(),
            msg: format!($($fmt_arg)+),
        }
    }
}
