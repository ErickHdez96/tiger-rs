/// A span in the source code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub lo: u32,
    pub hi: u32,
}

impl Span {
    pub fn new(lo: u32, hi: u32) -> Self {
        Self { lo, hi }
    }

    /// Create a new Span (self.lo, other.end).
    pub fn extend(self, end: Self) -> Self {
        Self {
            lo: self.lo,
            hi: end.hi,
        }
    }
}
