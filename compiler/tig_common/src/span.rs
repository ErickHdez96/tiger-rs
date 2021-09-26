/// A Span represents a region in the original source code, from an offset (lo inclusive), up to
/// another offset (hi exclusive).
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Span {
    pub lo: u32,
    pub hi: u32,
}

impl Span {
    pub fn new(lo: u32, hi: u32) -> Self {
        Self { lo, hi }
    }

    /// Creates a new Span with the current span's lo and the other span's hi.
    ///
    /// # Examples
    ///
    /// ```
    /// use tig_common::Span;
    ///
    /// let s1 = Span::new(0, 5);
    /// let s2 = Span::new(10, 15);
    /// let s3 = s1.extend(s2);
    /// assert_eq!(s3, Span::new(0, 15));
    /// ```
    pub fn extend(self, other: Self) -> Self {
        Self { lo: self.lo, hi: other.hi }
    }
}
