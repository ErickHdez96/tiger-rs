// Type Access
// new frame (name: Label, formals: Vec<bool>) -> Frame
// frame.name() -> Label
// frame.formals() -> Vec<Access>
// frame.alloc_local(bool) -> Access

use tig_common::temp::Label;

/// A Frame represents the frame view of a function. The formals being the parameters it receives.
/// A function has to decide if it will store its variables on registers, or in memory at a
/// specific offset from its frame.
///
/// A Frame holds:
/// * The locations of all the formals.
/// * Instructions required to implement the "view shift" (e.g. entering and leaving the frame, and
/// moving the arguments to where the function expects them).
/// * Number of locals allocated so far.
/// * The label at which the function's machine code is to begin.
pub trait Frame {
    type Access;

    /// Creates a new frame (function) with `label` and the list of formals`.
    /// `formals` is a list of the formals to the function, and whether they escape or not.
    fn new(label: Label, formals: impl Into<Vec<bool>>) -> Self;

    /// Returns the size of a native word in bytes (the size of a register).
    fn word_size() -> usize;

    fn name(&self) -> Label;

    fn formals(&self) -> &[Self::Access];

    fn alloc_local(&mut self, escapes: bool) -> &Self::Access;
}
