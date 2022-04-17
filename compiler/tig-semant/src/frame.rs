// Type Access
// new frame (name: Label, formals: Vec<bool>) -> Frame
// frame.name() -> Label
// frame.formals() -> Vec<Access>
// frame.alloc_local(bool) -> Access

pub mod amd64;

use std::{
    cell::RefCell,
    fmt::{self, Debug},
    rc::Rc,
};
use tig_common::{
    temp::{Label, Temp},
    Span,
};

use crate::{ir, translate::level};

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
pub trait Frame: Debug + Clone + PartialEq + Eq {
    /// Returns the size of a native word in bytes (the size of a register).
    const WORD_SIZE: usize;

    /// How many formals can be passed to a frame via registers, before they start spilling out to
    /// memory.
    const MAX_FORMALS_IN_REGISTERS: usize;

    type Access: Debug + Clone + PartialEq + Eq;

    /// Creates a new frame (function) with `label` and the list of formals`.
    /// `formals` is a list of the formals to the function, and whether they escape or not.
    fn new(label: Label, formals: impl Into<Vec<bool>>) -> Self;

    /// Returns the name of the frame.
    fn name(&self) -> Label;

    /// Returns the array of access calculated for the frame.
    fn formals(&self) -> &[Self::Access];

    /// Allocates a new local, and returns the access calculated for it.
    fn alloc_local(&mut self, escapes: bool) -> Self::Access;

    /// Frame pointer
    fn fp() -> Temp;

    /// Return value register
    fn rv() -> Temp;

    fn proc_entry_exit(&self, level: &level::Level<Self>, body: Box<ir::Expr>);

    /// Adds required information to the prologue and epiloque of a Frame.
    ///
    /// * Instructions to save "escaping" arguments - including the static link - into the frame,
    /// and to move nonescaping arguments into fresh temporary registers.
    /// * Store instructions to save any callee-save registers - including the return address
    /// register - used within the function.
    /// * Load instructions to restore the callee-save registers.
    fn proc_entry_exit_1(&self, body: Box<ir::Stmt>) -> Box<ir::Stmt>;

    /// Adds required information to the prologue and epiloque of a Frame.
    ///
    /// * Pseudo-instructions, as needed in the assembly language, to announce the beginning of a
    /// function.
    /// * An instruction to adjust the stack pointer (to allocate a new frame).
    /// * An instruction to reset the stack pointer (to deallocate the frame).
    /// * Pseudo-instructions, as needed, to announce the end of a function.
    /// * A label definition for the function name.
    /// * A return instruction (JUMP to the return address).
    ///
    fn proc_entry_exit_3(&self, stmt: Box<ir::Stmt>) -> Box<ir::Stmt>;

    /// Given an access, and the frame pointer or the calculated static link, generate an
    /// expression for accessing the spcified variable from within the frame.
    fn expr(access: &Self::Access, expr: Box<ir::Expr>) -> Box<ir::Expr>;

    /// Generates the appropriate code to call an external function.
    fn external_call(span: Span, name: &str, args: Vec<Box<ir::Expr>>) -> Box<ir::Expr>;
}

#[derive(Clone, PartialEq, Eq)]
pub enum Fragment<F: Frame> {
    Proc {
        body: Box<ir::Stmt>,
        frame: Rc<RefCell<F>>,
    },
    String {
        label: Label,
        string: Vec<u8>,
    },
}

impl<F: Frame> fmt::Debug for Fragment<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            let width = f.width().unwrap_or_default();
            let padding = " ".repeat(width);
            match self {
                Fragment::Proc { body, frame } => write!(
                    f,
                    "{}{}..{}: Procedure\n{:#width$?}\n{:#width$?}",
                    padding,
                    body.span.lo,
                    body.span.hi,
                    frame.borrow(),
                    body,
                    width = width + 2,
                ),
                Fragment::String { label, string } => write!(
                    f,
                    "{}String({})\n{}\"{}\"",
                    padding,
                    label,
                    " ".repeat(width + 2),
                    String::from_utf8_lossy(string),
                ),
            }
        } else {
            match self {
                Fragment::Proc { body, frame } => f
                    .debug_struct("Proc")
                    .field("body", &body)
                    .field("frame", &frame)
                    .finish(),
                Fragment::String { label, string } => f
                    .debug_struct("String")
                    .field("label", &label)
                    .field("string", &string)
                    .finish(),
            }
        }
    }
}
