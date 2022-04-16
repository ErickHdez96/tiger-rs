use tig_common::temp::{Label, Temp};

use crate::Frame;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Access {
    /// The formal is at offset `isize` from the frame.
    InFrame(isize),
    /// The formal is in a register.
    Reg(Temp),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Amd64Frame {
    name: Label,
    offset: isize,
    formals: Vec<Access>,
}

impl Frame for Amd64Frame {
    const WORD_SIZE: usize = 8;
    const MAX_FORMALS_IN_REGISTERS: usize = 6;
    type Access = Access;

    // Calculate:
    // * How the parameter will be seen from inside the function (register, or frame location).
    // * What instructions must be produced to implement the view shift.
    fn new(name: Label, formals: impl Into<Vec<bool>>) -> Self {
        let mut frame = Amd64Frame {
            name,
            offset: 0,
            formals: vec![],
        };
        let frame_formals = formals
            .into()
            .into_iter()
            .map(|f| frame.alloc_local(f))
            .collect();
        frame.formals = frame_formals;
        frame
    }

    fn name(&self) -> Label {
        // Cloning a Label is O(1)
        self.name.clone()
    }

    fn formals(&self) -> &[Self::Access] {
        &self.formals
    }

    fn alloc_local(&mut self, escapes: bool) -> Self::Access {
        if escapes {
            self.offset -= Self::WORD_SIZE as isize;
            Access::InFrame(self.offset)
        } else {
            Access::Reg(Temp::new())
        }
    }
}
