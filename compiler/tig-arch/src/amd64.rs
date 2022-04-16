use tig_common::temp::{Label, Temp};

use crate::Frame;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Amd64 {
    name: Label,
    offset: isize,
    formals: Vec<Access>,
    locals: Vec<Access>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Access {
    /// The formal is at offset `isize` from the frame.
    InFrame(isize),
    /// The formal is in a register.
    Reg(Temp),
}

impl Frame for Amd64 {
    type Access = Access;

    // Calculate:
    // * How the parameter will be seen from inside the function (register, or frame location).
    // * What instructions must be produced to implement the view shift.
    fn new(name: Label, formals: impl Into<Vec<bool>>) -> Self {
        let formals = formals.into();
        let mut frame_formals = vec![];
        let word_size = Self::word_size() as isize;
        // The formals will be below the fp, since the stack grows downwards, below the fp means
        // a positive offset. Calculate the maximum offset needed.
        let mut offset = formals
            .iter()
            .fold(0, |acc, f| if *f { acc + word_size } else { acc });

        for f in formals {
            if f {
                frame_formals.push(Access::InFrame(offset));
                offset -= Self::word_size() as isize;
            } else {
                frame_formals.push(Access::Reg(Temp::new()));
            }
        }

        Self {
            name,
            offset,
            formals: frame_formals,
            locals: vec![],
        }
    }

    fn word_size() -> usize {
        8
    }

    fn name(&self) -> Label {
        // Cloning a Label is O(1)
        self.name.clone()
    }

    fn formals(&self) -> &[Self::Access] {
        &self.formals
    }

    fn alloc_local(&mut self, escapes: bool) -> &Self::Access {
        if escapes {
            self.locals.push(Access::InFrame(self.offset));
            self.offset -= Self::word_size() as isize;
        } else {
            self.locals.push(Access::Reg(Temp::new()));
        }
        &self.locals[self.locals.len() - 1]
    }
}
