use std::fmt;

use tig_common::{
    temp::{Label, Temp},
    SmolStr, Span,
};

use crate::{ir, op, translate::level, Frame, IR};

#[derive(Clone, PartialEq, Eq)]
pub enum Access {
    /// The formal is at offset `isize` from the frame.
    InFrame(isize),
    /// The formal is in a register.
    Reg(Temp),
}

impl fmt::Debug for Access {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            let width = f.width().unwrap_or_default();
            let padding = " ".repeat(width);
            match self {
                Access::InFrame(o) => write!(f, "{}InFrame({})", padding, o,),
                Access::Reg(r) => write!(f, "{}Reg(Temp({}))", padding, r,),
            }
        } else {
            match self {
                Access::InFrame(o) => f.debug_tuple("InFrame").field(&o).finish(),
                Access::Reg(t) => f.debug_tuple("Reg").field(&t).finish(),
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Amd64Frame {
    name: Label,
    offset: isize,
    formals: Vec<Access>,
}

impl fmt::Debug for Amd64Frame {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            let width = f.width().unwrap_or_default();
            let padding = " ".repeat(width);
            write!(
                f,
                "{}Frame({}) - {}{}",
                padding,
                self.name,
                self.offset,
                if !self.formals.is_empty() {
                    format!(
                        "\n{}Formals\n{}",
                        " ".repeat(width + 2),
                        self.formals
                            .iter()
                            .map(|f| format!("{:#width$?}", f, width = width + 4))
                            .collect::<Vec<_>>()
                            .join("\n")
                    )
                } else {
                    "".to_string()
                },
            )
        } else {
            f.debug_struct("Amd64Frame")
                .field("name", &self.name)
                .field("offset", &self.offset)
                .field("formals", &self.formals)
                .finish()
        }
    }
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

    fn fp() -> Temp {
        Temp::named(SmolStr::new_inline("fp"))
    }

    fn rv() -> Temp {
        Temp::named(SmolStr::new_inline("rv"))
    }

    fn proc_entry_exit(&self, _level: &level::Level<Self>, _body: Box<ir::Expr>) {
        todo!()
    }

    fn proc_entry_exit_1(&self, body: Box<ir::Stmt>) -> Box<ir::Stmt> {
        body
    }

    fn proc_entry_exit_3(&self, _stmt: Box<ir::Stmt>) -> Box<ir::Stmt> {
        todo!()
    }

    fn expr(access: &Self::Access, expr: Box<ir::Expr>) -> Box<ir::Expr> {
        let span = expr.span;
        match access {
            // If it is an access to a variable InFrame, return a memory
            // access pointing to where the variable is stored in memory.
            Access::InFrame(offset) => {
                let (op, offset) = if *offset >= 0 {
                    (op![+], *offset as usize)
                } else {
                    let offset: usize = offset.abs().try_into().expect("how...");
                    (op![-], offset)
                };

                IR![e mem, span,
                    IR![
                        e binop, span, op,
                        expr,
                        IR![e const, span, offset],
                    ],
                ]
            }
            // Otherwise, just return the temporary.
            Access::Reg(r) => IR![e temp, span, r.clone()],
        }
    }

    fn external_call(span: Span, name: &str, args: Vec<Box<ir::Expr>>) -> Box<ir::Expr> {
        IR![e call, span,
            IR![e name, span, Label::raw(name)],
            args,
        ]
    }
}
