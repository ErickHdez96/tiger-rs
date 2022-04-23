use tig_common::{Span, temp::{Temp, Label}};

#[derive(Debug)]
pub struct Instruction {
    pub span: Span,
    pub kind: InstructionKind,
}

impl Instruction {
    pub fn format(self, t: impl Fn(Temp) -> String) -> String {
        match self.kind {
            InstructionKind::Op { mut asm, destination, source, .. } => {
                for (i, d) in destination.into_iter().enumerate() {
                    asm = asm.replace(&format!("'d{}", i), &t(d));
                }

                for (i, s) in source.into_iter().enumerate() {
                    asm = asm.replace(&format!("'s{}", i), &t(s));
                }

                asm
            }
            InstructionKind::Label { asm, .. } => asm,
            InstructionKind::Move { asm, destination, source } => {
                asm.replace("'d", &t(destination)).replace("'s", &t(source))
            }
        }
    }
}

#[derive(Debug)]
pub enum InstructionKind {
    /// It holds an aseembly language instruction `asm`, a list of operand registers `source`, and
    /// a list of result registers `destination`. Either of them may be empty. Operations that
    /// always fall through to the next instruction have `jump = None`; other operations have a
    /// list of _target_ labels to which they may jump (the list must explicitly include the next
    /// instruction if it is possible to fall through to it.
    Op {
        asm: String,
        destination: Vec<Temp>,
        source: Vec<Temp>,
        jump: Option<Vec<Label>>,
    },

    /// A point in a program to which jumps may go. It has an `asm` component showing how the label
    /// will look in the assembly-language program, and a `label` component identifying which
    /// label-symbol was used.
    Label {
        asm: String,
        label: Label,
    },

    /// Like an `Op`, but must perform only data transfer. If `destination` and `source` get
    /// assigned the same register, the move may be removed.
    Move {
        asm: String,
        destination: Temp,
        source: Temp,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_assembly_format() {
        let source = Temp::new();
        let source2 = Temp::new();
        let destination = Temp::new();

        let asm = Instruction {
            span: Span::new(0, 1),
            kind: InstructionKind::Move {
                asm: "mov 'd, 's".into(),
                source: source.clone(),
                destination: destination.clone(),
            },
        };

        assert_eq!(
            asm.format(|t| {
                if t == source {
                    "r1".into()
                } else {
                    "r0".into()
                }
            }),
            "mov r0, r1",
        );

        let asm = Instruction {
            span: Span::new(0, 1),
            kind: InstructionKind::Op {
                asm: "add 'd0, 's0, 's1".into(),
                source: vec![source.clone(), source2.clone()],
                destination: vec![destination.clone()],
                jump: None,
            },
        };

        assert_eq!(
            asm.format(|t| {
                if t == source {
                    "r1".into()
                } else if t == source2 {
                    "r2".into()
                } else {
                    "r0".into()
                }
            }),
            "add r0, r1, r2",
        );
    }
}
