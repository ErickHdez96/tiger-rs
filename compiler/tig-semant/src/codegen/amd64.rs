use tig_common::temp::Temp;

use crate::{ir, asm::{Instruction, InstructionKind}};

#[derive(Default)]
struct Muncher {
    insts: Vec<Instruction>,
}

impl Muncher {
    fn emit(&mut self, i: Instruction) {
        self.insts.push(i);
    }

    fn munch_stmt(&mut self, s: Box<ir::Stmt>) {
        let span = s.span;

        match s.kind {
            ir::StmtKind::Move(_, _) => todo!(),
            ir::StmtKind::Expr(_) => todo!(),
            ir::StmtKind::Jump { destination, targets } => todo!(),
            ir::StmtKind::CJump { op, left, right, true_label, false_label } => todo!(),
            ir::StmtKind::Seq(_, _) => todo!(),
            ir::StmtKind::Label(label) => {
                self.emit(Instruction {
                    span,
                    kind: InstructionKind::Label {
                        asm: format!("{}:", label),
                        label,
                    },
                });
            }
        }
    }

    fn munch_expr(&mut self, e: Box<ir::Expr>) -> Temp {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
