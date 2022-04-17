use std::fmt;

use tig_common::{
    temp::{Label, Temp},
    Span,
};

#[derive(Clone, PartialEq, Eq)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            let width = f.width().unwrap_or_default();
            let padding = " ".repeat(width);
            match &self.kind {
                ExprKind::Const(n) => write!(
                    f,
                    "{}{}..{}: Const({})",
                    padding, self.span.lo, self.span.hi, n
                ),
                ExprKind::Name(n) => write!(
                    f,
                    "{}{}..{}: Name({})",
                    padding, self.span.lo, self.span.hi, n
                ),
                ExprKind::Temp(t) => write!(
                    f,
                    "{}{}..{}: Temp({})",
                    padding, self.span.lo, self.span.hi, t,
                ),
                ExprKind::BinOp { op, left, right } => write!(
                    f,
                    "{}{}..{}: BinOp({})\n\
                     {}{}..{}: Left\n{:#width$?}\n\
                     {}{}..{}: Right\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    op,
                    " ".repeat(width + 2),
                    left.span.lo,
                    left.span.hi,
                    left,
                    " ".repeat(width + 2),
                    right.span.lo,
                    right.span.hi,
                    right,
                    width = width + 4,
                ),
                ExprKind::Mem(e) => write!(
                    f,
                    "{}{}..{}: Mem\n\
                     {}{}..{}: Expr\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    e.span.lo,
                    e.span.hi,
                    e,
                    width = width + 4,
                ),
                ExprKind::Call { func, arguments } => write!(
                    f,
                    "{}{}..{}: Call\n\
                     {}{}..{}: Function\n{:#width$?}{}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    func.span.lo,
                    func.span.hi,
                    func,
                    if !arguments.is_empty() {
                        format!(
                            "\n{}{}..{}: Arguments\n{}",
                            " ".repeat(width + 2),
                            arguments.get(0).map(|a| a.span.lo).unwrap_or_default(),
                            arguments
                                .iter()
                                .last()
                                .map(|a| a.span.hi)
                                .unwrap_or_default(),
                            arguments
                                .iter()
                                .map(|a| format!("{:#width$?}", a, width = width + 4))
                                .collect::<Vec<_>>()
                                .join("\n")
                        )
                    } else {
                        "".to_string()
                    },
                    width = width + 4,
                ),
                ExprKind::ESeq(stmt, expr) => write!(
                    f,
                    "{}{}..{}: ESeq\n\
                     {}{}..{}: Stmt\n{:#width$?}\n\
                     {}{}..{}: Expr\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    stmt.span.lo,
                    stmt.span.hi,
                    stmt,
                    " ".repeat(width + 2),
                    expr.span.lo,
                    expr.span.hi,
                    expr,
                    width = width + 4,
                ),
            }
        } else {
            f.debug_struct("Expr")
                .field("span", &self.span)
                .field("kind", &self.kind)
                .finish()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    /// CONST(i) Integer constant _i_.
    Const(usize),
    /// NAME(n) The symbolic constant _n_ (corresponding to an assembly language label).
    Name(Label),
    /// TEMP(t) Temporary _t_. A temporary in the abstract machine is similar to register in a real
    /// machine. However, the abstract machine has an infinite number of temporaries.
    Temp(Temp),
    /// BINOP(o, e1, e2) The application of binary operator o to operands _e1_, _e2_. Subexpression
    /// _e1_ is evaluated before _e2_. The integer arithmetic operators are PLUS, MINUS, MUL, DIV;
    /// the integer bitwise logical operators are AND, OR, XOR; the integer logical shift operators
    /// are LSHIFT, RSHIFT; the integer arithmetic right-shift is ARSHIFT. The Tiger language has
    /// no logical operators, but the intermediate language is meant to be independent of any
    /// source language; also, the logical operators might be used in implementing other features
    /// of Tiger.
    BinOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    /// MEM(e) The contents of wordSize bytes of memory starting at address _e_ (where wordSize is
    /// defined in the Frame module). Note that when MEM is used as the left child of a MOVE, it
    /// means "store", but anywhere else it means "fetch".
    Mem(Box<Expr>),
    /// CALL(f, l) A procedure call: the application of function _f_ to argument list _l_. The
    /// subexpression _f_ is evaluated before the arguments which are evaluated left to right.
    Call {
        func: Box<Expr>,
        arguments: Vec<Box<Expr>>,
    },
    /// ESEQ(s, e) The statement _s_ is evaluated for side effects, then _e_ is evaluated for a result.
    ESeq(Box<Stmt>, Box<Expr>),
}

#[derive(Clone, PartialEq, Eq)]
pub struct Stmt {
    pub span: Span,
    pub kind: StmtKind,
}

impl fmt::Debug for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            let width = f.width().unwrap_or_default();
            let padding = " ".repeat(width);
            match &self.kind {
                StmtKind::Move(e1, e2) => write!(
                    f,
                    "{}{}..{}: Move\n\
                     {}{}..{}: Destination\n{:#width$?}\n\
                     {}{}..{}: Source\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    e1.span.lo,
                    e1.span.hi,
                    e1,
                    " ".repeat(width + 2),
                    e2.span.lo,
                    e2.span.hi,
                    e2,
                    width = width + 4,
                ),
                StmtKind::Expr(e) => write!(
                    f,
                    "{}{}..{}: StmtExpr\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    e,
                    width = width + 2,
                ),
                StmtKind::Jump {
                    destination,
                    targets,
                } => write!(
                    f,
                    "{}{}..{}: Jump([{}])\n\
                     {}{}..{}: Target\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    targets
                        .iter()
                        .map(|l| format!("{}", l))
                        .collect::<Vec<_>>()
                        .join(", "),
                    " ".repeat(width + 2),
                    destination.span.lo,
                    destination.span.hi,
                    destination,
                    width = width + 4
                ),
                StmtKind::CJump {
                    op,
                    left,
                    right,
                    true_label,
                    false_label,
                } => write!(
                    f,
                    "{}{}..{}: CJmp({}) -> {} | {}\n\
                     {}{}..{}: Left\n{:#width$?}\n\
                     {}{}..{}: Right\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    op,
                    true_label,
                    false_label,
                    " ".repeat(width + 2),
                    left.span.lo,
                    left.span.hi,
                    left,
                    " ".repeat(width + 2),
                    right.span.lo,
                    right.span.hi,
                    right,
                    width = width + 4
                ),
                StmtKind::Seq(s1, s2) => write!(
                    f,
                    "{}{}..{}: Seq\n\
                     {}{}..{}: Stmt1\n{:#width$?}\n\
                     {}{}..{}: Stmt2\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    s1.span.lo,
                    s1.span.hi,
                    s1,
                    " ".repeat(width + 2),
                    s2.span.lo,
                    s2.span.hi,
                    s2,
                    width = width + 4
                ),
                StmtKind::Label(l) => write!(
                    f,
                    "{}{}..{}: Label({})",
                    padding, self.span.lo, self.span.hi, l,
                ),
            }
        } else {
            f.debug_struct("Stmt")
                .field("span", &self.span)
                .field("kind", &self.kind)
                .finish()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StmtKind {
    /// MOVE(TEMP(t), e) Evaluate _e_ and move it to temporary _t_.
    /// MOVE(MEM(e1), e1) Evaluate _e1_, yielding address _a_. Then evaluate _e2_, and store the
    /// result into wordSize bytes of memory starting at _a_.
    Move(Box<Expr>, Box<Expr>),
    /// EXP(e) Evaluate _e_ and discard the result.
    Expr(Box<Expr>),
    /// JUMP(e, labs) Transfer control (jump) to address _e_. The destination _e_ may be a literal
    /// label, as in NAME(lab), or it may be an address calculated by any other kind of expression.
    /// The list of labels _labs_ specifies specifies all the possible locations that the
    /// expression _e_ can evaluate to; this is necessary for dataflow analysis later. The common
    /// case of jumping to a known label _l_ is written as JUMP(NAME(l), [l]).
    Jump {
        destination: Box<Expr>,
        targets: Vec<Label>,
    },
    /// CJUMP(o, e1, e2, t, f) Evaluate _e1_, _e2_ in that order, yielding values _a_, _b_. Then
    /// compare _a_, _b_ using the relation operator _o_. If the result is _true_, jump to _t_;
    /// otherwise jump to _f_. The relational operators are EQ and NE for intenger equality and
    /// nonequality (signed or unsigned); signed integer inequalities LT, GT, LE, GE; and usigned
    /// integer inequalities ULT, ULE, UGT, UGE.
    CJump {
        op: RelOp,
        left: Box<Expr>,
        right: Box<Expr>,
        true_label: Label,
        false_label: Label,
    },
    /// SEQ(s1, s2) The statement _s1_ followed by _s2_.
    Seq(Box<Stmt>, Box<Stmt>),
    /// LABEL(n) Define the constant value of name _n_ to be the current machine code address. This
    /// is like a label definition in assembly language. The value NAME(n) may be the target of
    /// jumps, calls, etc.
    Label(Label),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    And,
    Or,
    LShift,
    RShift,
    ARshift,
    Xor,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                BinOp::Add => "+",
                BinOp::Subtract => "-",
                BinOp::Multiply => "*",
                BinOp::Divide => "/",
                BinOp::And => "&",
                BinOp::Or => "|",
                BinOp::LShift => "<<",
                BinOp::RShift => ">>",
                BinOp::ARshift => "a>>",
                BinOp::Xor => "^",
            }
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelOp {
    Eq,
    Neq,
    Lt,
    Gt,
    Le,
    Ge,
    Ult,
    Ule,
    Ugt,
    Uge,
}

impl fmt::Display for RelOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                RelOp::Eq => "=",
                RelOp::Neq => "<>",
                RelOp::Lt => "<",
                RelOp::Gt => ">",
                RelOp::Le => "<=",
                RelOp::Ge => ">=",
                RelOp::Ult => "u<",
                RelOp::Ule => "u<=",
                RelOp::Ugt => "u>",
                RelOp::Uge => "u>=",
            }
        )
    }
}

#[macro_export]
macro_rules! IR {
    (e const, $span:expr, $n:expr $(,)?) => {
        Box::new(ir::Expr {
            span: $span,
            kind: ir::ExprKind::Const($n),
        })
    };
    (e name, $span:expr, $name:expr $(,)?) => {
        Box::new(ir::Expr {
            span: $span,
            kind: ir::ExprKind::Name($name),
        })
    };
    (e temp, $span:expr, $temp:expr $(,)?) => {
        Box::new(ir::Expr {
            span: $span,
            kind: ir::ExprKind::Temp($temp),
        })
    };
    (e binop, $span:expr, $op:expr, $left:expr, $right:expr $(,)?) => {
        Box::new(ir::Expr {
            span: $span,
            kind: ir::ExprKind::BinOp {
                op: $op,
                left: $left,
                right: $right,
            },
        })
    };
    (e mem, $span:expr, $expr:expr, $(,)?) => {
        Box::new(ir::Expr {
            span: $span,
            kind: ir::ExprKind::Mem($expr),
        })
    };
    (e call, $span:expr, $fn:expr, $args:expr $(,)?) => {
        Box::new(ir::Expr {
            span: $span,
            kind: ir::ExprKind::Call {
                func: $fn,
                arguments: $args,
            }
        })
    };
    (e eseq, $span:expr, $stmt:expr, $e:expr $(,)?) => {
        Box::new(ir::Expr {
            span: $span,
            kind: ir::ExprKind::ESeq($stmt, $e),
        })
    };

    (s move, $span:expr, $dest:expr, $source:expr $(,)?) => {
        Box::new(ir::Stmt {
            span: $span,
            kind: ir::StmtKind::Move($dest, $source),
        })
    };
    (s expr, $span:expr, $expr:expr $(,)?) => {
        Box::new(ir::Stmt {
            span: $span,
            kind: ir::StmtKind::Expr($expr),
        })
    };
    (s jmpl, $span:expr, $l:expr $(,)?) => {
        Box::new(ir::Stmt {
            span: $span,
            kind: ir::StmtKind::Jump {
                destination: IR![e name, $span, $l.clone()],
                targets: vec![$l],
            }
        })
    };
    (s cjmp, $span:expr, $op:expr, $left:expr, $right:expr, $true:expr, $false:expr $(,)?) => {
        Box::new(ir::Stmt {
            span: $span,
            kind: ir::StmtKind::CJump {
                op: $op,
                left: $left,
                right: $right,
                true_label: $true,
                false_label: $false,
            }
        })
    };
    (s seq, $span:expr, $stmt1:expr, $stmt2:expr $(,)?) => {
        Box::new(ir::Stmt {
            span: $span,
            kind: ir::StmtKind::Seq($stmt1, $stmt2),
        })
    };
    (s seq, $span:expr, $stmt1:expr, $stmt2:expr, $($stmt3:expr),* $(,)?) => {
        IR![
            s seq,
            $span,
            IR![s seq, $span, $stmt1, $stmt2],
            $($stmt3),*
        ]
    };
    (s label, $span:expr, $label:expr) => {
        Box::new(ir::Stmt {
            span: $span,
            kind: ir::StmtKind::Label($label),
        })
    };
}

#[macro_export]
macro_rules! op {
    (+) => {
        ir::BinOp::Add
    };
    (-) => {
        ir::BinOp::Subtract
    };
    (*) => {
        ir::BinOp::Multiply
    };
    (/) => {
        ir::BinOp::Divide
    };
    (&) => {
        ir::BinOp::And
    };
    (|) => {
        ir::BinOp::Or
    };
    (<<) => {
        ir::BinOp::LShift
    };
    (>>) => {
        ir::BinOp::RShift
    };
    (a>>) => {
        ir::BinOp::AShift
    };
    (^) => {
        ir::BinOp::Xor
    };
    (=) => {
        ir::RelOp::Eq
    };
    (<>) => {
        ir::RelOp::Neq
    };
    (<) => {
        ir::RelOp::Lt
    };
    (>) => {
        ir::RelOp::Gt
    };
    (<=) => {
        ir::RelOp::Le
    };
    (>=) => {
        ir::RelOp::Ge
    };
    (u<) => {
        ir::RelOp::Ult
    };
    (u<=) => {
        ir::RelOp::Ule
    };
    (u>) => {
        ir::RelOp::Ugt
    };
    (u>=) => {
        ir::RelOp::Uge
    };
}
