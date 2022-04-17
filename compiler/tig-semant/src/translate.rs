pub mod level;

use std::{fmt, rc::Rc};

pub use level::Level;
use tig_common::{
    temp::{Label, Temp},
    Span,
};
use tig_syntax::ast;

use crate::{frame::Fragment, ir, op, types, Frame, IR};

pub(crate) enum TExpr {
    /// Expression
    Ex(Box<ir::Expr>),
    /// No result
    Nx(Box<ir::Stmt>),
    /// Conditional, if you pass it a true-destination, and a false-destination, it will make a
    /// statement that evaluates some conditional and then jumps to one of the destinations (the
    /// statement will never "fall through").
    Cx(Span, Box<dyn FnOnce(Label, Label) -> Box<ir::Stmt>>),
}

impl Clone for TExpr {
    fn clone(&self) -> Self {
        match self {
            TExpr::Ex(e) => TExpr::Ex(e.clone()),
            TExpr::Nx(n) => TExpr::Nx(n.clone()),
            TExpr::Cx(_, _) => panic!("ICE: Tried to call clone on an unclonable cx"),
        }
    }
}

impl fmt::Debug for TExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TExpr::Ex(e) => f.debug_tuple("Ex").field(&e).finish(),
            TExpr::Nx(n) => f.debug_tuple("Nx").field(&n).finish(),
            TExpr::Cx(span, _) => f
                .debug_tuple("Cx")
                .field(&span)
                .field(&"Fn(Label, Label) -> Stmt")
                .finish(),
        }
    }
}

impl TExpr {
    pub(crate) fn hole() -> Self {
        TExpr::Ex(IR![e const, Span::new(0, 0), 0])
    }

    pub(crate) fn span(&self) -> Span {
        match self {
            TExpr::Ex(e) => e.span,
            TExpr::Nx(n) => n.span,
            TExpr::Cx(span, _) => *span,
        }
    }

    pub(crate) fn un_ex(self) -> Box<ir::Expr> {
        match self {
            TExpr::Ex(e) => e,
            TExpr::Nx(n) => {
                let span = n.span;
                IR!(e eseq, span, n, IR!(e const, span, 0))
            }
            TExpr::Cx(span, genstmt) => {
                let result = IR![e temp, span, Temp::new()];
                let r#true = Label::named("true");
                let r#false = Label::named("false");

                // mov r, 1
                // cmp -> true, false
                // false:
                //      mov r, 0
                //      jmp true ; Avoid fallthrough // CHECK
                // true:
                //      r
                let compute = IR![s seq, span,
                    IR![s move, span,
                        result.clone(),
                        IR![e const, span, 1],
                    ],
                    genstmt(r#true.clone(), r#false.clone()),
                    IR![s jmpl, span, r#false],
                    IR![s move, span,
                        result.clone(),
                        IR![e const, span, 0],
                    ],
                    IR![s jmpl, span, r#true.clone()],
                    IR![s label, span, r#true],
                ];

                Box::new(ir::Expr {
                    span,
                    kind: ir::ExprKind::ESeq(compute, result),
                })
            }
        }
    }

    pub(crate) fn un_nx(self) -> Box<ir::Stmt> {
        match self {
            TExpr::Nx(n) => n,
            TExpr::Ex(e) => IR![s expr, e.span, e],
            TExpr::Cx(span, genstmt) => {
                let end = Label::new();
                IR![s seq, span,
                    genstmt(end.clone(), end.clone()),
                    IR![s label, span, end]
                ]
            }
        }
    }

    pub(crate) fn un_cx(self) -> Box<dyn FnOnce(Label, Label) -> Box<ir::Stmt>> {
        use ir::ExprKind::*;
        match self {
            TExpr::Cx(_, genstmt) => genstmt,
            TExpr::Ex(e) => match &e.kind {
                // Always jump to the false label.
                Const(0) => Box::new(move |_, f| IR![s jmpl, e.span, f]),
                // Always jump to the true label.
                Const(_) => Box::new(move |t, _| IR![s jmpl, e.span, t]),
                _ => Box::new(move |t, f| {
                    let span = e.span;
                    // cmp e, 0
                    // je false
                    // jne true
                    IR![s cjmp,
                        span,
                        op![=],
                        e,
                        IR![e const, span, 0],
                        f,
                        t,
                    ]
                }),
            },
            TExpr::Nx(_) => panic!("ICE: un_cx should never be called on an Nx {:?}", self),
        }
    }
}

/// Translate a variable declaration.
pub(crate) fn var_dec<F: Frame>(span: Span, access: &level::Access<F>, value: TExpr) -> TExpr {
    // The access of a variable declaration always point to the current level.
    // No need for static links.
    let var = F::expr(&access.access, IR![e temp, span, F::fp()]);
    TExpr::Nx(IR![s move, span,
        var,
        value.un_ex(),
    ])
}

/// Translates an access to an expression pointing to the expected variable.  
///
/// * If the variable lives in the current frame's registers, it returns the temporary where
/// it lives.
/// * If the variable lives in the current frame's stack, a memory load pointing to it is returned.
/// * Otherwise, code is generated to follow the static links to get to the expected level and load
/// the variable from its stack.
pub(crate) fn simple_var<F: Frame>(
    span: Span,
    access: &level::Access<F>,
    level: &Level<F>,
) -> TExpr {
    // Level is where the variable is used.
    // Access is where it was defined.
    let mut current_level = level;
    let mut fp = IR![e temp, span, F::fp()];

    // For every different level, we load the current frame's static link,
    // and go up one level.
    while current_level != &access.level {
        fp = F::expr(
            current_level
                .frame
                .borrow()
                .formals()
                .get(0)
                .expect("ICE: Static link should be precent"),
            fp,
        );

        current_level = current_level
            .parent
            .as_ref()
            .expect("ICE: A level should have been found");
    }

    TExpr::Ex(F::expr(&access.access, fp))
}

// Add bounds checks?
/// Translate an array access.
pub(crate) fn array_access<F: Frame>(span: Span, array: TExpr, index: TExpr) -> TExpr {
    TExpr::Ex(IR![e mem, span,
        IR![e binop, span,
            op![+],
            array.un_ex(),
            IR![e binop, span,
                op![*],
                index.un_ex(),
                IR![e const, span, F::WORD_SIZE],
            ],
        ],
    ])
}

/// Translate a field access to a record.
pub(crate) fn field_access<F: Frame>(
    span: Span,
    record: TExpr,
    field: &ast::Ident,
    ty_fields: &[types::RecordField],
) -> TExpr {
    let mut offset = 0;
    for (i, f) in ty_fields.iter().enumerate() {
        if &f.name == field {
            offset = i;
            break;
        }
    }

    TExpr::Ex(IR![e mem, span,
        IR![e binop, span,
            op![+],
            record.un_ex(),
            IR![e const, span, offset * F::WORD_SIZE],
        ],
    ])
}

/// Translate a record literal.
pub(crate) fn record<F: Frame>(
    span: Span,
    type_fields: &[types::RecordField],
    fields: Vec<TExpr>,
) -> TExpr {
    let result = IR![e temp, span, Temp::new()];
    let word_size = F::WORD_SIZE;
    let record_width = word_size * type_fields.len();

    let mut seq = IR![s move, span,
        result.clone(),
        F::external_call(span, "malloc", vec![IR![e const, span, record_width]]),
    ];

    for (i, f) in fields.into_iter().enumerate() {
        seq = IR![s seq, span,
            seq,
            IR![s move, span,
                IR![e mem, span,
                    IR![e binop, span,
                        op![+],
                        result.clone(),
                        IR![e const, span, word_size * i],
                    ],
                ],
                f.un_ex(),
            ],
        ];
    }

    TExpr::Ex(IR![e eseq, span,
        seq,
        result,
    ])
}

/// Translate an array creation.
pub(crate) fn array<F: Frame>(span: Span, size: TExpr, init: TExpr) -> TExpr {
    let result = IR![e temp, span, Temp::new()];
    let array_size = IR![e temp, span, Temp::new()];
    let word_size = F::WORD_SIZE;

    TExpr::Ex(IR![e eseq, span,
        IR![s seq, span,
            // First calculate array size
            IR![s move, span,
                array_size.clone(),
                IR![e binop, span,
                    op![*],
                    size.un_ex(),
                    IR![e const, span, word_size],
                ],
            ],
            // First call malloc with (size * word size)
            IR![s move, span,
                result.clone(),
                F::external_call(span, "malloc", vec![array_size.clone()]),
            ],
            IR![s expr, span, IR![e call, span,
                IR![e name, span, Label::raw("initArray")],
                vec![
                    result.clone(),
                    array_size,
                    init.un_ex(),
                ],
            ]],
        ],
        result,
    ])
}

/// Translate assign expression.
pub(crate) fn assign(span: Span, var: TExpr, value: TExpr) -> TExpr {
    TExpr::Nx(IR![s move, span,
        var.un_ex(),
        value.un_ex(),
    ])
}

/// Generate a nil expression.
pub(crate) fn nil(span: Span) -> TExpr {
    TExpr::Ex(IR![e const, span, 0])
}

/// Generate a nil expression.
pub(crate) fn string<F>(span: Span, string: Vec<u8>, fragments: &mut Vec<Fragment<F>>) -> TExpr
where
    F: Frame,
{
    let string_l = Label::named("label");
    fragments.push(Fragment::String {
        label: string_l.clone(),
        string,
    });
    TExpr::Ex(IR![e name, span, string_l])
}

/// Translate a literal integer.
pub(crate) fn int(span: Span, n: usize) -> TExpr {
    TExpr::Ex(IR![e const, span, n])
}

/// Translate the unit value.
pub(crate) fn unit(span: Span) -> TExpr {
    // It is basically the same as nil, but the typechecker won't
    // let it be used for pretty much anything.
    TExpr::Ex(IR![e const, span, 0])
}

/// Translate two expressions into an ESeq.
pub(crate) fn eseq(span: Span, e1: TExpr, e2: TExpr) -> TExpr {
    TExpr::Ex(IR![e eseq, span, e1.un_nx(), e2.un_ex()])
}

/// Translate a negation.
pub(crate) fn negate(span: Span, e: TExpr) -> TExpr {
    TExpr::Ex(IR![e binop, span,
        op![-],
        IR![e const, span, 0],
        e.un_ex()
    ])
}

/// Translates a break to the most proximate loop.
pub(crate) fn break_(span: Span, l: &Label) -> TExpr {
    TExpr::Nx(IR![s jmpl, span, l.clone()])
}

/// Generates code to compare two strings.
pub(crate) fn string_cmp<F: Frame>(span: Span, op: ir::RelOp, left: TExpr, right: TExpr) -> TExpr {
    // Deviation: Instead of calling stringEqual to compare two strings for =, and <>
    // we call stringCompare, which returns -1, 0, or 1.
    // -1 left < right
    //  0 left = right
    //  1 left > right

    let result = IR![e temp, span, Temp::new()];
    let end_l = Label::named("cmp_end");
    let negate_l = Label::named("cmp_negate");
    let end_l_s = IR![s label, span, end_l.clone()];
    let negate_l_s = IR![s label, span, negate_l.clone()];
    // call = -1, 0, 1
    let call = F::external_call(span, "stringCompare", vec![left.un_ex(), right.un_ex()]);

    // It generates the following code:
    //
    // mov result, 1
    // cjmp call `op` 0 -> end | neq
    // neq:
    //      mov result, 0
    //      jmp end
    // end:
    //      result
    TExpr::Ex(IR![e eseq, span,
        IR![s seq, span,
            IR![s move, span, result.clone(), IR![e const, span, 1]],
            IR![s cjmp, span,
                op,
                call,
                IR![e const, span, 0],
                end_l.clone(),
                negate_l,
            ],
            negate_l_s,
            IR![s move, span, result.clone(), IR![e const, span, 0]],
            IR![s jmpl, span, end_l],
            end_l_s,
        ],
        result,
    ])
}

/// Translate a binary expression
pub(crate) fn binary_op(span: Span, op: ast::BinOp, left: TExpr, right: TExpr) -> TExpr {
    match op {
        ast::BinOp::Add | ast::BinOp::Subtract | ast::BinOp::Multiply | ast::BinOp::Divide => {
            let op = match op {
                ast::BinOp::Add => op![+],
                ast::BinOp::Subtract => op![-],
                ast::BinOp::Multiply => op![*],
                _ => op![/],
            };

            TExpr::Ex(IR![e binop, span,
                op,
                left.un_ex(),
                right.un_ex(),
            ])
        }
        ast::BinOp::And => {
            TExpr::Cx(
                span,
                Box::new(move |t, f| {
                    let middle_l = Label::named("second_op");

                    IR![s seq, span,
                        // If left evaluates to true, continue with the right exp,
                        // otherwise short circuit to false.
                        left.un_cx()(middle_l.clone(), f.clone()),
                        IR![s label, span, middle_l],
                        right.un_cx()(t, f),
                    ]
                }),
            )
        }
        ast::BinOp::Or => {
            TExpr::Cx(
                span,
                Box::new(move |t, f| {
                    let middle_l = Label::named("second_op");

                    IR![s seq, span,
                        // If left evaluates to true, shortcircuit to true,
                        // otherwise evaluate false.
                        left.un_cx()(t.clone(), middle_l.clone()),
                        IR![s label, span, middle_l],
                        right.un_cx()(t, f),
                    ]
                }),
            )
        }
        _ => {
            let op = match op {
                ast::BinOp::Eq => op![=],
                ast::BinOp::Neq => op![<>],
                ast::BinOp::Gt => op![>],
                ast::BinOp::Lt => op![<],
                ast::BinOp::Gte => op![>=],
                _ => op![<=],
            };

            TExpr::Cx(
                span,
                Box::new(move |t, f| IR![s cjmp, span, op, left.un_ex(), right.un_ex(), t, f]),
            )
        }
    }
}

pub(crate) fn let_(span: Span, decs: Vec<TExpr>, body: TExpr) -> TExpr {
    let mut decs = decs.into_iter();
    let mut let_decs = match decs.next() {
        Some(d) => d.un_nx(),
        None => return body,
    };

    for d in decs {
        let_decs = IR![s seq, span,
            let_decs,
            d.un_nx(),
        ];
    }

    TExpr::Ex(IR![e eseq, span,
        let_decs,
        body.un_ex(),
    ])
}

/// Translate an if expression/statement.
pub(crate) fn if_(
    span: Span,
    cond: TExpr,
    then_b: TExpr,
    else_b: TExpr,
    ignore_res: bool,
) -> TExpr {
    let true_l = Label::named("true");
    let false_l = Label::named("false");
    let cond = cond.un_cx()(true_l.clone(), false_l.clone());
    let then_span = then_b.span();
    let else_span = else_b.span();
    let true_l = IR![s label, span, true_l];
    let false_l = IR![s label, span, false_l];
    let end_l = Label::named("end");
    let end_l_s = IR![s label, span, end_l.clone()];

    if ignore_res {
        TExpr::Nx(IR![s seq, span,
            // cmp -> true | false
            cond,
            // true:
            true_l,
            // then
            then_b.un_nx(),
            // jmp end
            IR![s jmpl, then_span, end_l.clone()],
            // false:
            false_l,
            // else
            else_b.un_nx(),
            // jmp end
            IR![s jmpl, else_span, end_l],
            // end:
            end_l_s,
        ])
    } else {
        let result = IR![e temp, span, Temp::new()];
        TExpr::Ex(IR![e eseq, span,
            IR![s seq, span,
                // cmp -> true | false
                cond,
                // true:
                true_l,
                // mov result, e1
                IR![s move, then_span, result.clone(), then_b.un_ex()],
                // jmp end
                IR![s jmpl, then_span, end_l.clone()],
                // false:
                false_l,
                // mov 0, e2
                IR![s move, else_span, result.clone(), else_b.un_ex()],
                // jmp end
                IR![s jmpl, else_span, end_l],
                // end:
                end_l_s,
            ],
            result,
        ])
    }
}

/// Translate a while statement
pub(crate) fn while_(span: Span, cond: TExpr, body: TExpr, end_l: Label) -> TExpr {
    let cond_l = Label::named("test");
    let body_l = Label::named("body");
    let cond = cond.un_cx()(body_l.clone(), end_l.clone());
    let body_span = body.span();
    let body = body.un_nx();
    let cond_l_s = IR![s label, span, cond_l.clone()];
    let body_l_s = IR![s label, span, body_l];
    let end_l_s = IR![s label, span, end_l];

    TExpr::Nx(IR![s seq, span,
        // test:
        //      cmp cond -> body | end
        // body:
        //      body
        //      jmp cond
        // end:
        cond_l_s,
        cond,
        body_l_s,
        body,
        IR![s jmpl, body_span, cond_l],
        end_l_s,
    ])
}

/// Translate a for statement
pub(crate) fn for_(
    span: Span,
    iterator: TExpr,
    start: TExpr,
    end: TExpr,
    body: TExpr,
    end_l: Label,
) -> TExpr {
    let cond_l = Label::named("test");
    let body_l = Label::named("body");
    let iterator_ex = iterator.un_ex();

    TExpr::Nx(IR![s seq, span,
        // mov i, start
        IR![s move, start.span(), iterator_ex.clone(), start.un_ex()],
        // jmp test
        IR![s jmpl, span, cond_l.clone()],
        // body:
        IR![s label, body.span(), body_l.clone()],
        IR![s move, span, iterator_ex.clone(),
            IR![e binop, span,
                op![+],
                iterator_ex.clone(),
                IR![e const, span, 1],
            ],
        ],
        // body
        body.un_nx(),
        // test:
        IR![s label, end.span(), cond_l],
        // cmp i < end -> body | end
        IR![s cjmp, end.span(),
            op![<],
            iterator_ex,
            end.un_ex(),
            body_l,
            end_l.clone(),
        ],
        // end:
        IR![s label, span, end_l],
    ])
}

/// Translate a call expression. It also calculates the static link to pass to the function.
pub(crate) fn call<F: Frame>(
    span: Span,
    is_primitive: bool,
    name: Label,
    arguments: Vec<TExpr>,
    fn_level: &level::Level<F>,
    mut current_level: &level::Level<F>,
) -> TExpr {
    // The static link by default is the frame pointer.
    let mut args = if is_primitive {
        Vec::with_capacity(arguments.len())
    } else {
        let mut sl = IR![e temp, span, F::fp()];
        // When calling a function defined on the same 'let', the function will
        // actually have a higher level, so we must get its parent.
        // When a function calls itself, they have the same level, however we have
        // to pass the static link to the parent function, so we have to get
        // the parent's level too.
        let fn_level = fn_level
            .parent
            .as_ref()
            .expect("ICE: No function should be defined in the outermost level");
        while current_level != &**fn_level {
            // Fetch the current level's sl
            sl = F::expr(
                current_level
                    .frame
                    .borrow()
                    .formals()
                    .get(0)
                    .expect("ICE: Should have a static link"),
                sl,
            );

            current_level = current_level
                .parent
                .as_ref()
                .expect("ICE: A level should have been found");
        }

        let mut args = Vec::with_capacity(arguments.len() + 1);
        args.push(sl);
        args
    };

    for a in arguments {
        args.push(a.un_ex());
    }

    TExpr::Ex(IR![e call, span,
        IR![e name, span, name],
        args,
    ])
}

pub(crate) fn fn_<F: Frame>(
    span: Span,
    fragments: &mut Vec<Fragment<F>>,
    level: &Level<F>,
    body: TExpr,
) {
    let rv = IR![e temp, span, F::rv()];
    // mov rv, body
    let body = IR![s move, span, rv, body.un_ex()];
    let body = level.frame.borrow().proc_entry_exit_1(body);

    fragments.push(Fragment::Proc {
        body,
        frame: Rc::clone(&level.frame),
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::expect;
    use tig_common::SmolStr;

    use crate::frame::amd64::Amd64Frame;

    #[test]
    fn test_accessing_a_non_escaping_local() {
        let mut root = Level::<Amd64Frame>::outermost();
        let var_a = root.alloc_local(false);

        expect![[r#"
            0..1: Temp(0)
        "#]]
        .assert_debug_eq(&simple_var(Span::new(0, 1), &var_a, &root).un_ex());
    }

    #[test]
    fn test_accessing_an_in_frame_local() {
        let mut root = Level::<Amd64Frame>::outermost();
        let var_a = root.alloc_local(true);

        expect![[r#"
            0..1: Mem
              0..1: Expr
                0..1: BinOp(-)
                  0..1: Left
                    0..1: Temp(fp)
                  0..1: Right
                    0..1: Const(8)
        "#]]
        .assert_debug_eq(&simple_var(Span::new(0, 1), &var_a, &root).un_ex());
    }

    #[test]
    fn test_accessing_a_variable_on_parent_frame() {
        let mut root = Level::<Amd64Frame>::outermost();
        let var_a = root.alloc_local(true);
        let current_level = root.new_level(Label::new(), vec![true]);

        // mov r0, [fp - 8] // Load static link
        // mov r0, [r0 - 8] // Load variable form parent's frame
        expect![[r#"
            0..1: Mem
              0..1: Expr
                0..1: BinOp(-)
                  0..1: Left
                    0..1: Mem
                      0..1: Expr
                        0..1: BinOp(-)
                          0..1: Left
                            0..1: Temp(fp)
                          0..1: Right
                            0..1: Const(8)
                  0..1: Right
                    0..1: Const(8)
        "#]]
        .assert_debug_eq(&simple_var(Span::new(0, 1), &var_a, &current_level).un_ex());
    }

    #[test]
    fn test_accessing_a_variable_on_grandfather_frame() {
        let mut root = Level::<Amd64Frame>::outermost();
        root.alloc_local(true);
        let var_a = root.alloc_local(true);
        let current_level = root.new_level(Label::new(), vec![true]);
        let current_level = current_level.new_level(Label::new(), vec![true]);

        // mov r0, [fp - 8] // Load static link
        // mov r0, [r0 - 8] // Load parent's frame's static link
        // mov r0, [r0 - 16] // Load variable form grandfathers's frame
        expect![[r#"
            0..1: Mem
              0..1: Expr
                0..1: BinOp(-)
                  0..1: Left
                    0..1: Mem
                      0..1: Expr
                        0..1: BinOp(-)
                          0..1: Left
                            0..1: Mem
                              0..1: Expr
                                0..1: BinOp(-)
                                  0..1: Left
                                    0..1: Temp(fp)
                                  0..1: Right
                                    0..1: Const(8)
                          0..1: Right
                            0..1: Const(8)
                  0..1: Right
                    0..1: Const(16)
        "#]]
        .assert_debug_eq(&simple_var(Span::new(0, 1), &var_a, &current_level).un_ex());
    }

    #[test]
    fn test_string_comparison() {
        let s = Span::new(0, 1);
        let left_string = TExpr::Ex(IR![e name, s,
            Label::raw(SmolStr::new_inline("left"))]);
        let right_string = TExpr::Ex(IR![e name, s,
            Label::raw(SmolStr::new_inline("right"))]);

        expect![[r#"
            0..1: ESeq
              0..1: Stmt
                0..1: Seq
                  0..1: Stmt1
                    0..1: Seq
                      0..1: Stmt1
                        0..1: Seq
                          0..1: Stmt1
                            0..1: Seq
                              0..1: Stmt1
                                0..1: Seq
                                  0..1: Stmt1
                                    0..1: Move
                                      0..1: Destination
                                        0..1: Temp(0)
                                      0..1: Source
                                        0..1: Const(1)
                                  0..1: Stmt2
                                    0..1: CJmp(=) -> cmp_end0 | cmp_negate1
                                      0..1: Left
                                        0..1: Call
                                          0..1: Function
                                            0..1: Name(stringCompare)
                                          0..1: Arguments
                                            0..1: Name(left)
                                            0..1: Name(right)
                                      0..1: Right
                                        0..1: Const(0)
                              0..1: Stmt2
                                0..1: Label(cmp_negate1)
                          0..1: Stmt2
                            0..1: Move
                              0..1: Destination
                                0..1: Temp(0)
                              0..1: Source
                                0..1: Const(0)
                      0..1: Stmt2
                        0..1: Jump([cmp_end0])
                          0..1: Target
                            0..1: Name(cmp_end0)
                  0..1: Stmt2
                    0..1: Label(cmp_end0)
              0..1: Expr
                0..1: Temp(0)
        "#]]
        .assert_debug_eq(
            &string_cmp::<Amd64Frame>(s, op![=], left_string.clone(), right_string.clone()).un_ex(),
        );

        expect![[r#"
            0..1: ESeq
              0..1: Stmt
                0..1: Seq
                  0..1: Stmt1
                    0..1: Seq
                      0..1: Stmt1
                        0..1: Seq
                          0..1: Stmt1
                            0..1: Seq
                              0..1: Stmt1
                                0..1: Seq
                                  0..1: Stmt1
                                    0..1: Move
                                      0..1: Destination
                                        0..1: Temp(1)
                                      0..1: Source
                                        0..1: Const(1)
                                  0..1: Stmt2
                                    0..1: CJmp(<>) -> cmp_end2 | cmp_negate3
                                      0..1: Left
                                        0..1: Call
                                          0..1: Function
                                            0..1: Name(stringCompare)
                                          0..1: Arguments
                                            0..1: Name(left)
                                            0..1: Name(right)
                                      0..1: Right
                                        0..1: Const(0)
                              0..1: Stmt2
                                0..1: Label(cmp_negate3)
                          0..1: Stmt2
                            0..1: Move
                              0..1: Destination
                                0..1: Temp(1)
                              0..1: Source
                                0..1: Const(0)
                      0..1: Stmt2
                        0..1: Jump([cmp_end2])
                          0..1: Target
                            0..1: Name(cmp_end2)
                  0..1: Stmt2
                    0..1: Label(cmp_end2)
              0..1: Expr
                0..1: Temp(1)
        "#]]
        .assert_debug_eq(
            &string_cmp::<Amd64Frame>(s, op![<>], left_string.clone(), right_string.clone())
                .un_ex(),
        );

        expect![[r#"
            0..1: ESeq
              0..1: Stmt
                0..1: Seq
                  0..1: Stmt1
                    0..1: Seq
                      0..1: Stmt1
                        0..1: Seq
                          0..1: Stmt1
                            0..1: Seq
                              0..1: Stmt1
                                0..1: Seq
                                  0..1: Stmt1
                                    0..1: Move
                                      0..1: Destination
                                        0..1: Temp(2)
                                      0..1: Source
                                        0..1: Const(1)
                                  0..1: Stmt2
                                    0..1: CJmp(<) -> cmp_end4 | cmp_negate5
                                      0..1: Left
                                        0..1: Call
                                          0..1: Function
                                            0..1: Name(stringCompare)
                                          0..1: Arguments
                                            0..1: Name(left)
                                            0..1: Name(right)
                                      0..1: Right
                                        0..1: Const(0)
                              0..1: Stmt2
                                0..1: Label(cmp_negate5)
                          0..1: Stmt2
                            0..1: Move
                              0..1: Destination
                                0..1: Temp(2)
                              0..1: Source
                                0..1: Const(0)
                      0..1: Stmt2
                        0..1: Jump([cmp_end4])
                          0..1: Target
                            0..1: Name(cmp_end4)
                  0..1: Stmt2
                    0..1: Label(cmp_end4)
              0..1: Expr
                0..1: Temp(2)
        "#]]
        .assert_debug_eq(
            &string_cmp::<Amd64Frame>(s, op![<], left_string.clone(), right_string.clone()).un_ex(),
        );

        expect![[r#"
            0..1: ESeq
              0..1: Stmt
                0..1: Seq
                  0..1: Stmt1
                    0..1: Seq
                      0..1: Stmt1
                        0..1: Seq
                          0..1: Stmt1
                            0..1: Seq
                              0..1: Stmt1
                                0..1: Seq
                                  0..1: Stmt1
                                    0..1: Move
                                      0..1: Destination
                                        0..1: Temp(3)
                                      0..1: Source
                                        0..1: Const(1)
                                  0..1: Stmt2
                                    0..1: CJmp(>=) -> cmp_end6 | cmp_negate7
                                      0..1: Left
                                        0..1: Call
                                          0..1: Function
                                            0..1: Name(stringCompare)
                                          0..1: Arguments
                                            0..1: Name(left)
                                            0..1: Name(right)
                                      0..1: Right
                                        0..1: Const(0)
                              0..1: Stmt2
                                0..1: Label(cmp_negate7)
                          0..1: Stmt2
                            0..1: Move
                              0..1: Destination
                                0..1: Temp(3)
                              0..1: Source
                                0..1: Const(0)
                      0..1: Stmt2
                        0..1: Jump([cmp_end6])
                          0..1: Target
                            0..1: Name(cmp_end6)
                  0..1: Stmt2
                    0..1: Label(cmp_end6)
              0..1: Expr
                0..1: Temp(3)
        "#]]
        .assert_debug_eq(
            &string_cmp::<Amd64Frame>(s, op![>=], left_string.clone(), right_string.clone())
                .un_ex(),
        );
    }
}
