use std::rc::Rc;

use tig_common::{temp::Label, Span};
use tig_error::SpannedError;
use tig_syntax::ast;

use crate::{ir, op, translate::TExpr, ExpTy, Frame, Type};

use super::{TEnv, Translator, VEnv, ValEntry};
use crate::translate as tx;

/// Pushes a SpannedError to self.errors.
macro_rules! E {
    ($translator:expr, $span:expr, $($error:expr),+ $(,)?) => {
        $translator.errors.push(SpannedError::new(
            format!($($error),+),
            $span,
        ))
    };
}

impl<F: Frame> Translator<F> {
    /// Translates an expression into an `ExpTy`.
    pub(super) fn translate_expr(&mut self, expr: ast::Expr, venv: &VEnv<F>, tenv: &TEnv) -> ExpTy {
        let ast::Expr {
            span,
            kind: expr_kind,
        } = expr;
        match expr_kind {
            ast::ExprKind::Nil => ExpTy {
                exp: tx::nil(span),
                ty: Type::nil(),
            },

            ast::ExprKind::Integer(n) => ExpTy {
                exp: tx::int(span, n),
                ty: Type::int(),
            },

            ast::ExprKind::String(s) => ExpTy {
                exp: tx::string::<F>(span, s, &mut self.fragments),
                ty: Type::string(),
            },

            ast::ExprKind::Array {
                type_id,
                size,
                initial_value,
            } => self.translate_array(type_id, *size, *initial_value, venv, tenv),

            ast::ExprKind::Record { type_id, fields } => {
                self.translate_record(type_id, fields, venv, tenv)
            }

            ast::ExprKind::LValue(lvalue) => self.translate_var(lvalue, venv, tenv),
            ast::ExprKind::Call { func, arguments } => {
                self.translate_call(span, func, arguments, venv, tenv)
            }
            ast::ExprKind::Negate(expr) => {
                let espan = expr.span;
                let expr = self.translate_expr(*expr, venv, tenv);
                self.expect_int(&expr, espan, tenv);

                ExpTy {
                    exp: tx::negate(span, expr.exp),
                    ty: Type::int(),
                }
            }

            ast::ExprKind::BinOp { op, left, right } => {
                self.translate_binary_op(op, *left, *right, venv, tenv)
            }

            ast::ExprKind::Exprs(exprs) => {
                let mut exprs = exprs.into_iter();
                let mut expty = match exprs.next() {
                    Some(e) => self.translate_expr(e, venv, tenv),
                    // HACK: empty parenthesis is the unit type
                    None => {
                        return ExpTy {
                            exp: tx::unit(span),
                            ty: Type::unit(),
                        }
                    }
                };

                for exp in exprs {
                    let e = self.translate_expr(exp, venv, tenv);
                    expty = ExpTy {
                        exp: tx::eseq(span, expty.exp, e.exp),
                        ty: e.ty,
                    }
                }

                expty
            }

            ast::ExprKind::Assign {
                destination,
                source,
            } => {
                let destination_span = destination.span();
                let destionation_ty = self.translate_var(destination, venv, tenv);
                let source_span = source.span;
                let source_ty = self.translate_expr(*source, venv, tenv);

                if !self.cmp_ty(
                    &destionation_ty.ty,
                    destination_span,
                    &source_ty.ty,
                    source_span,
                    tenv,
                ) {
                    E!(
                        self,
                        source_span,
                        "Expected type '{}', got '{}'",
                        destionation_ty.ty,
                        source_ty.ty,
                    );
                }

                ExpTy {
                    exp: tx::assign(span, destionation_ty.exp, source_ty.exp),
                    ty: Type::unit(),
                }
            }

            ast::ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => self.translate_if(*cond, *then_branch, else_branch, venv, tenv),

            ast::ExprKind::While { cond, body } => self.translate_while(*cond, *body, venv, tenv),

            ast::ExprKind::For {
                iterator,
                escape,
                start,
                end,
                body,
            } => {
                let start_span = start.span;
                let start_ty = self.translate_expr(*start, venv, tenv);
                self.expect_int(&start_ty, start_span, tenv);

                let end_span = end.span;
                let end_ty = self.translate_expr(*end, venv, tenv);
                self.expect_int(&end_ty, end_span, tenv);

                let mut venv = venv.new_child();
                let access = self.current_level.alloc_local(escape);
                venv.enter(
                    iterator.value,
                    ValEntry::Variable {
                        access: access.clone(),
                        ty: Type::int(),
                    },
                );

                self.loop_stack.push(Label::named("for_end"));
                let body_span = body.span;
                let body_ty = self.translate_expr(*body, &venv, tenv);
                self.expect_unit(&body_ty, body_span, tenv);
                let end_l = self
                    .loop_stack
                    .pop()
                    .expect("ICE: The loop stack got corrupted");

                ExpTy {
                    exp: tx::for_(
                        span,
                        tx::simple_var(iterator.span, &access, &self.current_level),
                        start_ty.exp,
                        end_ty.exp,
                        body_ty.exp,
                        end_l,
                    ),
                    ty: Type::unit(),
                }
            }

            ast::ExprKind::Break => {
                let end_l = match self.loop_stack.last() {
                    Some(l) => tx::break_(span, l),
                    None => {
                        E!(self, span, "Cannot break outside a loop",);
                        TExpr::hole()
                    }
                };
                ExpTy {
                    exp: end_l,
                    ty: Type::unit(),
                }
            }

            ast::ExprKind::Let { decs, expr } => {
                let (venv, tenv, stmts) = self.translate_decs(decs, venv, tenv);
                let body_ty = self.translate_expr(*expr, &venv, &tenv);

                ExpTy {
                    exp: tx::let_(span, stmts, body_ty.exp),
                    ty: body_ty.ty,
                }
            }
        }
    }

    fn translate_binary_op(
        &mut self,
        op: ast::BinOp,
        left: ast::Expr,
        right: ast::Expr,
        venv: &VEnv<F>,
        tenv: &TEnv,
    ) -> ExpTy {
        let lspan = left.span;
        let rspan = right.span;
        let left = self.translate_expr(left, venv, tenv);
        let right = self.translate_expr(right, venv, tenv);

        use ast::BinOp::*;

        match op {
            Add | Subtract | Multiply | Divide | And | Or => {
                self.expect_int(&left, lspan, tenv);
                self.expect_int(&right, rspan, tenv);
            }
            Gt | Lt | Gte | Lte => match (&*left.ty, &*right.ty) {
                (Type::Int, Type::Int) => {}
                (Type::String, Type::String) => {
                    return ExpTy {
                        exp: tx::string_cmp::<F>(
                            lspan.extend(rspan),
                            match op {
                                Gt => op![>],
                                Lt => op![<],
                                Gte => op![>=],
                                _ => op![<=],
                            },
                            left.exp,
                            right.exp,
                        ),
                        ty: Type::int(),
                    };
                }
                (Type::Int, o) => {
                    E!(self, rspan, "Expected an int, got '{}'", o,);
                }
                (o, Type::Int) => {
                    E!(self, lspan, "Expected an int, got '{}'", o,);
                }
                (Type::String, o) => {
                    E!(self, rspan, "Expected a string, got '{}'", o,);
                }
                (o, Type::String) => {
                    E!(self, lspan, "Expected a string, got '{}'", o,);
                }
                (_, _) => {
                    E!(
                        self,
                        lspan.extend(rspan),
                        "Only the types int, and string can be ordered",
                    );
                }
            },
            Eq | Neq => match (&*left.ty, &*right.ty) {
                (Type::Nil, Type::Nil) => {
                    E!(self, lspan.extend(rspan), "Nil cannot be compared with nil");
                }
                (Type::String, Type::String) => {
                    return ExpTy {
                        exp: tx::string_cmp::<F>(
                            lspan.extend(rspan),
                            if op == Eq { op![=] } else { op![<>] },
                            left.exp,
                            right.exp,
                        ),
                        ty: Type::int(),
                    }
                }
                _ => {
                    if !self.cmp_ty(&left.ty, lspan, &right.ty, rspan, tenv) {
                        E!(
                            self,
                            lspan.extend(rspan),
                            "Cannot compare type '{}' with '{}'",
                            left.ty,
                            right.ty
                        );
                    }
                }
            },
        };

        ExpTy {
            exp: tx::binary_op(lspan.extend(rspan), op, left.exp, right.exp),
            ty: Type::int(),
        }
    }

    fn translate_call(
        &mut self,
        span: Span,
        func: ast::Ident,
        arguments: Vec<ast::Expr>,
        venv: &VEnv<F>,
        tenv: &TEnv,
    ) -> ExpTy {
        let (formals, result, level, label, is_primitive) = match venv.look(&func.value) {
            Some(f) => match f {
                ValEntry::Variable { ty, .. } => {
                    E!(self, func.span, "Expected a function, got '{}'", ty,);
                    return ExpTy {
                        exp: TExpr::hole(),
                        ty: Type::hole(),
                    };
                }
                ValEntry::Function {
                    is_primitive,
                    level,
                    label,
                    formals,
                    result,
                } => (formals, result, level, label, is_primitive),
            },
            None => {
                E!(self, func.span, "Undefined function '{}'", func.value,);
                return ExpTy {
                    exp: TExpr::hole(),
                    ty: Type::hole(),
                };
            }
        };

        let formals_len = formals.len();
        let arguments_len = arguments.len();
        let mut arguments_exp = vec![];
        for (formal, arg) in formals.iter().zip(arguments.into_iter()) {
            let arg_span = arg.span;
            let arg_ty = self.translate_expr(arg, venv, tenv);

            if formal != &self.actual_ty(&arg_ty.ty, arg_span, tenv) {
                E!(
                    self,
                    arg_span,
                    "Expected type '{}', got '{}'",
                    formal,
                    arg_ty.ty,
                );
            }
            arguments_exp.push(arg_ty.exp);
        }

        if formals_len != arguments_len {
            E!(
                self,
                span,
                "Function '{}' expects {} argument{}, {} given",
                func.value,
                formals_len,
                if formals_len == 1 { "" } else { "s" },
                arguments_len,
            );
        }

        ExpTy {
            exp: tx::call(
                span,
                *is_primitive,
                label.clone(),
                arguments_exp,
                level,
                &self.current_level,
            ),
            ty: Rc::clone(result),
        }
    }

    fn translate_array(
        &mut self,
        type_id: ast::Ident,
        size: ast::Expr,
        initial_value: ast::Expr,
        venv: &VEnv<F>,
        tenv: &TEnv,
    ) -> ExpTy {
        let array_ty = self.resolve_ty(&type_id.value, type_id.span, tenv, true);

        match &*array_ty {
            Type::Array { ty, .. } => {
                let size_span = size.span;
                let size_ty = self.translate_expr(size, venv, tenv);
                self.expect_int(&size_ty, size_span, tenv);
                let initial_value_span = initial_value.span;
                let initial_value_ty = self.translate_expr(initial_value, venv, tenv);

                // Unfortunately by this point we don't have a span for the array type.
                // TODO: Add a span to it?
                if !self.cmp_ty(
                    ty,
                    initial_value_span,
                    &initial_value_ty.ty,
                    initial_value_span,
                    tenv,
                ) {
                    log::trace!(
                        "Expected type of array '{}' does not match with actual type from initial value '{}'",
                        ty,
                        initial_value_ty.ty,
                    );
                    E!(
                        self,
                        initial_value_span,
                        "Expected type '{}', got '{}'",
                        ty,
                        initial_value_ty.ty
                    );
                }

                ExpTy {
                    exp: tx::array::<F>(
                        type_id.span.extend(initial_value_span),
                        size_ty.exp,
                        initial_value_ty.exp,
                    ),
                    ty: array_ty,
                }
            }
            Type::Hole => ExpTy {
                exp: TExpr::hole(),
                ty: array_ty,
            },
            _ => {
                E!(
                    self,
                    type_id.span,
                    "Expected an array type, got '{}'",
                    array_ty
                );
                ExpTy {
                    exp: TExpr::hole(),
                    ty: array_ty,
                }
            }
        }
    }

    fn translate_record(
        &mut self,
        ast::Ident {
            value: ty_id_value,
            span: ty_id_span,
        }: ast::Ident,
        fields: Vec<ast::RecordField>,
        venv: &VEnv<F>,
        tenv: &TEnv,
    ) -> ExpTy {
        let found_ty = match tenv.look(&ty_id_value) {
            // A record has the form type-id { fields }
            // First lookup the type-id to make sure it is a record,
            // and get the expected fields.
            Some(found_ty) => found_ty,
            None => {
                E!(self, ty_id_span, "Undefined type '{}'", ty_id_value);
                return ExpTy {
                    exp: TExpr::hole(),
                    ty: Type::hole(),
                };
            }
        };

        let ty_r = self.actual_ty(found_ty, ty_id_span, tenv);
        match &*ty_r {
            Type::Record {
                fields: ty_fields, ..
            } => {
                // PERF: Complain first about the extra fields by iterating
                // over the record literal. Then iterate over the record definition
                // to complain about the missing fields, and translate the fields
                // in the same order as in the record definition, then only send
                // the translated fields to tx::record, since the fields will already
                // be ordered.
                //
                // Look for missing fields, the next step consumes the
                // fields iterator, so we have to do this first.
                'field_type_iter: for ty_f in ty_fields {
                    for r_f in &fields {
                        if ty_f.name.value == r_f.field.value {
                            continue 'field_type_iter;
                        }
                    }

                    E!(
                        self,
                        ty_id_span,
                        "Missing field {} for record {}",
                        ty_f.name.value,
                        ty_r
                    );
                }

                let record_span =
                    ty_id_span.extend(fields.last().map(|f| f.value.span).unwrap_or(ty_id_span));
                let mut expr_fields = Vec::with_capacity(fields.len());
                // Iterate over every record literal field.
                'field_literal_iter: for r_f in fields {
                    // Find the corresponding field in the record type.
                    for ty_f in ty_fields {
                        if r_f.field.value == ty_f.name.value {
                            let r_exp_span = r_f.value.span;
                            let r_exp = self.translate_expr(r_f.value, venv, tenv);
                            // The record literal type does not match
                            // the expected type.
                            if !self.cmp_ty(&r_exp.ty, r_exp_span, &ty_f.ty, ty_f.name.span, tenv) {
                                E!(
                                    self,
                                    r_exp_span,
                                    "Expected type '{}', got '{}'",
                                    ty_f.ty,
                                    r_exp.ty
                                );
                            }
                            expr_fields.push(r_exp.exp);
                            // Continue with the next record literal field.
                            continue 'field_literal_iter;
                        }
                    }

                    // The field in the record literal does not exist in the
                    // record type.
                    E!(
                        self,
                        r_f.field.span,
                        "Field '{}' does not exist in type {}",
                        r_f.field.value,
                        ty_r
                    );
                }

                // The record literal matches the expected record, or
                // all errors have been generated.
                ExpTy {
                    exp: tx::record::<F>(record_span, ty_fields, expr_fields),
                    ty: ty_r,
                }
            }
            Type::Hole => ExpTy {
                exp: TExpr::hole(),
                ty: Type::hole(),
            },
            _ => {
                E!(
                    self,
                    ty_id_span,
                    "Expected a record type, got '{}'",
                    found_ty
                );
                ExpTy {
                    exp: TExpr::hole(),
                    ty: Type::hole(),
                }
            }
        }
    }

    fn translate_if(
        &mut self,
        cond: ast::Expr,
        then_branch: ast::Expr,
        else_branch: Option<Box<ast::Expr>>,
        venv: &VEnv<F>,
        tenv: &TEnv,
    ) -> ExpTy {
        let cond_span = cond.span;
        let cond_ty = self.translate_expr(cond, venv, tenv);
        self.expect_int(&cond_ty, cond_span, tenv);

        let then_branch_span = then_branch.span;
        let then_branch_ty = self.translate_expr(then_branch, venv, tenv);

        let (else_branch_span, else_branch_ty) = match else_branch {
            Some(else_branch) => {
                let else_branch_span = else_branch.span;
                let else_branch_ty = self.translate_expr(*else_branch, venv, tenv);

                if self.cmp_ty(
                    &else_branch_ty.ty,
                    else_branch_span,
                    &then_branch_ty.ty,
                    then_branch_span,
                    tenv,
                ) {
                    (else_branch_span, else_branch_ty)
                } else {
                    E!(
                        self,
                        then_branch_span.extend(else_branch_span),
                        "Then and else branch return types don't match - '{}' and '{}' respectively",
                        then_branch_ty.ty,
                        else_branch_ty.ty,
                    );
                    (
                        else_branch_span,
                        ExpTy {
                            exp: TExpr::hole(),
                            ty: Type::hole(),
                        },
                    )
                }
            }
            None => match &*then_branch_ty.ty {
                Type::Unit | Type::Hole => (
                    then_branch_span,
                    ExpTy {
                        exp: tx::unit(cond_span.extend(then_branch_span)),
                        ty: Rc::clone(&then_branch_ty.ty),
                    },
                ),
                _ => {
                    E!(
                        self,
                        then_branch_span,
                        "Expected then branch to return unit, as it does not have an else branch, got '{}'",
                        then_branch_ty.ty
                      );
                    (
                        then_branch_span,
                        ExpTy {
                            exp: TExpr::hole(),
                            ty: Type::hole(),
                        },
                    )
                }
            },
        };

        let ty = then_branch_ty.ty;
        ExpTy {
            exp: tx::if_(
                cond_span.extend(else_branch_span),
                cond_ty.exp,
                then_branch_ty.exp,
                else_branch_ty.exp,
                ty.is_unit(), // Ignore result
            ),
            ty,
        }
    }

    fn translate_while(
        &mut self,
        cond: ast::Expr,
        body: ast::Expr,
        venv: &VEnv<F>,
        tenv: &TEnv,
    ) -> ExpTy {
        let cond_span = cond.span;
        let cond_ty = self.translate_expr(cond, venv, tenv);
        self.expect_int(&cond_ty, cond_span, tenv);

        self.loop_stack.push(Label::named("while_end"));
        let body_span = body.span;
        let body_ty = self.translate_expr(body, venv, tenv);
        self.expect_unit(&body_ty, body_span, tenv);
        let end_l = self
            .loop_stack
            .pop()
            .expect("ICE: The loop stack got corrupted");

        ExpTy {
            exp: tx::while_(cond_span.extend(body_span), cond_ty.exp, body_ty.exp, end_l),
            ty: Type::unit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use expect_test::{expect, Expect};

    use crate::{frame::amd64::Amd64Frame, translate_program};

    use tig_syntax::parse_str;

    //fn check(program: &str, expected: Expect) {
    //    let (_, p) = parse_str(program);
    //    assert_eq!(p.errors, vec![]);
    //    let result = translate_program::<Amd64Frame>(p.program.expect("Should have compiled"));
    //    assert_eq!(result.errors, vec![]);
    //    expected.assert_debug_eq(&result.expty);
    //}

    fn check_fragments(program: &str, fragments: Vec<Expect>) {
        let (_, p) = parse_str(program);
        assert_eq!(p.errors, vec![]);
        let result = translate_program::<Amd64Frame>(p.program.expect("Should have compiled"));
        assert_eq!(result.errors, vec![]);
        let rf_len = result.fragments.len();
        let ef_len = fragments.len();
        for (f, e) in result.fragments.into_iter().zip(fragments.into_iter()) {
            e.assert_debug_eq(&f);
        }
        assert_eq!(rf_len, ef_len);
    }

    fn check_err(program: &str, expected: Vec<Expect>) {
        let (_, p) = parse_str(program);
        assert_eq!(p.errors, vec![]);
        let result = translate_program::<Amd64Frame>(p.program.expect("Should have compiled"));
        for (r, e) in result.errors.iter().zip(expected.iter()) {
            e.assert_eq(&format!("{}", r));
        }
        assert_eq!(result.errors.len(), expected.len());
    }

    #[test]
    fn test_tyc_integer() {
        check_fragments(
            "3",
            vec![expect![[r#"
                    0..1: Procedure
                      Frame(_main) - 0
                      0..1: Move
                        0..1: Destination
                          0..1: Temp(rv)
                        0..1: Source
                          0..1: Const(3)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_nil() {
        check_fragments(
            "nil",
            vec![expect![[r#"
                    0..3: Procedure
                      Frame(_main) - 0
                      0..3: Move
                        0..3: Destination
                          0..3: Temp(rv)
                        0..3: Source
                          0..3: Const(0)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_string() {
        check_fragments(
            "\"Hi\"",
            vec![
                expect![[r#"
                    String(label0)
                      "Hi"
                "#]],
                expect![[r#"
                    0..4: Procedure
                      Frame(_main) - 0
                      0..4: Move
                        0..4: Destination
                          0..4: Temp(rv)
                        0..4: Source
                          0..4: Name(label0)
                "#]],
            ],
        );
    }

    #[test]
    fn test_tyc_unit_type() {
        check_fragments(
            "let var a := () in a end",
            vec![expect![[r#"
                    0..24: Procedure
                      Frame(_main) - 0
                      0..24: Move
                        0..24: Destination
                          0..24: Temp(rv)
                        0..24: Source
                          0..24: ESeq
                            4..15: Stmt
                              4..15: Move
                                4..15: Destination
                                  4..15: Temp(0)
                                13..15: Source
                                  13..15: Const(0)
                            19..20: Expr
                              19..20: Temp(0)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_string_fragments() {
        check_fragments(
            r#"
                ("Hello, World!";
                "Hi")
            "#,
            vec![
                expect![[r#"
                    String(label0)
                      "Hello, World!"
                "#]],
                expect![[r#"
                    String(label1)
                      "Hi"
                "#]],
                expect![[r#"
                    17..56: Procedure
                      Frame(_main) - 0
                      17..56: Move
                        17..56: Destination
                          17..56: Temp(rv)
                        17..56: Source
                          17..56: ESeq
                            18..33: Stmt
                              18..33: StmtExpr
                                18..33: Name(label0)
                            51..55: Expr
                              51..55: Name(label1)
                "#]],
            ],
        );
    }

    #[test]
    fn test_tyc_binary_op() {
        check_fragments(
            "2 > 1",
            vec![expect![[r#"
                    0..5: Procedure
                      Frame(_main) - 0
                      0..5: Move
                        0..5: Destination
                          0..5: Temp(rv)
                        0..5: Source
                          0..5: ESeq
                            0..5: Stmt
                              0..5: Seq
                                0..5: Stmt1
                                  0..5: Seq
                                    0..5: Stmt1
                                      0..5: Seq
                                        0..5: Stmt1
                                          0..5: Seq
                                            0..5: Stmt1
                                              0..5: Seq
                                                0..5: Stmt1
                                                  0..5: Move
                                                    0..5: Destination
                                                      0..5: Temp(0)
                                                    0..5: Source
                                                      0..5: Const(1)
                                                0..5: Stmt2
                                                  0..5: CJmp(>) -> true0 | false1
                                                    0..1: Left
                                                      0..1: Const(2)
                                                    4..5: Right
                                                      4..5: Const(1)
                                            0..5: Stmt2
                                              0..5: Jump([false1])
                                                0..5: Target
                                                  0..5: Name(false1)
                                        0..5: Stmt2
                                          0..5: Move
                                            0..5: Destination
                                              0..5: Temp(0)
                                            0..5: Source
                                              0..5: Const(0)
                                    0..5: Stmt2
                                      0..5: Jump([true0])
                                        0..5: Target
                                          0..5: Name(true0)
                                0..5: Stmt2
                                  0..5: Label(true0)
                            0..5: Expr
                              0..5: Temp(0)
                "#]]],
        );

        check_fragments(
            "2 > 1 & 0 = 0",
            vec![expect![[r#"
                    0..13: Procedure
                      Frame(_main) - 0
                      0..13: Move
                        0..13: Destination
                          0..13: Temp(rv)
                        0..13: Source
                          0..13: ESeq
                            0..13: Stmt
                              0..13: Seq
                                0..13: Stmt1
                                  0..13: Seq
                                    0..13: Stmt1
                                      0..13: Seq
                                        0..13: Stmt1
                                          0..13: Seq
                                            0..13: Stmt1
                                              0..13: Seq
                                                0..13: Stmt1
                                                  0..13: Move
                                                    0..13: Destination
                                                      0..13: Temp(1)
                                                    0..13: Source
                                                      0..13: Const(1)
                                                0..13: Stmt2
                                                  0..13: Seq
                                                    0..13: Stmt1
                                                      0..13: Seq
                                                        0..5: Stmt1
                                                          0..5: CJmp(>) -> second_op4 | false3
                                                            0..1: Left
                                                              0..1: Const(2)
                                                            4..5: Right
                                                              4..5: Const(1)
                                                        0..13: Stmt2
                                                          0..13: Label(second_op4)
                                                    8..13: Stmt2
                                                      8..13: CJmp(=) -> true2 | false3
                                                        8..9: Left
                                                          8..9: Const(0)
                                                        12..13: Right
                                                          12..13: Const(0)
                                            0..13: Stmt2
                                              0..13: Jump([false3])
                                                0..13: Target
                                                  0..13: Name(false3)
                                        0..13: Stmt2
                                          0..13: Move
                                            0..13: Destination
                                              0..13: Temp(1)
                                            0..13: Source
                                              0..13: Const(0)
                                    0..13: Stmt2
                                      0..13: Jump([true2])
                                        0..13: Target
                                          0..13: Name(true2)
                                0..13: Stmt2
                                  0..13: Label(true2)
                            0..13: Expr
                              0..13: Temp(1)
                "#]]],
        );

        check_fragments(
            "1 <> 2 | 4 > 2",
            vec![expect![[r#"
                    0..14: Procedure
                      Frame(_main) - 0
                      0..14: Move
                        0..14: Destination
                          0..14: Temp(rv)
                        0..14: Source
                          0..14: ESeq
                            0..14: Stmt
                              0..14: Seq
                                0..14: Stmt1
                                  0..14: Seq
                                    0..14: Stmt1
                                      0..14: Seq
                                        0..14: Stmt1
                                          0..14: Seq
                                            0..14: Stmt1
                                              0..14: Seq
                                                0..14: Stmt1
                                                  0..14: Move
                                                    0..14: Destination
                                                      0..14: Temp(2)
                                                    0..14: Source
                                                      0..14: Const(1)
                                                0..14: Stmt2
                                                  0..14: Seq
                                                    0..14: Stmt1
                                                      0..14: Seq
                                                        0..6: Stmt1
                                                          0..6: CJmp(<>) -> true5 | second_op7
                                                            0..1: Left
                                                              0..1: Const(1)
                                                            5..6: Right
                                                              5..6: Const(2)
                                                        0..14: Stmt2
                                                          0..14: Label(second_op7)
                                                    9..14: Stmt2
                                                      9..14: CJmp(>) -> true5 | false6
                                                        9..10: Left
                                                          9..10: Const(4)
                                                        13..14: Right
                                                          13..14: Const(2)
                                            0..14: Stmt2
                                              0..14: Jump([false6])
                                                0..14: Target
                                                  0..14: Name(false6)
                                        0..14: Stmt2
                                          0..14: Move
                                            0..14: Destination
                                              0..14: Temp(2)
                                            0..14: Source
                                              0..14: Const(0)
                                    0..14: Stmt2
                                      0..14: Jump([true5])
                                        0..14: Target
                                          0..14: Name(true5)
                                0..14: Stmt2
                                  0..14: Label(true5)
                            0..14: Expr
                              0..14: Temp(2)
                "#]]],
        );

        check_fragments(
            "\"hi\" = \"hi\"",
            vec![
                expect![[r#"
                    String(label8)
                      "hi"
                "#]],
                expect![[r#"
                    String(label9)
                      "hi"
                "#]],
                expect![[r#"
                    0..11: Procedure
                      Frame(_main) - 0
                      0..11: Move
                        0..11: Destination
                          0..11: Temp(rv)
                        0..11: Source
                          0..11: ESeq
                            0..11: Stmt
                              0..11: Seq
                                0..11: Stmt1
                                  0..11: Seq
                                    0..11: Stmt1
                                      0..11: Seq
                                        0..11: Stmt1
                                          0..11: Seq
                                            0..11: Stmt1
                                              0..11: Seq
                                                0..11: Stmt1
                                                  0..11: Move
                                                    0..11: Destination
                                                      0..11: Temp(3)
                                                    0..11: Source
                                                      0..11: Const(1)
                                                0..11: Stmt2
                                                  0..11: CJmp(=) -> cmp_end10 | cmp_negate11
                                                    0..11: Left
                                                      0..11: Call
                                                        0..11: Function
                                                          0..11: Name(stringCompare)
                                                        0..11: Arguments
                                                          0..4: Name(label8)
                                                          7..11: Name(label9)
                                                    0..11: Right
                                                      0..11: Const(0)
                                            0..11: Stmt2
                                              0..11: Label(cmp_negate11)
                                        0..11: Stmt2
                                          0..11: Move
                                            0..11: Destination
                                              0..11: Temp(3)
                                            0..11: Source
                                              0..11: Const(0)
                                    0..11: Stmt2
                                      0..11: Jump([cmp_end10])
                                        0..11: Target
                                          0..11: Name(cmp_end10)
                                0..11: Stmt2
                                  0..11: Label(cmp_end10)
                            0..11: Expr
                              0..11: Temp(3)
                "#]],
            ],
        );

        check_fragments(
            "\"hi\" <> \"hi\"",
            vec![
                expect![[r#"
                    String(label12)
                      "hi"
                "#]],
                expect![[r#"
                    String(label13)
                      "hi"
                "#]],
                expect![[r#"
                    0..12: Procedure
                      Frame(_main) - 0
                      0..12: Move
                        0..12: Destination
                          0..12: Temp(rv)
                        0..12: Source
                          0..12: ESeq
                            0..12: Stmt
                              0..12: Seq
                                0..12: Stmt1
                                  0..12: Seq
                                    0..12: Stmt1
                                      0..12: Seq
                                        0..12: Stmt1
                                          0..12: Seq
                                            0..12: Stmt1
                                              0..12: Seq
                                                0..12: Stmt1
                                                  0..12: Move
                                                    0..12: Destination
                                                      0..12: Temp(4)
                                                    0..12: Source
                                                      0..12: Const(1)
                                                0..12: Stmt2
                                                  0..12: CJmp(<>) -> cmp_end14 | cmp_negate15
                                                    0..12: Left
                                                      0..12: Call
                                                        0..12: Function
                                                          0..12: Name(stringCompare)
                                                        0..12: Arguments
                                                          0..4: Name(label12)
                                                          8..12: Name(label13)
                                                    0..12: Right
                                                      0..12: Const(0)
                                            0..12: Stmt2
                                              0..12: Label(cmp_negate15)
                                        0..12: Stmt2
                                          0..12: Move
                                            0..12: Destination
                                              0..12: Temp(4)
                                            0..12: Source
                                              0..12: Const(0)
                                    0..12: Stmt2
                                      0..12: Jump([cmp_end14])
                                        0..12: Target
                                          0..12: Name(cmp_end14)
                                0..12: Stmt2
                                  0..12: Label(cmp_end14)
                            0..12: Expr
                              0..12: Temp(4)
                "#]],
            ],
        );

        // TODO: Check this monstruosity
        check_fragments(
            r#"
            let
                type ints = array of int
                type m = {n: int}
            in
                3 + 1;
                3 * 1;
                (ints [10] of 0) = ints[5] of 1;
                m {n = 2} <> m {n = 3};
                m {n = 2} = nil
            end
            "#,
            vec![expect![[r#"
                    123..273: Procedure
                      Frame(_main) - 0
                      123..273: Move
                        123..273: Destination
                          123..273: Temp(rv)
                        123..273: Source
                          123..273: ESeq
                            123..273: Stmt
                              123..273: StmtExpr
                                123..273: ESeq
                                  123..273: Stmt
                                    123..273: StmtExpr
                                      123..273: ESeq
                                        123..273: Stmt
                                          123..273: StmtExpr
                                            123..273: ESeq
                                              123..128: Stmt
                                                123..128: StmtExpr
                                                  123..128: BinOp(+)
                                                    123..124: Left
                                                      123..124: Const(3)
                                                    127..128: Right
                                                      127..128: Const(1)
                                              146..151: Expr
                                                146..151: BinOp(*)
                                                  146..147: Left
                                                    146..147: Const(3)
                                                  150..151: Right
                                                    150..151: Const(1)
                                        169..200: Expr
                                          169..200: ESeq
                                            169..200: Stmt
                                              169..200: Seq
                                                169..200: Stmt1
                                                  169..200: Seq
                                                    169..200: Stmt1
                                                      169..200: Seq
                                                        169..200: Stmt1
                                                          169..200: Seq
                                                            169..200: Stmt1
                                                              169..200: Seq
                                                                169..200: Stmt1
                                                                  169..200: Move
                                                                    169..200: Destination
                                                                      169..200: Temp(9)
                                                                    169..200: Source
                                                                      169..200: Const(1)
                                                                169..200: Stmt2
                                                                  169..200: CJmp(=) -> true16 | false17
                                                                    170..184: Left
                                                                      170..184: ESeq
                                                                        170..184: Stmt
                                                                          170..184: Seq
                                                                            170..184: Stmt1
                                                                              170..184: Seq
                                                                                170..184: Stmt1
                                                                                  170..184: Move
                                                                                    170..184: Destination
                                                                                      170..184: Temp(6)
                                                                                    170..184: Source
                                                                                      170..184: BinOp(*)
                                                                                        176..178: Left
                                                                                          176..178: Const(10)
                                                                                        170..184: Right
                                                                                          170..184: Const(8)
                                                                                170..184: Stmt2
                                                                                  170..184: Move
                                                                                    170..184: Destination
                                                                                      170..184: Temp(5)
                                                                                    170..184: Source
                                                                                      170..184: Call
                                                                                        170..184: Function
                                                                                          170..184: Name(malloc)
                                                                                        170..184: Arguments
                                                                                          170..184: Temp(6)
                                                                            170..184: Stmt2
                                                                              170..184: StmtExpr
                                                                                170..184: Call
                                                                                  170..184: Function
                                                                                    170..184: Name(initArray)
                                                                                  170..184: Arguments
                                                                                    170..184: Temp(5)
                                                                                    170..184: Temp(6)
                                                                                    183..184: Const(0)
                                                                        170..184: Expr
                                                                          170..184: Temp(5)
                                                                    188..200: Right
                                                                      188..200: ESeq
                                                                        188..200: Stmt
                                                                          188..200: Seq
                                                                            188..200: Stmt1
                                                                              188..200: Seq
                                                                                188..200: Stmt1
                                                                                  188..200: Move
                                                                                    188..200: Destination
                                                                                      188..200: Temp(8)
                                                                                    188..200: Source
                                                                                      188..200: BinOp(*)
                                                                                        193..194: Left
                                                                                          193..194: Const(5)
                                                                                        188..200: Right
                                                                                          188..200: Const(8)
                                                                                188..200: Stmt2
                                                                                  188..200: Move
                                                                                    188..200: Destination
                                                                                      188..200: Temp(7)
                                                                                    188..200: Source
                                                                                      188..200: Call
                                                                                        188..200: Function
                                                                                          188..200: Name(malloc)
                                                                                        188..200: Arguments
                                                                                          188..200: Temp(8)
                                                                            188..200: Stmt2
                                                                              188..200: StmtExpr
                                                                                188..200: Call
                                                                                  188..200: Function
                                                                                    188..200: Name(initArray)
                                                                                  188..200: Arguments
                                                                                    188..200: Temp(7)
                                                                                    188..200: Temp(8)
                                                                                    199..200: Const(1)
                                                                        188..200: Expr
                                                                          188..200: Temp(7)
                                                            169..200: Stmt2
                                                              169..200: Jump([false17])
                                                                169..200: Target
                                                                  169..200: Name(false17)
                                                        169..200: Stmt2
                                                          169..200: Move
                                                            169..200: Destination
                                                              169..200: Temp(9)
                                                            169..200: Source
                                                              169..200: Const(0)
                                                    169..200: Stmt2
                                                      169..200: Jump([true16])
                                                        169..200: Target
                                                          169..200: Name(true16)
                                                169..200: Stmt2
                                                  169..200: Label(true16)
                                            169..200: Expr
                                              169..200: Temp(9)
                                  218..240: Expr
                                    218..240: ESeq
                                      218..240: Stmt
                                        218..240: Seq
                                          218..240: Stmt1
                                            218..240: Seq
                                              218..240: Stmt1
                                                218..240: Seq
                                                  218..240: Stmt1
                                                    218..240: Seq
                                                      218..240: Stmt1
                                                        218..240: Seq
                                                          218..240: Stmt1
                                                            218..240: Move
                                                              218..240: Destination
                                                                218..240: Temp(12)
                                                              218..240: Source
                                                                218..240: Const(1)
                                                          218..240: Stmt2
                                                            218..240: CJmp(<>) -> true18 | false19
                                                              218..226: Left
                                                                218..226: ESeq
                                                                  218..226: Stmt
                                                                    218..226: Seq
                                                                      218..226: Stmt1
                                                                        218..226: Move
                                                                          218..226: Destination
                                                                            218..226: Temp(10)
                                                                          218..226: Source
                                                                            218..226: Call
                                                                              218..226: Function
                                                                                218..226: Name(malloc)
                                                                              218..226: Arguments
                                                                                218..226: Const(8)
                                                                      218..226: Stmt2
                                                                        218..226: Move
                                                                          218..226: Destination
                                                                            218..226: Mem
                                                                              218..226: Expr
                                                                                218..226: BinOp(+)
                                                                                  218..226: Left
                                                                                    218..226: Temp(10)
                                                                                  218..226: Right
                                                                                    218..226: Const(0)
                                                                          225..226: Source
                                                                            225..226: Const(2)
                                                                  218..226: Expr
                                                                    218..226: Temp(10)
                                                              231..239: Right
                                                                231..239: ESeq
                                                                  231..239: Stmt
                                                                    231..239: Seq
                                                                      231..239: Stmt1
                                                                        231..239: Move
                                                                          231..239: Destination
                                                                            231..239: Temp(11)
                                                                          231..239: Source
                                                                            231..239: Call
                                                                              231..239: Function
                                                                                231..239: Name(malloc)
                                                                              231..239: Arguments
                                                                                231..239: Const(8)
                                                                      231..239: Stmt2
                                                                        231..239: Move
                                                                          231..239: Destination
                                                                            231..239: Mem
                                                                              231..239: Expr
                                                                                231..239: BinOp(+)
                                                                                  231..239: Left
                                                                                    231..239: Temp(11)
                                                                                  231..239: Right
                                                                                    231..239: Const(0)
                                                                          238..239: Source
                                                                            238..239: Const(3)
                                                                  231..239: Expr
                                                                    231..239: Temp(11)
                                                      218..240: Stmt2
                                                        218..240: Jump([false19])
                                                          218..240: Target
                                                            218..240: Name(false19)
                                                  218..240: Stmt2
                                                    218..240: Move
                                                      218..240: Destination
                                                        218..240: Temp(12)
                                                      218..240: Source
                                                        218..240: Const(0)
                                              218..240: Stmt2
                                                218..240: Jump([true18])
                                                  218..240: Target
                                                    218..240: Name(true18)
                                          218..240: Stmt2
                                            218..240: Label(true18)
                                      218..240: Expr
                                        218..240: Temp(12)
                            258..273: Expr
                              258..273: ESeq
                                258..273: Stmt
                                  258..273: Seq
                                    258..273: Stmt1
                                      258..273: Seq
                                        258..273: Stmt1
                                          258..273: Seq
                                            258..273: Stmt1
                                              258..273: Seq
                                                258..273: Stmt1
                                                  258..273: Seq
                                                    258..273: Stmt1
                                                      258..273: Move
                                                        258..273: Destination
                                                          258..273: Temp(14)
                                                        258..273: Source
                                                          258..273: Const(1)
                                                    258..273: Stmt2
                                                      258..273: CJmp(=) -> true20 | false21
                                                        258..266: Left
                                                          258..266: ESeq
                                                            258..266: Stmt
                                                              258..266: Seq
                                                                258..266: Stmt1
                                                                  258..266: Move
                                                                    258..266: Destination
                                                                      258..266: Temp(13)
                                                                    258..266: Source
                                                                      258..266: Call
                                                                        258..266: Function
                                                                          258..266: Name(malloc)
                                                                        258..266: Arguments
                                                                          258..266: Const(8)
                                                                258..266: Stmt2
                                                                  258..266: Move
                                                                    258..266: Destination
                                                                      258..266: Mem
                                                                        258..266: Expr
                                                                          258..266: BinOp(+)
                                                                            258..266: Left
                                                                              258..266: Temp(13)
                                                                            258..266: Right
                                                                              258..266: Const(0)
                                                                    265..266: Source
                                                                      265..266: Const(2)
                                                            258..266: Expr
                                                              258..266: Temp(13)
                                                        270..273: Right
                                                          270..273: Const(0)
                                                258..273: Stmt2
                                                  258..273: Jump([false21])
                                                    258..273: Target
                                                      258..273: Name(false21)
                                            258..273: Stmt2
                                              258..273: Move
                                                258..273: Destination
                                                  258..273: Temp(14)
                                                258..273: Source
                                                  258..273: Const(0)
                                        258..273: Stmt2
                                          258..273: Jump([true20])
                                            258..273: Target
                                              258..273: Name(true20)
                                    258..273: Stmt2
                                      258..273: Label(true20)
                                258..273: Expr
                                  258..273: Temp(14)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_exprs() {
        check_fragments(
            "(3; 2; nil)",
            vec![expect![[r#"
                    0..11: Procedure
                      Frame(_main) - 0
                      0..11: Move
                        0..11: Destination
                          0..11: Temp(rv)
                        0..11: Source
                          0..11: ESeq
                            0..11: Stmt
                              0..11: StmtExpr
                                0..11: ESeq
                                  1..2: Stmt
                                    1..2: StmtExpr
                                      1..2: Const(3)
                                  4..5: Expr
                                    4..5: Const(2)
                            7..10: Expr
                              7..10: Const(0)
                "#]]],
        );

        check_fragments(
            "(nil; 3)",
            vec![expect![[r#"
                    0..8: Procedure
                      Frame(_main) - 0
                      0..8: Move
                        0..8: Destination
                          0..8: Temp(rv)
                        0..8: Source
                          0..8: ESeq
                            1..4: Stmt
                              1..4: StmtExpr
                                1..4: Const(0)
                            6..7: Expr
                              6..7: Const(3)
                "#]]],
        );

        check_fragments(
            "(3; nil; \"hi\")",
            vec![
                expect![[r#"
                    String(label0)
                      "hi"
                "#]],
                expect![[r#"
                    0..14: Procedure
                      Frame(_main) - 0
                      0..14: Move
                        0..14: Destination
                          0..14: Temp(rv)
                        0..14: Source
                          0..14: ESeq
                            0..14: Stmt
                              0..14: StmtExpr
                                0..14: ESeq
                                  1..2: Stmt
                                    1..2: StmtExpr
                                      1..2: Const(3)
                                  4..7: Expr
                                    4..7: Const(0)
                            9..13: Expr
                              9..13: Name(label0)
                "#]],
            ],
        );
    }

    #[test]
    fn test_tyc_negate() {
        check_fragments(
            "--3",
            vec![expect![[r#"
                    0..3: Procedure
                      Frame(_main) - 0
                      0..3: Move
                        0..3: Destination
                          0..3: Temp(rv)
                        0..3: Source
                          0..3: BinOp(-)
                            0..3: Left
                              0..3: Const(0)
                            1..3: Right
                              1..3: BinOp(-)
                                1..3: Left
                                  1..3: Const(0)
                                2..3: Right
                                  2..3: Const(3)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_call() {
        check_fragments(
            r#"
            let
                primitive exit(code: int)
                primitive add(x: int, y: int): int
            in
                exit(1);
                add(1, 2)
            end
            "#,
            vec![expect![[r#"
                    141..175: Procedure
                      Frame(_main) - 0
                      141..175: Move
                        141..175: Destination
                          141..175: Temp(rv)
                        141..175: Source
                          141..175: ESeq
                            141..148: Stmt
                              141..148: StmtExpr
                                141..148: Call
                                  141..148: Function
                                    141..148: Name(exit)
                                  146..147: Arguments
                                    146..147: Const(1)
                            166..175: Expr
                              166..175: Call
                                166..175: Function
                                  166..175: Name(add)
                                170..174: Arguments
                                  170..171: Const(1)
                                  173..174: Const(2)
                "#]]],
        );

        check_fragments(
            r#"
            let
                function add(x: int, y: int): int = x + y
            in
                add(1, 2)
            end
            "#,
            vec![
                expect![[r#"
                    33..74: Procedure
                      Frame(add0) - -8
                        Formals
                          InFrame(-8)
                          Reg(Temp(3))
                          Reg(Temp(4))
                      33..74: Move
                        33..74: Destination
                          33..74: Temp(rv)
                        69..74: Source
                          69..74: BinOp(+)
                            69..70: Left
                              69..70: Temp(3)
                            73..74: Right
                              73..74: Temp(4)
                "#]],
                expect![[r#"
                    106..115: Procedure
                      Frame(_main) - 0
                      106..115: Move
                        106..115: Destination
                          106..115: Temp(rv)
                        106..115: Source
                          106..115: Call
                            106..115: Function
                              106..115: Name(add0)
                            106..114: Arguments
                              106..115: Temp(fp)
                              110..111: Const(1)
                              113..114: Const(2)
                "#]],
            ],
        );
    }

    #[test]
    fn test_tyc_break() {
        check_fragments(
            "while 1 > 2 do break",
            vec![expect![[r#"
                    6..20: Procedure
                      Frame(_main) - 0
                      6..20: Move
                        6..20: Destination
                          6..20: Temp(rv)
                        6..20: Source
                          6..20: ESeq
                            6..20: Stmt
                              6..20: Seq
                                6..20: Stmt1
                                  6..20: Seq
                                    6..20: Stmt1
                                      6..20: Seq
                                        6..20: Stmt1
                                          6..20: Seq
                                            6..20: Stmt1
                                              6..20: Seq
                                                6..20: Stmt1
                                                  6..20: Label(test1)
                                                6..11: Stmt2
                                                  6..11: CJmp(>) -> body2 | while_end0
                                                    6..7: Left
                                                      6..7: Const(1)
                                                    10..11: Right
                                                      10..11: Const(2)
                                            6..20: Stmt2
                                              6..20: Label(body2)
                                        15..20: Stmt2
                                          15..20: Jump([while_end0])
                                            15..20: Target
                                              15..20: Name(while_end0)
                                    15..20: Stmt2
                                      15..20: Jump([test1])
                                        15..20: Target
                                          15..20: Name(test1)
                                6..20: Stmt2
                                  6..20: Label(while_end0)
                            6..20: Expr
                              6..20: Const(0)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_assign() {
        check_fragments(
            "let var a := 1 in a := 3 end",
            vec![expect![[r#"
                    0..28: Procedure
                      Frame(_main) - 0
                      0..28: Move
                        0..28: Destination
                          0..28: Temp(rv)
                        0..28: Source
                          0..28: ESeq
                            4..14: Stmt
                              4..14: Move
                                4..14: Destination
                                  4..14: Temp(0)
                                13..14: Source
                                  13..14: Const(1)
                            18..24: Expr
                              18..24: ESeq
                                18..24: Stmt
                                  18..24: Move
                                    18..19: Destination
                                      18..19: Temp(0)
                                    23..24: Source
                                      23..24: Const(3)
                                18..24: Expr
                                  18..24: Const(0)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_if() {
        check_fragments(
            "if 0 then 1 else 2",
            vec![expect![[r#"
                    3..18: Procedure
                      Frame(_main) - 0
                      3..18: Move
                        3..18: Destination
                          3..18: Temp(rv)
                        3..18: Source
                          3..18: ESeq
                            3..18: Stmt
                              3..18: Seq
                                3..18: Stmt1
                                  3..18: Seq
                                    3..18: Stmt1
                                      3..18: Seq
                                        3..18: Stmt1
                                          3..18: Seq
                                            3..18: Stmt1
                                              3..18: Seq
                                                3..18: Stmt1
                                                  3..18: Seq
                                                    3..18: Stmt1
                                                      3..18: Seq
                                                        3..4: Stmt1
                                                          3..4: Jump([false1])
                                                            3..4: Target
                                                              3..4: Name(false1)
                                                        3..18: Stmt2
                                                          3..18: Label(true0)
                                                    10..11: Stmt2
                                                      10..11: Move
                                                        3..18: Destination
                                                          3..18: Temp(0)
                                                        10..11: Source
                                                          10..11: Const(1)
                                                10..11: Stmt2
                                                  10..11: Jump([end2])
                                                    10..11: Target
                                                      10..11: Name(end2)
                                            3..18: Stmt2
                                              3..18: Label(false1)
                                        17..18: Stmt2
                                          17..18: Move
                                            3..18: Destination
                                              3..18: Temp(0)
                                            17..18: Source
                                              17..18: Const(2)
                                    17..18: Stmt2
                                      17..18: Jump([end2])
                                        17..18: Target
                                          17..18: Name(end2)
                                3..18: Stmt2
                                  3..18: Label(end2)
                            3..18: Expr
                              3..18: Temp(0)
                "#]]],
        );

        check_fragments(
            "if 1 then 1 else 2",
            vec![expect![[r#"
                    3..18: Procedure
                      Frame(_main) - 0
                      3..18: Move
                        3..18: Destination
                          3..18: Temp(rv)
                        3..18: Source
                          3..18: ESeq
                            3..18: Stmt
                              3..18: Seq
                                3..18: Stmt1
                                  3..18: Seq
                                    3..18: Stmt1
                                      3..18: Seq
                                        3..18: Stmt1
                                          3..18: Seq
                                            3..18: Stmt1
                                              3..18: Seq
                                                3..18: Stmt1
                                                  3..18: Seq
                                                    3..18: Stmt1
                                                      3..18: Seq
                                                        3..4: Stmt1
                                                          3..4: Jump([true3])
                                                            3..4: Target
                                                              3..4: Name(true3)
                                                        3..18: Stmt2
                                                          3..18: Label(true3)
                                                    10..11: Stmt2
                                                      10..11: Move
                                                        3..18: Destination
                                                          3..18: Temp(1)
                                                        10..11: Source
                                                          10..11: Const(1)
                                                10..11: Stmt2
                                                  10..11: Jump([end5])
                                                    10..11: Target
                                                      10..11: Name(end5)
                                            3..18: Stmt2
                                              3..18: Label(false4)
                                        17..18: Stmt2
                                          17..18: Move
                                            3..18: Destination
                                              3..18: Temp(1)
                                            17..18: Source
                                              17..18: Const(2)
                                    17..18: Stmt2
                                      17..18: Jump([end5])
                                        17..18: Target
                                          17..18: Name(end5)
                                3..18: Stmt2
                                  3..18: Label(end5)
                            3..18: Expr
                              3..18: Temp(1)
                "#]]],
        );

        check_fragments(
            "if 1 = 1 then (nil; 3) else 2",
            vec![expect![[r#"
                    3..29: Procedure
                      Frame(_main) - 0
                      3..29: Move
                        3..29: Destination
                          3..29: Temp(rv)
                        3..29: Source
                          3..29: ESeq
                            3..29: Stmt
                              3..29: Seq
                                3..29: Stmt1
                                  3..29: Seq
                                    3..29: Stmt1
                                      3..29: Seq
                                        3..29: Stmt1
                                          3..29: Seq
                                            3..29: Stmt1
                                              3..29: Seq
                                                3..29: Stmt1
                                                  3..29: Seq
                                                    3..29: Stmt1
                                                      3..29: Seq
                                                        3..8: Stmt1
                                                          3..8: CJmp(=) -> true6 | false7
                                                            3..4: Left
                                                              3..4: Const(1)
                                                            7..8: Right
                                                              7..8: Const(1)
                                                        3..29: Stmt2
                                                          3..29: Label(true6)
                                                    14..22: Stmt2
                                                      14..22: Move
                                                        3..29: Destination
                                                          3..29: Temp(2)
                                                        14..22: Source
                                                          14..22: ESeq
                                                            15..18: Stmt
                                                              15..18: StmtExpr
                                                                15..18: Const(0)
                                                            20..21: Expr
                                                              20..21: Const(3)
                                                14..22: Stmt2
                                                  14..22: Jump([end8])
                                                    14..22: Target
                                                      14..22: Name(end8)
                                            3..29: Stmt2
                                              3..29: Label(false7)
                                        28..29: Stmt2
                                          28..29: Move
                                            3..29: Destination
                                              3..29: Temp(2)
                                            28..29: Source
                                              28..29: Const(2)
                                    28..29: Stmt2
                                      28..29: Jump([end8])
                                        28..29: Target
                                          28..29: Name(end8)
                                3..29: Stmt2
                                  3..29: Label(end8)
                            3..29: Expr
                              3..29: Temp(2)
                "#]]],
        );

        check_fragments(
            "if 3 then () else ()",
            vec![expect![[r#"
                    3..20: Procedure
                      Frame(_main) - 0
                      3..20: Move
                        3..20: Destination
                          3..20: Temp(rv)
                        3..20: Source
                          3..20: ESeq
                            3..20: Stmt
                              3..20: Seq
                                3..20: Stmt1
                                  3..20: Seq
                                    3..20: Stmt1
                                      3..20: Seq
                                        3..20: Stmt1
                                          3..20: Seq
                                            3..20: Stmt1
                                              3..20: Seq
                                                3..20: Stmt1
                                                  3..20: Seq
                                                    3..20: Stmt1
                                                      3..20: Seq
                                                        3..4: Stmt1
                                                          3..4: Jump([true9])
                                                            3..4: Target
                                                              3..4: Name(true9)
                                                        3..20: Stmt2
                                                          3..20: Label(true9)
                                                    10..12: Stmt2
                                                      10..12: StmtExpr
                                                        10..12: Const(0)
                                                10..12: Stmt2
                                                  10..12: Jump([end11])
                                                    10..12: Target
                                                      10..12: Name(end11)
                                            3..20: Stmt2
                                              3..20: Label(false10)
                                        18..20: Stmt2
                                          18..20: StmtExpr
                                            18..20: Const(0)
                                    18..20: Stmt2
                                      18..20: Jump([end11])
                                        18..20: Target
                                          18..20: Name(end11)
                                3..20: Stmt2
                                  3..20: Label(end11)
                            3..20: Expr
                              3..20: Const(0)
                "#]]],
        );

        check_fragments(
            "if 3 = 3 then 2 > 1 else 1 = 1",
            vec![expect![[r#"
                    3..30: Procedure
                      Frame(_main) - 0
                      3..30: Move
                        3..30: Destination
                          3..30: Temp(rv)
                        3..30: Source
                          3..30: ESeq
                            3..30: Stmt
                              3..30: Seq
                                3..30: Stmt1
                                  3..30: Seq
                                    3..30: Stmt1
                                      3..30: Seq
                                        3..30: Stmt1
                                          3..30: Seq
                                            3..30: Stmt1
                                              3..30: Seq
                                                3..30: Stmt1
                                                  3..30: Seq
                                                    3..30: Stmt1
                                                      3..30: Seq
                                                        3..8: Stmt1
                                                          3..8: CJmp(=) -> true12 | false13
                                                            3..4: Left
                                                              3..4: Const(3)
                                                            7..8: Right
                                                              7..8: Const(3)
                                                        3..30: Stmt2
                                                          3..30: Label(true12)
                                                    14..19: Stmt2
                                                      14..19: Move
                                                        3..30: Destination
                                                          3..30: Temp(3)
                                                        14..19: Source
                                                          14..19: ESeq
                                                            14..19: Stmt
                                                              14..19: Seq
                                                                14..19: Stmt1
                                                                  14..19: Seq
                                                                    14..19: Stmt1
                                                                      14..19: Seq
                                                                        14..19: Stmt1
                                                                          14..19: Seq
                                                                            14..19: Stmt1
                                                                              14..19: Seq
                                                                                14..19: Stmt1
                                                                                  14..19: Move
                                                                                    14..19: Destination
                                                                                      14..19: Temp(4)
                                                                                    14..19: Source
                                                                                      14..19: Const(1)
                                                                                14..19: Stmt2
                                                                                  14..19: CJmp(>) -> true15 | false16
                                                                                    14..15: Left
                                                                                      14..15: Const(2)
                                                                                    18..19: Right
                                                                                      18..19: Const(1)
                                                                            14..19: Stmt2
                                                                              14..19: Jump([false16])
                                                                                14..19: Target
                                                                                  14..19: Name(false16)
                                                                        14..19: Stmt2
                                                                          14..19: Move
                                                                            14..19: Destination
                                                                              14..19: Temp(4)
                                                                            14..19: Source
                                                                              14..19: Const(0)
                                                                    14..19: Stmt2
                                                                      14..19: Jump([true15])
                                                                        14..19: Target
                                                                          14..19: Name(true15)
                                                                14..19: Stmt2
                                                                  14..19: Label(true15)
                                                            14..19: Expr
                                                              14..19: Temp(4)
                                                14..19: Stmt2
                                                  14..19: Jump([end14])
                                                    14..19: Target
                                                      14..19: Name(end14)
                                            3..30: Stmt2
                                              3..30: Label(false13)
                                        25..30: Stmt2
                                          25..30: Move
                                            3..30: Destination
                                              3..30: Temp(3)
                                            25..30: Source
                                              25..30: ESeq
                                                25..30: Stmt
                                                  25..30: Seq
                                                    25..30: Stmt1
                                                      25..30: Seq
                                                        25..30: Stmt1
                                                          25..30: Seq
                                                            25..30: Stmt1
                                                              25..30: Seq
                                                                25..30: Stmt1
                                                                  25..30: Seq
                                                                    25..30: Stmt1
                                                                      25..30: Move
                                                                        25..30: Destination
                                                                          25..30: Temp(5)
                                                                        25..30: Source
                                                                          25..30: Const(1)
                                                                    25..30: Stmt2
                                                                      25..30: CJmp(=) -> true17 | false18
                                                                        25..26: Left
                                                                          25..26: Const(1)
                                                                        29..30: Right
                                                                          29..30: Const(1)
                                                                25..30: Stmt2
                                                                  25..30: Jump([false18])
                                                                    25..30: Target
                                                                      25..30: Name(false18)
                                                            25..30: Stmt2
                                                              25..30: Move
                                                                25..30: Destination
                                                                  25..30: Temp(5)
                                                                25..30: Source
                                                                  25..30: Const(0)
                                                        25..30: Stmt2
                                                          25..30: Jump([true17])
                                                            25..30: Target
                                                              25..30: Name(true17)
                                                    25..30: Stmt2
                                                      25..30: Label(true17)
                                                25..30: Expr
                                                  25..30: Temp(5)
                                    25..30: Stmt2
                                      25..30: Jump([end14])
                                        25..30: Target
                                          25..30: Name(end14)
                                3..30: Stmt2
                                  3..30: Label(end14)
                            3..30: Expr
                              3..30: Temp(3)
                "#]]],
        );

        check_fragments(
            "if 3 then \"h\" else \"i\"",
            vec![
                expect![[r#"
                    String(label19)
                      "h"
                "#]],
                expect![[r#"
                    String(label20)
                      "i"
                "#]],
                expect![[r#"
                    3..22: Procedure
                      Frame(_main) - 0
                      3..22: Move
                        3..22: Destination
                          3..22: Temp(rv)
                        3..22: Source
                          3..22: ESeq
                            3..22: Stmt
                              3..22: Seq
                                3..22: Stmt1
                                  3..22: Seq
                                    3..22: Stmt1
                                      3..22: Seq
                                        3..22: Stmt1
                                          3..22: Seq
                                            3..22: Stmt1
                                              3..22: Seq
                                                3..22: Stmt1
                                                  3..22: Seq
                                                    3..22: Stmt1
                                                      3..22: Seq
                                                        3..4: Stmt1
                                                          3..4: Jump([true21])
                                                            3..4: Target
                                                              3..4: Name(true21)
                                                        3..22: Stmt2
                                                          3..22: Label(true21)
                                                    10..13: Stmt2
                                                      10..13: Move
                                                        3..22: Destination
                                                          3..22: Temp(6)
                                                        10..13: Source
                                                          10..13: Name(label19)
                                                10..13: Stmt2
                                                  10..13: Jump([end23])
                                                    10..13: Target
                                                      10..13: Name(end23)
                                            3..22: Stmt2
                                              3..22: Label(false22)
                                        19..22: Stmt2
                                          19..22: Move
                                            3..22: Destination
                                              3..22: Temp(6)
                                            19..22: Source
                                              19..22: Name(label20)
                                    19..22: Stmt2
                                      19..22: Jump([end23])
                                        19..22: Target
                                          19..22: Name(end23)
                                3..22: Stmt2
                                  3..22: Label(end23)
                            3..22: Expr
                              3..22: Temp(6)
                "#]],
            ],
        );
    }

    #[test]
    fn test_tyc_while() {
        check_fragments(
            "while 3 > 2 do if 2 = 2 then break",
            vec![expect![[r#"
                    6..34: Procedure
                      Frame(_main) - 0
                      6..34: Move
                        6..34: Destination
                          6..34: Temp(rv)
                        6..34: Source
                          6..34: ESeq
                            6..34: Stmt
                              6..34: Seq
                                6..34: Stmt1
                                  6..34: Seq
                                    6..34: Stmt1
                                      6..34: Seq
                                        6..34: Stmt1
                                          6..34: Seq
                                            6..34: Stmt1
                                              6..34: Seq
                                                6..34: Stmt1
                                                  6..34: Label(test4)
                                                6..11: Stmt2
                                                  6..11: CJmp(>) -> body5 | while_end0
                                                    6..7: Left
                                                      6..7: Const(3)
                                                    10..11: Right
                                                      10..11: Const(2)
                                            6..34: Stmt2
                                              6..34: Label(body5)
                                        18..34: Stmt2
                                          18..34: Seq
                                            18..34: Stmt1
                                              18..34: Seq
                                                18..34: Stmt1
                                                  18..34: Seq
                                                    18..34: Stmt1
                                                      18..34: Seq
                                                        18..34: Stmt1
                                                          18..34: Seq
                                                            18..34: Stmt1
                                                              18..34: Seq
                                                                18..34: Stmt1
                                                                  18..34: Seq
                                                                    18..23: Stmt1
                                                                      18..23: CJmp(=) -> true1 | false2
                                                                        18..19: Left
                                                                          18..19: Const(2)
                                                                        22..23: Right
                                                                          22..23: Const(2)
                                                                    18..34: Stmt2
                                                                      18..34: Label(true1)
                                                                29..34: Stmt2
                                                                  29..34: Jump([while_end0])
                                                                    29..34: Target
                                                                      29..34: Name(while_end0)
                                                            29..34: Stmt2
                                                              29..34: Jump([end3])
                                                                29..34: Target
                                                                  29..34: Name(end3)
                                                        18..34: Stmt2
                                                          18..34: Label(false2)
                                                    18..34: Stmt2
                                                      18..34: StmtExpr
                                                        18..34: Const(0)
                                                18..34: Stmt2
                                                  18..34: Jump([end3])
                                                    18..34: Target
                                                      18..34: Name(end3)
                                            18..34: Stmt2
                                              18..34: Label(end3)
                                    18..34: Stmt2
                                      18..34: Jump([test4])
                                        18..34: Target
                                          18..34: Name(test4)
                                6..34: Stmt2
                                  6..34: Label(while_end0)
                            6..34: Expr
                              6..34: Const(0)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_for() {
        check_fragments(
            "for i := 0 to 10 do break",
            vec![expect![[r#"
                    0..25: Procedure
                      Frame(_main) - 0
                      0..25: Move
                        0..25: Destination
                          0..25: Temp(rv)
                        0..25: Source
                          0..25: ESeq
                            0..25: Stmt
                              0..25: Seq
                                0..25: Stmt1
                                  0..25: Seq
                                    0..25: Stmt1
                                      0..25: Seq
                                        0..25: Stmt1
                                          0..25: Seq
                                            0..25: Stmt1
                                              0..25: Seq
                                                0..25: Stmt1
                                                  0..25: Seq
                                                    0..25: Stmt1
                                                      0..25: Seq
                                                        9..10: Stmt1
                                                          9..10: Move
                                                            4..5: Destination
                                                              4..5: Temp(0)
                                                            9..10: Source
                                                              9..10: Const(0)
                                                        0..25: Stmt2
                                                          0..25: Jump([test1])
                                                            0..25: Target
                                                              0..25: Name(test1)
                                                    20..25: Stmt2
                                                      20..25: Label(body2)
                                                0..25: Stmt2
                                                  0..25: Move
                                                    4..5: Destination
                                                      4..5: Temp(0)
                                                    0..25: Source
                                                      0..25: BinOp(+)
                                                        4..5: Left
                                                          4..5: Temp(0)
                                                        0..25: Right
                                                          0..25: Const(1)
                                            20..25: Stmt2
                                              20..25: Jump([for_end0])
                                                20..25: Target
                                                  20..25: Name(for_end0)
                                        14..16: Stmt2
                                          14..16: Label(test1)
                                    14..16: Stmt2
                                      14..16: CJmp(<) -> body2 | for_end0
                                        4..5: Left
                                          4..5: Temp(0)
                                        14..16: Right
                                          14..16: Const(10)
                                0..25: Stmt2
                                  0..25: Label(for_end0)
                            0..25: Expr
                              0..25: Const(0)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_error_binary_op() {
        check_err(
            r#"
            let
                type ints = array of int
                type m = {n: int}
            in
                3 + nil;
                "hi" + 3;
                "hi" + nil;
                3 > "hi";
                nil = nil;
                (ints[1] of 0) = m {n = 1};
                (ints[1] of 0) = nil;
                (ints[1] of 0) > ints[1] of 0
            end
            "#,
            vec![
                expect![[r#"(127, 130): Expected an int, got 'nil'"#]],
                expect![[r#"(148, 152): Expected an int, got 'string'"#]],
                expect![[r#"(174, 178): Expected an int, got 'string'"#]],
                expect![[r#"(181, 184): Expected an int, got 'nil'"#]],
                expect![[r#"(206, 210): Expected an int, got 'string'"#]],
                expect![[r#"(228, 237): Nil cannot be compared with nil"#]],
                expect![[r#"(255, 281): Cannot compare type 'int[]' with '{n: int}'"#]],
                expect![[r#"(299, 319): Cannot compare type 'int[]' with 'nil'"#]],
                expect![[r#"(337, 366): Only the types int, and string can be ordered"#]],
            ],
        );
    }

    #[test]
    fn test_tyc_error_negate() {
        check_err(
            "-nil",
            vec![expect![[r#"(1, 4): Expected an int, got 'nil'"#]]],
        );

        check_err(
            "-\"hi\"",
            vec![expect![[r#"(1, 5): Expected an int, got 'string'"#]]],
        );
    }

    #[test]
    fn test_tyc_error_call() {
        check_err(
            r#"
            let
                primitive exit(code: int)
            in
                exit()
            end
            "#,
            vec![expect![[
                r#"(90, 96): Function 'exit' expects 1 argument, 0 given"#
            ]]],
        );

        check_err(
            "let var a := 1 in a() end",
            vec![expect![[r#"(18, 19): Expected a function, got 'int'"#]]],
        );

        check_err(
            "let primitive add(x: int, y: int): int in add(add(\"1\", nil, 2)) end",
            vec![
                expect![[r#"(50, 53): Expected type 'int', got 'string'"#]],
                expect![[r#"(55, 58): Expected type 'int', got 'nil'"#]],
                expect![[r#"(46, 62): Function 'add' expects 2 arguments, 3 given"#]],
                expect![[r#"(42, 63): Function 'add' expects 2 arguments, 1 given"#]],
            ],
        );
    }

    #[test]
    fn test_tyc_error_exprs() {
        check_err(
            "1 + (3; nil)",
            vec![expect![[r#"(4, 12): Expected an int, got 'nil'"#]]],
        );

        check_err(
            "2 + (nil + 1; 3)",
            vec![expect![[r#"(5, 8): Expected an int, got 'nil'"#]]],
        );
    }

    #[test]
    fn test_tyc_error_records() {
        check_err(
            "let type meter = {m:int} var m := meter {m=\"h\", n=2} var a := 3 in a.m end",
            vec![
                expect![[r#"(43, 46): Expected type 'int', got 'string'"#]],
                expect![[r#"(48, 49): Field 'n' does not exist in type {m: int}"#]],
                expect![[r#"(69, 70): Cannot access field 'm' of non-record int"#]],
            ],
        );

        check_err(
            "let type meter = {m:int} var m := meter {} in m.m end",
            vec![expect![[
                r#"(34, 39): Missing field m for record {m: int}"#
            ]]],
        );

        check_err(
            "let type meter = {m:int} var m := meter {n=2} in m.m end",
            vec![
                expect![[r#"(34, 39): Missing field m for record {m: int}"#]],
                expect![[r#"(41, 42): Field 'n' does not exist in type {m: int}"#]],
            ],
        );
    }

    #[test]
    fn test_tyc_error_assign() {
        check_err(
            "let var a := 1 in a := \"h\" end",
            vec![expect![[r#"(23, 26): Expected type 'int', got 'string'"#]]],
        );

        check_err(
            "let var a := 1 in b := \"h\" end",
            vec![expect![[r#"(18, 19): Undefined variable 'b'"#]]],
        );
    }

    #[test]
    fn test_tyc_error_if() {
        check_err(
            "if \"h\" then 3",
            vec![
                expect![[r#"(3, 6): Expected an int, got 'string'"#]],
                expect![[
                    r#"(12, 13): Expected then branch to return unit, as it does not have an else branch, got 'int'"#
                ]],
            ],
        );

        check_err(
            "if nil then 3 else \"h\"",
            vec![
                expect![[r#"(3, 6): Expected an int, got 'nil'"#]],
                expect![[
                    r#"(12, 22): Then and else branch return types don't match - 'int' and 'string' respectively"#
                ]],
            ],
        );
    }

    #[test]
    fn test_tyc_error_while() {
        check_err(
            "while break do break",
            vec![
                expect![[r#"(6, 11): Cannot break outside a loop"#]],
                expect![[r#"(6, 11): Expected an int, got 'unit'"#]],
            ],
        );
    }

    #[test]
    fn test_tyc_error_break() {
        check_err(
            "break",
            vec![expect![[r#"(0, 5): Cannot break outside a loop"#]]],
        );
    }

    #[test]
    fn test_tyc_error_for() {
        check_err(
            "for i := i + 1 to \"hi\" do 3",
            vec![
                expect![[r#"(9, 10): Undefined variable 'i'"#]],
                expect![[r#"(18, 22): Expected an int, got 'string'"#]],
                expect![[r#"(26, 27): Expected no value, got 'int'"#]],
            ],
        );
    }
}
