use std::rc::Rc;

use tig_arch::Frame;
use tig_common::Span;
use tig_error::SpannedError;
use tig_syntax::ast;

use crate::{ExpTy, Type};

use super::{TEnv, Translator, VEnv, ValEntry};

/// Pushes a SpannedError to self.errors.
macro_rules! E {
    ($translator:expr, $span:expr, $($error:expr),+ $(,)?) => {
        $translator.errors.push(SpannedError::new(
            format!($($error),+),
            $span,
        ))
    };
}

impl<F: Frame + PartialEq + Eq> Translator<F> {
    /// Translates an expression into an `ExpTy`.
    pub(super) fn translate_expr(&mut self, expr: ast::Expr, venv: &VEnv<F>, tenv: &TEnv) -> ExpTy {
        let ast::Expr {
            span,
            kind: expr_kind,
        } = expr;
        match expr_kind {
            ast::ExprKind::Nil => ExpTy {
                exp: (),
                ty: Type::nil(),
            },

            ast::ExprKind::Integer(_) => ExpTy {
                exp: (),
                ty: Type::int(),
            },

            ast::ExprKind::String(_) => ExpTy {
                exp: (),
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
                    exp: (),
                    ty: Type::int(),
                }
            }

            ast::ExprKind::BinOp { op, left, right } => {
                self.translate_binary_op(op, *left, *right, venv, tenv)
            }

            ast::ExprKind::Exprs(exprs) => {
                if exprs.is_empty() {
                    // HACK: empty parenthesis is the unit type
                    return ExpTy {
                        exp: (),
                        ty: Type::unit(),
                    };
                }
                let mut expty = ExpTy {
                    exp: (),
                    ty: Type::nil(),
                };
                for exp in exprs {
                    expty = self.translate_expr(exp, venv, tenv);
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
                    exp: (),
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
                venv.enter(iterator.value, ValEntry::Variable { ty: Type::int() });
                let _access = self.current_level.alloc_local(escape);

                self.loop_stack += 1;
                let body_span = body.span;
                let body_ty = self.translate_expr(*body, &venv, tenv);
                self.expect_unit(&body_ty, body_span, tenv);
                self.loop_stack -= 1;

                ExpTy {
                    exp: (),
                    ty: Type::unit(),
                }
            }

            ast::ExprKind::Break => {
                if self.loop_stack == 0 {
                    E!(self, span, "Cannot break outside a loop",);
                }
                ExpTy {
                    exp: (),
                    ty: Type::unit(),
                }
            }

            ast::ExprKind::Let { decs, expr } => {
                let (venv, tenv) = self.translate_decs(decs, venv, tenv);
                self.translate_expr(*expr, &venv, &tenv)
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
                (Type::String, Type::String) => {}
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
        }

        ExpTy {
            exp: (),
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
        let (formals, result) = match venv.look(&func.value) {
            Some(f) => match f {
                ValEntry::Variable { ty } => {
                    E!(self, func.span, "Expected a function, got '{}'", ty,);
                    return ExpTy {
                        exp: (),
                        ty: Type::hole(),
                    };
                }
                ValEntry::Function {
                    formals, result, ..
                } => (formals, result),
            },
            None => {
                E!(self, func.span, "Undefined function '{}'", func.value,);
                return ExpTy {
                    exp: (),
                    ty: Type::hole(),
                };
            }
        };

        let formals_len = formals.len();
        let arguments_len = arguments.len();
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
            exp: (),
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
                    exp: (),
                    ty: array_ty,
                }
            }
            Type::Hole => ExpTy {
                exp: (),
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
                    exp: (),
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
                    exp: (),
                    ty: Type::hole(),
                };
            }
        };

        let ty_r = self.actual_ty(found_ty, ty_id_span, tenv);
        match &*ty_r {
            Type::Record {
                fields: ty_fields, ..
            } => {
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
                ExpTy { exp: (), ty: ty_r }
            }
            Type::Hole => ExpTy {
                exp: (),
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
                    exp: (),
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

        match else_branch {
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
                    ExpTy {
                        exp: (),
                        ty: then_branch_ty.ty,
                    }
                } else {
                    E!(
                        self,
                        then_branch_span.extend(else_branch_span),
                        "Then and else branch return types don't match - '{}' and '{}' respectively",
                        then_branch_ty.ty,
                        else_branch_ty.ty,
                    );
                    ExpTy {
                        exp: (),
                        ty: Type::hole(),
                    }
                }
            }
            None => match &*then_branch_ty.ty {
                Type::Unit | Type::Hole => ExpTy {
                    exp: (),
                    ty: then_branch_ty.ty,
                },
                _ => {
                    E!(
                        self,
                        then_branch_span,
                        "Expected then branch to return unit, as it does not have an else branch, got '{}'",
                        then_branch_ty.ty
                      );
                    ExpTy {
                        exp: (),
                        ty: Type::hole(),
                    }
                }
            },
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

        self.loop_stack += 1;
        let body_span = body.span;
        let body_ty = self.translate_expr(body, venv, tenv);
        self.expect_unit(&body_ty, body_span, tenv);
        self.loop_stack -= 1;

        ExpTy {
            exp: (),
            ty: Type::unit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use expect_test::{expect, Expect};
    use tig_arch::amd64::Amd64Frame;

    use crate::translate_program;

    use tig_syntax::parse_str;

    fn check(program: &str, expected: Expect) {
        let (_, p) = parse_str(program);
        assert_eq!(p.errors, vec![]);
        let result = translate_program::<Amd64Frame>(p.program.expect("Should have compiled"));
        assert_eq!(result.errors, vec![]);
        expected.assert_debug_eq(&result.expty);
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
    fn test_tyc_literal_types() {
        check(
            "3",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Int,
                }
            "#]],
        );

        check(
            "nil",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Nil,
                }
            "#]],
        );

        check(
            "\"Hi\"",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: String,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_unit_type() {
        check(
            "let var a := () in a end",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Unit,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_binary_op() {
        check(
            r#"
            let
                type ints = array of int
                type m = {n: int}
            in
                3 + 1;
                3 * 1;
                3 > 1;
                3 = 1;
                "h" <> "i";
                "h" > "i";
                (ints [10] of 0) = ints[5] of 1;
                m {n = 2} <> m {n = 3};
                m {n = 2} = nil
            end
            "#,
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Int,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_exprs() {
        check(
            "(3; 2; nil)",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Nil,
                }
            "#]],
        );

        check(
            "(nil; 3)",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Int,
                }
            "#]],
        );

        check(
            "(3; nil; \"hi\")",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: String,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_negate() {
        check(
            "--3",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Int,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_call() {
        check(
            r#"
            let
                primitive exit(code: int)
                primitive add(x: int, y: int): int
            in
                exit(1);
                add(1, 2)
            end
            "#,
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Int,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_break() {
        check(
            "while 1 do break",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Unit,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_records() {
        check(
            "let type meter = {m:int} var m := meter {m=1} in m.m end",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Int,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_assign() {
        check(
            "let var a := 1 in a := 3 end",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Unit,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_array() {
        check(
            "let type ints = array of int var i := ints [10] of 0 in i[0] end",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Int,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_if() {
        check(
            "if 3 then \"h\" else \"i\"",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: String,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_while() {
        check(
            "while 1 do break",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Unit,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_for() {
        check(
            "for i := 0 to 10 do break",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Unit,
                }
            "#]],
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
