use std::rc::Rc;

use tig_common::Span;
use tig_error::SpannedError;
use tig_syntax::ast;

use crate::{RType, Type};

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

impl Translator {
    /// Translates a list of declarations, creating new value and type environments and returning
    /// them.
    pub(super) fn translate_decs<'venv, 'tenv>(
        &mut self,
        decs: Vec<ast::Dec>,
        venv: &'venv VEnv<'venv>,
        tenv: &'tenv TEnv<'tenv>,
    ) -> (VEnv<'venv>, TEnv<'tenv>) {
        let mut venv = venv.new_child();
        let mut tenv = tenv.new_child();

        for dec in decs {
            self.translate_dec(dec, &mut venv, &mut tenv);
        }

        (venv, tenv)
    }

    /// Translates a declaration, modifying `venv` and `tenv` in place.
    fn translate_dec(&mut self, dec: ast::Dec, venv: &mut VEnv, tenv: &mut TEnv) {
        let ast::Dec {
            kind: dec_kind,
            span,
        } = dec;
        match dec_kind {
            ast::DecKind::Type(typedecs) => self.translate_typedecs(span, typedecs, tenv),

            ast::DecKind::Variable {
                name, ty, value, ..
            } => self.translate_variable_dec(name, ty, *value, venv, tenv),

            ast::DecKind::Function(funcs) => self.translate_functions(funcs, venv, tenv),

            ast::DecKind::Primitive {
                name,
                parameters,
                ret_ty,
            } => self.translate_primitive(name, parameters, ret_ty, venv, tenv),
        }
    }

    fn translate_typedecs(&mut self, span: Span, typedecs: Vec<ast::TypeDec>, tenv: &mut TEnv) {
        let names = typedecs.iter().map(|t| t.name.clone()).collect::<Vec<_>>();
        // First all the headers are inserted into the type environment.
        //
        // type list = {first: int, rest: list}
        //
        // `type list` is the header.
        // We insert a type `list -> list(None)`
        for name in &names {
            tenv.enter(name.value.clone(), Type::name(name.clone(), None));
        }

        let mut newtypes = vec![];
        // With all the headers in the type environment, we can now
        // translate the types. We don't return the actual type, as the headers
        // are still invalid.
        for tydec in typedecs {
            let ty = self.translate_ty(tydec.ty, tenv);
            let ty_ref = tenv
                .get_immediate(&tydec.name.value)
                .expect("ICE: The type name should be present in the type environment.");
            match &**ty_ref {
                Type::Name { ty: opt_ty, .. } => {
                    if &ty == ty_ref {
                        E!(self, span, "Type declaration cycle not allowed",);
                    } else {
                        // We don't have to check types that point to themselves for cycles again.
                        newtypes.push(Rc::clone(ty_ref));
                    }
                    *opt_ty.borrow_mut() = Some(ty);
                }
                ty_ref => panic!(
                    "ICE: A name type should have been added to the type environment, got {}",
                    ty_ref
                ),
            }
        }

        // FIXME: Performance improvement, don't recheck every type every time.
        // E.g.
        //
        // type a = b       // On the first loop check, we visit a and b.
        // type b = int     // On the second loop check, we can safely ignore b.
        // type c = d
        // type d = c
        let newtypes_len = newtypes.len();
        for (i, ty) in newtypes
            .into_iter()
            .take(newtypes_len.saturating_sub(1))
            .enumerate()
        {
            if let Type::Name { ty, .. } = &*ty {
                match &*ty.borrow() {
                    Some(ty) => {
                        if self.check_type_loops(ty, ty, newtypes_len - i + 1) {
                            E!(self, span, "Cycle between types detected",);
                            break;
                        }
                    }
                    None => {}
                }
            }
        }
    }

    /// Helper function for type declarations.
    ///
    /// When a type cycle is declared, it will look the following way.
    ///
    /// `Name { a, Some Name { b, Some Name { a, ... }}}`
    ///
    /// To detect a cycle, we follow the refs of the name types. If at any point the cycle is
    /// broken, by either not having a reference (which should be a bug), or pointing to a terminal
    /// type (i.e. non-name), then we don't have a loop.
    ///
    /// `Orig` is the root type of our check, if at any point we see it again, there is a cycle.
    /// `Ty` is our current position in the graph. On the first call they'll be the same.
    /// `max_rec` should be at most the number of consecutive type declarations, as only those can
    /// introduce cycles.
    fn check_type_loops(&self, orig: &RType, ty: &RType, max_rec: usize) -> bool {
        // Base case, once we reach max_rec, we know there is no loop.
        if max_rec == 0 {
            return false;
        }

        // On the first call, orig and ty are the same, so first we have to evaluate ty.
        // If it evaluates to a non-name, or a name with no reference, we don't have a cycle.
        // Otherwise, follow the reference.
        match &**ty {
            Type::Name { ty: rty, .. } => match &*rty.borrow() {
                Some(rty) if rty == orig => true,
                Some(ty) => self.check_type_loops(orig, ty, max_rec - 1),
                None => false,
            },
            // If it resolves to anything that is not a name, it is not a loop.
            _ => false,
        }
    }

    fn translate_variable_dec(
        &mut self,
        name: ast::Ident,
        ty: Option<ast::Ident>,
        value: ast::Expr,
        venv: &mut VEnv,
        tenv: &mut TEnv,
    ) {
        let value_span = value.span;
        let value = self.translate_expr(value, venv, tenv);
        let ty = match ty {
            Some(ty) => self.resolve_ty(&ty.value, ty.span, tenv, true),
            None => match &*value.ty {
                Type::Nil => {
                    E!(
                        self,
                        value_span,
                        "Cannot assign nil to a variable without a specified type",
                    );
                    Type::hole()
                }
                _ => Rc::clone(&value.ty),
            },
        };
        if ty != self.actual_ty(&value.ty, value_span, tenv) {
            E!(
                self,
                value_span,
                "Expected type '{}', got '{}'",
                ty,
                value.ty
            );
        }
        venv.enter(name.value, ValEntry::Variable { ty });
    }

    fn translate_functions(
        &mut self,
        funcs: Vec<ast::FunctionDec>,
        venv: &mut VEnv,
        tenv: &mut TEnv,
    ) {
        let mut processed_funcs = vec![];

        for f in funcs {
            let ast::FunctionDec {
                name,
                parameters,
                ret_ty,
                body,
                ..
            } = f;

            let mut processed_params = vec![];
            let mut formals = vec![];
            for p in parameters {
                let ast::Field { name, ty, .. } = p;
                let p_ty = self.resolve_ty(&ty.value, ty.span, tenv, true);
                processed_params.push((name, Rc::clone(&p_ty)));
                formals.push(p_ty);
            }

            let result = ret_ty
                .map(|ty| self.resolve_ty(&ty.value, ty.span, tenv, true))
                .unwrap_or_else(Type::unit);

            venv.enter(
                name.value.clone(),
                ValEntry::Function {
                    formals,
                    result: Rc::clone(&result),
                },
            );

            processed_funcs.push((processed_params, body, result));
        }

        for (params, body, expected_result) in processed_funcs {
            let mut venv = venv.new_child();

            for (name, ty) in params {
                venv.enter(name.value, ValEntry::Variable { ty });
            }

            let body_span = body.span;
            let body_ty = self.translate_expr(*body, &venv, tenv);

            if expected_result != self.actual_ty(&body_ty.ty, body_span, tenv) {
                E!(
                    self,
                    body_span,
                    "Expected function to return '{}', got '{}'",
                    expected_result,
                    body_ty.ty,
                );
            }
        }
    }

    fn translate_primitive(
        &mut self,
        name: ast::Ident,
        parameters: Vec<ast::TyField>,
        ret_ty: Option<ast::Ident>,
        venv: &mut VEnv,
        tenv: &mut TEnv,
    ) {
        let formals = parameters
            .iter()
            .map(|p| self.resolve_ty(&p.ty.value, p.ty.span, tenv, true))
            .collect::<Vec<_>>();

        let result = match ret_ty {
            Some(ty) => self.resolve_ty(&ty.value, ty.span, tenv, true),
            None => Type::unit(),
        };

        venv.enter(name.value, ValEntry::Function { formals, result });
    }
}

#[cfg(test)]
mod tests {
    use expect_test::{expect, Expect};

    use crate::translate_program;

    use tig_syntax::parse_str;

    fn check(program: &str, expected: Expect) {
        let (_, p) = parse_str(program);
        assert_eq!(p.errors, vec![]);
        let result = translate_program(p.program.expect("Should have compiled"));
        assert_eq!(result.errors, vec![]);
        expected.assert_debug_eq(&result.expty);
    }

    fn check_err(program: &str, expected: Vec<Expect>) {
        let (_, p) = parse_str(program);
        assert_eq!(p.errors, vec![]);
        let result = translate_program(p.program.expect("Should have compiled"));
        for (r, e) in result.errors.iter().zip(expected.iter()) {
            e.assert_eq(&format!("{}", r));
        }
        assert_eq!(result.errors.len(), expected.len());
    }

    #[test]
    fn test_tyc_variable_declaration() {
        check(
            "let var a := 1 in a end",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Int,
                }
            "#]],
        );

        check(
            "let var a: int := 1 var b := a in b end",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Int,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_function_declaration() {
        check(
            r#"
            let
                function add(x: int, y: int): int = x + y
            in
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

        check(
            r#"
            let
                function a() = b()
                function b() = a()
            in
                a()
            end
            "#,
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Unit,
                }
            "#]],
        );

        check(
            r#"
            let
                function a(c: int): int = b(c - 1)
                function b(d: int): int = a(d + 1)
            in
                a(1)
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
    fn test_tyc_error_variable_declaration() {
        check_err(
            "let var a: string := 1 var b: unit := \"hi\" in a end",
            vec![
                expect![[r#"(21, 22): Expected type 'string', got 'int'"#]],
                expect![[r#"(38, 42): Expected type 'unit', got 'string'"#]],
            ],
        );

        check_err(
            "let var a := 1 var b: string := a in a end",
            vec![expect![[r#"(32, 33): Expected type 'string', got 'int'"#]]],
        );
    }

    #[test]
    fn test_tyc_error_function_declaration() {
        check_err(
            r#"
            let
                function a(c: int): int = b()
                function b(d: int, e: string): string = a()
            in
                b(a())
            end
            "#,
            vec![
                expect![[r#"(59, 62): Function 'b' expects 2 arguments, 0 given"#]],
                expect![[r#"(59, 62): Expected function to return 'int', got 'string'"#]],
                expect![[r#"(119, 122): Function 'a' expects 1 argument, 0 given"#]],
                expect![[r#"(119, 122): Expected function to return 'string', got 'int'"#]],
                expect![[r#"(156, 159): Function 'a' expects 1 argument, 0 given"#]],
                expect![[r#"(154, 160): Function 'b' expects 2 arguments, 1 given"#]],
            ],
        );
    }
}
