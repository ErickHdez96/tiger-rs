use std::rc::Rc;

use tig_common::{temp::Label, Span};
use tig_error::SpannedError;
use tig_syntax::ast;

use crate::{
    translate::{self as tx, TExpr},
    Frame, RType, Type,
};

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

impl<F: Frame> Translator<F> {
    /// Translates a list of declarations, creating new value and type environments and returning
    /// them.
    pub(super) fn translate_decs<'venv, 'tenv>(
        &mut self,
        decs: Vec<ast::Dec>,
        venv: &'venv VEnv<'venv, F>,
        tenv: &'tenv TEnv<'tenv>,
    ) -> (VEnv<'venv, F>, TEnv<'tenv>, Vec<TExpr>) {
        let mut venv = venv.new_child();
        let mut tenv = tenv.new_child();
        let mut stmts = vec![];

        for dec in decs {
            if let Some(stmt) = self.translate_dec(dec, &mut venv, &mut tenv) {
                stmts.push(stmt);
            }
        }

        (venv, tenv, stmts)
    }

    /// Translates a declaration, modifying `venv` and `tenv` in place.
    fn translate_dec(
        &mut self,
        dec: ast::Dec,
        venv: &mut VEnv<F>,
        tenv: &mut TEnv,
    ) -> Option<TExpr> {
        let ast::Dec {
            kind: dec_kind,
            span,
        } = dec;
        match dec_kind {
            ast::DecKind::Type(typedecs) => {
                self.translate_typedecs(span, typedecs, tenv);
                None
            }

            ast::DecKind::Variable {
                name,
                escape,
                ty,
                value,
            } => {
                let value_span = value.span;
                let value = self.translate_expr(*value, venv, tenv);
                let access = self.current_level.alloc_local(escape);
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
                venv.enter(
                    name.value,
                    ValEntry::Variable {
                        access: access.clone(),
                        ty,
                    },
                );
                Some(tx::var_dec::<F>(span, &access, value.exp))
            }

            ast::DecKind::Function(funcs) => {
                self.translate_functions(funcs, venv, tenv);
                None
            }

            ast::DecKind::Primitive {
                name,
                parameters,
                ret_ty,
            } => {
                self.translate_primitive(name, parameters, ret_ty, venv, tenv);
                None
            }
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

    fn translate_functions(
        &mut self,
        funcs: Vec<ast::FunctionDec>,
        venv: &mut VEnv<F>,
        tenv: &mut TEnv,
    ) {
        let mut processed_funcs = vec![];

        for f in funcs {
            let ast::FunctionDec {
                span,
                name,
                parameters,
                ret_ty,
                body,
            } = f;

            let mut processed_params = vec![];
            let mut formals = vec![];
            let mut escapes = vec![true]; // Static link
            for p in parameters {
                let ast::Field { name, ty, escape } = p;
                let p_ty = self.resolve_ty(&ty.value, ty.span, tenv, true);
                processed_params.push((name, Rc::clone(&p_ty)));
                formals.push(p_ty);
                escapes.push(escape);
            }

            let result = ret_ty
                .map(|ty| self.resolve_ty(&ty.value, ty.span, tenv, true))
                .unwrap_or_else(Type::unit);

            let mut generate = true;
            let mut label = Label::named(name.value.as_str());
            if name.value == "_main" {
                if self.has_main {
                    E!(self, name.span, "Cannot redeclare _main function.",);
                    generate = false;
                } else {
                    self.has_main = true;
                    label = Label::raw("_main");
                }
            }
            let level = self.current_level.new_level(label.clone(), escapes);

            if generate {
                venv.enter(
                    name.value.clone(),
                    ValEntry::Function {
                        is_primitive: false,
                        level: level.clone(),
                        label,
                        formals,
                        result: Rc::clone(&result),
                    },
                );
            }

            processed_funcs.push((processed_params, body, result, level, span));
        }

        for (params, body, expected_result, level, span) in processed_funcs {
            let mut venv = venv.new_child();

            // Skip the static link
            for ((name, ty), access) in params.into_iter().zip(level.formals().into_iter().skip(1))
            {
                venv.enter(name.value, ValEntry::Variable { access, ty });
            }

            let current_level = std::mem::replace(&mut self.current_level, level);
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
            tx::fn_::<F>(span, &mut self.fragments, &self.current_level, body_ty.exp);
            self.current_level = current_level;
        }
    }

    fn translate_primitive(
        &mut self,
        name: ast::Ident,
        parameters: Vec<ast::TyField>,
        ret_ty: Option<ast::Ident>,
        venv: &mut VEnv<F>,
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

        if name.value == "_main" {
            E!(self, name.span, "Cannot declare a primitive as _main.",);
        } else {
            let label = Label::raw(name.value.as_str());
            let level = self
                .current_level
                .new_level(label.clone(), vec![false; formals.len()]);
            venv.enter(
                name.value,
                ValEntry::Function {
                    is_primitive: true,
                    level,
                    label,
                    formals,
                    result,
                },
            );
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
    fn test_tyc_variable_declaration() {
        check_fragments(
            "let var a := 1 in a end",
            vec![expect![[r#"
                    0..23: Procedure
                      Frame(_main) - 0
                      0..23: Move
                        0..23: Destination
                          0..23: Temp(rv)
                        0..23: Source
                          0..23: ESeq
                            4..14: Stmt
                              4..14: Move
                                4..14: Destination
                                  4..14: Temp(0)
                                13..14: Source
                                  13..14: Const(1)
                            18..19: Expr
                              18..19: Temp(0)
                "#]]],
        );

        check_fragments(
            "let var a: int := 2 var b := a in b end",
            vec![expect![[r#"
                    0..39: Procedure
                      Frame(_main) - 0
                      0..39: Move
                        0..39: Destination
                          0..39: Temp(rv)
                        0..39: Source
                          0..39: ESeq
                            0..39: Stmt
                              0..39: Seq
                                4..19: Stmt1
                                  4..19: Move
                                    4..19: Destination
                                      4..19: Temp(1)
                                    18..19: Source
                                      18..19: Const(2)
                                20..30: Stmt2
                                  20..30: Move
                                    20..30: Destination
                                      20..30: Temp(2)
                                    29..30: Source
                                      29..30: Temp(1)
                            34..35: Expr
                              34..35: Temp(2)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_function_declaration() {
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
                          Reg(Temp(0))
                          Reg(Temp(1))
                      33..74: Move
                        33..74: Destination
                          33..74: Temp(rv)
                        69..74: Source
                          69..74: BinOp(+)
                            69..70: Left
                              69..70: Temp(0)
                            73..74: Right
                              73..74: Temp(1)
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

        check_fragments(
            r#"
            let
                function a() = b()
                function b() = a()
            in
                a()
            end
            "#,
            vec![
                expect![[r#"
                33..51: Procedure
                  Frame(a1) - -8
                    Formals
                      InFrame(-8)
                  33..51: Move
                    33..51: Destination
                      33..51: Temp(rv)
                    48..51: Source
                      48..51: Call
                        48..51: Function
                          48..51: Name(b2)
                        48..51: Arguments
                          48..51: Mem
                            48..51: Expr
                              48..51: BinOp(-)
                                48..51: Left
                                  48..51: Temp(fp)
                                48..51: Right
                                  48..51: Const(8)
                "#]],
                expect![[r#"
                68..86: Procedure
                  Frame(b2) - -8
                    Formals
                      InFrame(-8)
                  68..86: Move
                    68..86: Destination
                      68..86: Temp(rv)
                    83..86: Source
                      83..86: Call
                        83..86: Function
                          83..86: Name(a1)
                        83..86: Arguments
                          83..86: Mem
                            83..86: Expr
                              83..86: BinOp(-)
                                83..86: Left
                                  83..86: Temp(fp)
                                83..86: Right
                                  83..86: Const(8)
                "#]],
                expect![[r#"
                    118..121: Procedure
                      Frame(_main) - 0
                      118..121: Move
                        118..121: Destination
                          118..121: Temp(rv)
                        118..121: Source
                          118..121: Call
                            118..121: Function
                              118..121: Name(a1)
                            118..121: Arguments
                              118..121: Temp(fp)
                "#]],
            ],
        );

        check_fragments(
            r#"
            let
                function a(c: int): int = b(c - 1)
                function b(d: int): int = a(d + 1)
            in
                a(1)
            end
            "#,
            vec![
                expect![[r#"
                    33..67: Procedure
                      Frame(a3) - -8
                        Formals
                          InFrame(-8)
                          Reg(Temp(2))
                      33..67: Move
                        33..67: Destination
                          33..67: Temp(rv)
                        59..67: Source
                          59..67: Call
                            59..67: Function
                              59..67: Name(b4)
                            59..66: Arguments
                              59..67: Mem
                                59..67: Expr
                                  59..67: BinOp(-)
                                    59..67: Left
                                      59..67: Temp(fp)
                                    59..67: Right
                                      59..67: Const(8)
                              61..66: BinOp(-)
                                61..62: Left
                                  61..62: Temp(2)
                                65..66: Right
                                  65..66: Const(1)
                "#]],
                expect![[r#"
                    84..118: Procedure
                      Frame(b4) - -8
                        Formals
                          InFrame(-8)
                          Reg(Temp(3))
                      84..118: Move
                        84..118: Destination
                          84..118: Temp(rv)
                        110..118: Source
                          110..118: Call
                            110..118: Function
                              110..118: Name(a3)
                            110..117: Arguments
                              110..118: Mem
                                110..118: Expr
                                  110..118: BinOp(-)
                                    110..118: Left
                                      110..118: Temp(fp)
                                    110..118: Right
                                      110..118: Const(8)
                              112..117: BinOp(+)
                                112..113: Left
                                  112..113: Temp(3)
                                116..117: Right
                                  116..117: Const(1)
                "#]],
                expect![[r#"
                    150..154: Procedure
                      Frame(_main) - 0
                      150..154: Move
                        150..154: Destination
                          150..154: Temp(rv)
                        150..154: Source
                          150..154: Call
                            150..154: Function
                              150..154: Name(a3)
                            150..153: Arguments
                              150..154: Temp(fp)
                              152..153: Const(1)
                "#]],
            ],
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

    #[test]
    fn test_tyc_error_main() {
        check_err(
            r#"
            let
                primitive _main()
                function _main() = ()
            in
                nil
            end
            "#,
            vec![
                expect![[r#"(43, 48): Cannot declare a primitive as _main."#]],
                expect![[r#"(76, 81): Cannot redeclare _main function."#]],
            ],
        );
    }
}
