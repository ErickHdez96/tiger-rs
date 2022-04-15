mod expr;
mod stmt;

use std::rc::Rc;

use crate::{RType, RecordField, Type};
use tig_common::{Env, SmolStr, Span};
use tig_error::SpannedError;
use tig_syntax::ast;

/// Pushes a SpannedError to self.errors.
macro_rules! E {
    ($translator:expr, $span:expr, $($error:expr),+ $(,)?) => {
        $translator.errors.push(SpannedError::new(
            format!($($error),+),
            $span,
        ))
    };
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ValEntry {
    Variable {
        ty: RType,
    },
    Function {
        /// The parameters to the function.
        formals: Vec<RType>,
        result: RType,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpTy {
    exp: (),
    ty: RType,
}

type VEnv<'env> = Env<'env, SmolStr, ValEntry>;
type TEnv<'env> = Env<'env, SmolStr, RType>;

#[derive(Debug, Default)]
struct Translator {
    /// Counter for holding if the current translation is inside of a loop, used for translating
    /// break expressions.
    loop_stack: usize,
    errors: Vec<SpannedError>,
}

#[derive(Debug)]
pub struct TranslateResult {
    pub expty: ExpTy,
    pub errors: Vec<SpannedError>,
}

/// Entry point to semantic analysis.
pub fn translate_program(program: ast::Program) -> TranslateResult {
    let mut translator = Translator::default();
    let base_venv = VEnv::new();
    let base_tenv = base_tenv();

    match program {
        ast::Program::Expr(expr) => {
            let result = translator.translate_expr(expr, &base_venv, &base_tenv);
            TranslateResult {
                expty: result,
                errors: translator.errors,
            }
        }
        ast::Program::Decs(decs) => {
            translator.translate_decs(decs, &base_venv, &base_tenv);
            TranslateResult {
                expty: ExpTy {
                    exp: (),
                    ty: Type::unit(),
                },
                errors: translator.errors,
            }
        }
    }
}

pub fn base_tenv() -> TEnv<'static> {
    let mut tenv = TEnv::new();

    tenv.enter("int".into(), Type::int());
    tenv.enter("string".into(), Type::string());
    tenv.enter("unit".into(), Type::unit());

    tenv
}

impl Translator {
    /// Translates an LValue, looking it up in `venv`.
    fn translate_var(&mut self, var: ast::LValue, venv: &VEnv, tenv: &TEnv) -> ExpTy {
        match var {
            ast::LValue::Ident(id) => match venv.look(&id.value) {
                Some(ValEntry::Variable { ty }) => ExpTy {
                    exp: (),
                    ty: self.actual_ty(ty, id.span, tenv),
                },
                Some(ValEntry::Function { .. }) => {
                    E!(
                        self,
                        id.span,
                        "Expected a variable, got a function - '{}'",
                        id.value
                    );
                    ExpTy {
                        exp: (),
                        ty: Type::hole(),
                    }
                }
                None => {
                    E!(self, id.span, "Undefined variable '{}'", id.value);
                    ExpTy {
                        exp: (),
                        ty: Type::hole(),
                    }
                }
            },

            ast::LValue::FieldAccess(object, field) => {
                let object_span = object.span();
                let object_expty = self.translate_var(*object, venv, tenv);

                match &*self.actual_ty(&object_expty.ty, object_span, tenv) {
                    Type::Record { fields, .. } => {
                        for f in fields {
                            if f.name.value == field.value {
                                return ExpTy {
                                    exp: (),
                                    ty: Rc::clone(&f.ty),
                                };
                            }
                        }
                        E!(
                            self,
                            field.span,
                            "Record {} does not have field '{}'",
                            object_expty.ty,
                            field.value
                        );
                        ExpTy {
                            exp: (),
                            ty: Type::hole(),
                        }
                    }
                    Type::Hole => ExpTy {
                        exp: (),
                        ty: object_expty.ty,
                    },
                    ty => {
                        E!(
                            self,
                            field.span,
                            "Cannot access field '{}' of non-record {}",
                            field.value,
                            ty
                        );
                        ExpTy {
                            exp: (),
                            ty: Type::hole(),
                        }
                    }
                }
            }

            ast::LValue::ArrayAccess(array, index) => {
                let array_span = array.span();
                let index_span = index.span;

                let array_ty = self.translate_var(*array, venv, tenv);
                match &*self.actual_ty(&array_ty.ty, array_span, tenv) {
                    Type::Array { ty, .. } => {
                        let index_ty = self.translate_expr(*index, venv, tenv);
                        self.expect_int(&index_ty, index_span, tenv);
                        ExpTy {
                            exp: (),
                            ty: Rc::clone(ty),
                        }
                    }
                    Type::Hole => ExpTy {
                        exp: (),
                        ty: array_ty.ty,
                    },
                    _ => {
                        E!(self, array_span, "Cannot index a non-array {}", array_ty.ty);
                        ExpTy {
                            exp: (),
                            ty: Type::hole(),
                        }
                    }
                }
            }
        }
    }

    /// Translates a type as defind in the AST into a proper type.
    /// Types in the ast only really appear on the right of a type declaration.
    /// Types in any other place are only an identifier, and should use
    /// `Self::resolve_ty`.
    fn translate_ty(&mut self, ty: ast::Type, tenv: &TEnv) -> RType {
        let ast::Type {
            span,
            kind: ty_kind,
        } = ty;
        match ty_kind {
            ast::TypeKind::Id(id) => match tenv.look(&id) {
                Some(ty) => Rc::clone(ty),
                None => {
                    E!(self, span, "Undefined type '{}'", id);
                    Type::hole()
                }
            },
            ast::TypeKind::Record(fields) => {
                let mut record_fields = vec![];

                for f in fields {
                    let field = RecordField {
                        name: f.name,
                        ty: self.resolve_ty(&f.ty.value, f.ty.span, tenv, false),
                    };
                    record_fields.push(field);
                }

                Type::record(record_fields)
            }
            ast::TypeKind::Array(ty) => {
                let ty = self.resolve_ty(&ty.value, ty.span, tenv, false);
                Type::array(ty)
            }
        }
    }

    /// Pushes an error if the `expty` is not of type `int`, otherwise does nothing.
    fn expect_int(&mut self, expty: &ExpTy, span: Span, tenv: &TEnv) {
        match &*self.actual_ty(&expty.ty, span, tenv) {
            Type::Int | Type::Hole => {}
            ty => E!(self, span, "Expected an int, got '{}'", ty),
        }
    }

    /// Pushes an error if the `expty` is not of type `unit`, otherwise does nothing.
    fn expect_unit(&mut self, expty: &ExpTy, span: Span, tenv: &TEnv) {
        match &*self.actual_ty(&expty.ty, span, tenv) {
            Type::Unit | Type::Hole => {}
            ty => E!(self, span, "Expected no value, got '{}'", ty),
        }
    }

    /// Resolves type-id's into actual types, calling `Self::actual_ty` before returning the
    /// result. If the type doesn't exist, an error is pushed and a `Type::Hole` is returned.
    fn resolve_ty(
        &mut self,
        type_name: &SmolStr,
        span: Span,
        tenv: &TEnv,
        get_actual_type: bool,
    ) -> RType {
        tenv.look(type_name)
            .map(Rc::clone)
            .map(|ty| {
                if get_actual_type {
                    self.actual_ty(&ty, span, tenv)
                } else {
                    ty
                }
            })
            .unwrap_or_else(|| {
                E!(self, span, "Undefined type '{}'", type_name);
                Type::hole()
            })
    }

    /// Looks up the actual underlying type. It leaves the primitive types untouched, but it
    /// resolves `Type::Name` into a primitive, or pushes an error and returns a `Type::Hole` if
    /// the type name doesn't exist.
    fn actual_ty(&self, oty: &RType, span: Span, tenv: &TEnv) -> RType {
        match &**oty {
            Type::Name { name, ty } => match &*ty.borrow() {
                Some(ty) => self.actual_ty(ty, span, tenv),
                None => {
                    panic!(
                        "ICE: Tried to dereference an unitialized type - {}",
                        name.value
                    )
                }
            },
            _ => Rc::clone(oty),
        }
    }

    fn cmp_ty(&self, lty: &RType, lspan: Span, rty: &RType, rspan: Span, tenv: &TEnv) -> bool {
        match (
            &*self.actual_ty(lty, lspan, tenv),
            &*self.actual_ty(rty, rspan, tenv),
        ) {
            (Type::Int, Type::Int) => true,
            (Type::String, Type::String) => true,
            (
                Type::Record {
                    unique: lunique, ..
                },
                Type::Record {
                    unique: runique, ..
                },
            ) => lunique == runique,
            (
                Type::Array {
                    unique: lunique, ..
                },
                Type::Array {
                    unique: runique, ..
                },
            ) => lunique == runique,
            // Nil returns true when compared to a record,
            // but nil = nil is invalid
            (Type::Record { .. }, Type::Nil) => true,
            (Type::Nil, Type::Record { .. }) => true,
            (Type::Unit, Type::Unit) => true,
            (
                Type::Name { name, ty },
                Type::Name {
                    name: rname,
                    ty: rty,
                },
            ) => name == rname && ty == rty,
            (_, Type::Hole) | (Type::Hole, _) => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use expect_test::{expect, Expect};

    use super::*;
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
    fn test_tyc_type_declaration() {
        check(
            "let type a = int var a: a := 1 in a end",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Int,
                }
            "#]],
        );

        check(
            "let type b = a type a = int var a: b := 1 in a end",
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Int,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_recursive_types() {
        check(
            r#"
            let
                type list = {head: int, tail: list}
            in
                list {head = 1, tail=list { head = 2, tail = nil}};
                1
            end"#,
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Int,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_error_type_declaration() {
        check_err(
            "let type a = a in 3 end",
            vec![expect![[r#"(4, 14): Type declaration cycle not allowed"#]]],
        );

        check_err(
            "let type a = b type b = a in 3 end",
            vec![expect![[r#"(4, 25): Cycle between types detected"#]]],
        );
    }

    #[test]
    fn test_tyc_bug_1() {
        // It was complaining that 0 was not of type 'myint'.
        check(
            r#"
            let
                type myint = int
                type arrtype = array of myint

                var arr1: arrtype := arrtype [10] of 0
            in
                arr1
            end
            "#,
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Array {
                        ty: Name {
                            name: 38..43: Ident(myint),
                            ty: RefCell {
                                value: Some(
                                    Int,
                                ),
                            },
                        },
                        unique: Unique(
                            0,
                        ),
                    },
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_bug_2() {
        // It was assiging the type nil to b.
        check(
            r#"
            let
                type rectype = {name: string, id: int}
                var b: rectype := nil
            in
                b := nil
            end
            "#,
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Unit,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_bug_3() {
        // It was complaining arr2[3] did not have a field named 'name'
        check(
            r#"
            let
                type arrtype1 = array of int
                type rectype1 = {name: string, address: string, id: int, age: int}
                type arrtype2 = array of rectype1
                type rectype2 = {name: string, dates: arrtype1}

                type arrtype3 = array of string

                var arr1 := arrtype1 [10] of 0
                var arr2 := arrtype2 [5] of rectype1 {name = "aname", address = "somewhere", id = 0, age = 0}
                var arr3: arrtype3 := arrtype3 [100] of ""

                var rec1 := rectype1 {name = "Kapoios", address = "Kapou", id = 02432, age = 44}
                var rec2 := rectype2 {name = "Allos", dates = arrtype1 [3] of 1900}
            in
                arr1[0] := 1;
                arr1[9] := 3;
                arr2[3].name := "kati";
                arr2[1].age := 23;
                arr3[34] := "sfd";

                rec1.name := "sdf";
                rec2.dates[0] := 2323;
                rec2.dates[2] := 2323
            end
            "#,
            expect![[r#"
                ExpTy {
                    exp: (),
                    ty: Unit,
                }
            "#]],
        );
    }

    #[test]
    fn test_tyc_bug_4() {
        // It was compiling correctly
        check_err(
            r#"
            let
                type rectype = {name: string, id: int}

                var a := nil
            in
                a
            end
            "#,
            vec![expect![[
                r#"(98, 101): Cannot assign nil to a variable without a specified type"#
            ]]],
        );
    }
}
