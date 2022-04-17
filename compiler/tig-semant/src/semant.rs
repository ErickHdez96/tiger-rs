mod expr;
mod stmt;

use std::{marker::PhantomData, rc::Rc};

use crate::{
    frame::Fragment,
    translate::{self as tx, level::Access, simple_var, Level, TExpr},
    Frame, RType, RecordField, Type,
};
use tig_common::{temp::Label, Env, SmolStr, Span};
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
enum ValEntry<F: Frame> {
    Variable {
        access: Access<F>,
        ty: RType,
    },
    Function {
        /// Primitive functions don't require a static link.
        is_primitive: bool,
        level: Level<F>,
        label: Label,
        /// The parameters to the function.
        formals: Vec<RType>,
        result: RType,
    },
}

//#[derive(Clone, PartialEq, Eq)]
//pub struct ExpResult {
//    ty: RType,
//    exp: Box<ir::Expr>,
//}

pub struct ExpTy {
    ty: RType,
    exp: TExpr,
}

//impl fmt::Debug for ExpResult {
//    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//        if f.alternate() {
//            let width = f.width().unwrap_or_default();
//            let padding = " ".repeat(width);
//            write!(
//                f,
//                "{}Type({})\n\
//                 {}Expr\n{:#width$?}",
//                padding,
//                self.ty,
//                padding,
//                self.exp,
//                width = width + 2,
//            )
//        } else {
//            f.debug_struct("ExpTy")
//                .field("ty", &self.ty)
//                .field("exp", &self.exp)
//                .finish()
//        }
//    }
//}

type VEnv<'env, F> = Env<'env, SmolStr, ValEntry<F>>;
type TEnv<'env> = Env<'env, SmolStr, RType>;

#[derive(Debug)]
struct Translator<F: Frame> {
    /// Stack holding the end label of the last enclosing loop, used for break exprs.
    loop_stack: Vec<Label>,
    errors: Vec<SpannedError>,
    current_level: Level<F>,
    has_main: bool,
    fragments: Vec<Fragment<F>>,
    _f: PhantomData<F>,
}

impl<F: Frame> Default for Translator<F> {
    fn default() -> Self {
        Self {
            loop_stack: vec![],
            errors: vec![],
            current_level: Level::<F>::outermost(),
            has_main: false,
            fragments: vec![],
            _f: PhantomData,
        }
    }
}

#[derive(Debug)]
pub struct TranslateResult<F: Frame> {
    pub errors: Vec<SpannedError>,
    pub fragments: Vec<Fragment<F>>,
}

/// Entry point to semantic analysis.
pub fn translate_program<F: Frame>(program: ast::Program) -> TranslateResult<F> {
    let mut translator = Translator::<F>::default();
    let base_venv = VEnv::new();
    let base_tenv = base_tenv();

    match program {
        ast::Program::Expr(expr) => {
            translator.current_level = translator
                .current_level
                .new_level(Label::raw("_main"), vec![]);
            translator.has_main = true;
            let result = translator.translate_expr(expr, &base_venv, &base_tenv);
            tx::fn_::<F>(
                result.exp.span(),
                &mut translator.fragments,
                &translator.current_level,
                result.exp,
            );
            TranslateResult {
                errors: translator.errors,
                fragments: translator.fragments,
            }
        }
        ast::Program::Decs(decs) => {
            translator.translate_decs(decs, &base_venv, &base_tenv);
            TranslateResult {
                fragments: translator.fragments,
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

impl<F: Frame> Translator<F> {
    /// Translates an LValue, looking it up in `venv`.
    fn translate_var(&mut self, var: ast::LValue, venv: &VEnv<F>, tenv: &TEnv) -> ExpTy {
        let span = var.span();
        match var {
            ast::LValue::Ident(id) => match venv.look(&id.value) {
                Some(ValEntry::Variable { access, ty }) => ExpTy {
                    exp: simple_var(span, access, &self.current_level),
                    ty: self.actual_ty(ty, span, tenv),
                },
                Some(ValEntry::Function { .. }) => {
                    E!(
                        self,
                        span,
                        "Expected a variable, got a function - '{}'",
                        id.value
                    );
                    ExpTy {
                        exp: TExpr::hole(),
                        ty: Type::hole(),
                    }
                }
                None => {
                    E!(self, span, "Undefined variable '{}'", id.value);
                    ExpTy {
                        exp: TExpr::hole(),
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
                                    exp: tx::field_access::<F>(
                                        span,
                                        object_expty.exp,
                                        &f.name,
                                        fields,
                                    ),
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
                            exp: TExpr::hole(),
                            ty: Type::hole(),
                        }
                    }
                    Type::Hole => ExpTy {
                        exp: TExpr::hole(),
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
                            exp: TExpr::hole(),
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
                            exp: tx::array_access::<F>(span, array_ty.exp, index_ty.exp),
                            ty: Rc::clone(ty),
                        }
                    }
                    Type::Hole => ExpTy {
                        exp: TExpr::hole(),
                        ty: array_ty.ty,
                    },
                    _ => {
                        E!(self, index_span, "Cannot index a non-array {}", array_ty.ty);
                        ExpTy {
                            exp: TExpr::hole(),
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
    use crate::frame::amd64::Amd64Frame;
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
    fn test_tyc_type_declaration() {
        check_fragments(
            "let type a = int var a: a := 1 in a end",
            vec![expect![[r#"
                    0..39: Procedure
                      Frame(_main) - 0
                      0..39: Move
                        0..39: Destination
                          0..39: Temp(rv)
                        0..39: Source
                          0..39: ESeq
                            17..30: Stmt
                              17..30: Move
                                17..30: Destination
                                  17..30: Temp(0)
                                29..30: Source
                                  29..30: Const(1)
                            34..35: Expr
                              34..35: Temp(0)
                "#]]],
        );

        check_fragments(
            "let type b = a type a = int var a: b := 1 in a end",
            vec![expect![[r#"
                    0..50: Procedure
                      Frame(_main) - 0
                      0..50: Move
                        0..50: Destination
                          0..50: Temp(rv)
                        0..50: Source
                          0..50: ESeq
                            28..41: Stmt
                              28..41: Move
                                28..41: Destination
                                  28..41: Temp(1)
                                40..41: Source
                                  40..41: Const(1)
                            45..46: Expr
                              45..46: Temp(1)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_records() {
        check_fragments(
            "let type meter = {m: int, n: int} in meter {m = 1, n = 2 + 3} end",
            vec![expect![[r#"
                    37..60: Procedure
                      Frame(_main) - 0
                      37..60: Move
                        37..60: Destination
                          37..60: Temp(rv)
                        37..60: Source
                          37..60: ESeq
                            37..60: Stmt
                              37..60: Seq
                                37..60: Stmt1
                                  37..60: Seq
                                    37..60: Stmt1
                                      37..60: Move
                                        37..60: Destination
                                          37..60: Temp(0)
                                        37..60: Source
                                          37..60: Call
                                            37..60: Function
                                              37..60: Name(malloc)
                                            37..60: Arguments
                                              37..60: Const(16)
                                    37..60: Stmt2
                                      37..60: Move
                                        37..60: Destination
                                          37..60: Mem
                                            37..60: Expr
                                              37..60: BinOp(+)
                                                37..60: Left
                                                  37..60: Temp(0)
                                                37..60: Right
                                                  37..60: Const(0)
                                        48..49: Source
                                          48..49: Const(1)
                                37..60: Stmt2
                                  37..60: Move
                                    37..60: Destination
                                      37..60: Mem
                                        37..60: Expr
                                          37..60: BinOp(+)
                                            37..60: Left
                                              37..60: Temp(0)
                                            37..60: Right
                                              37..60: Const(8)
                                    55..60: Source
                                      55..60: BinOp(+)
                                        55..56: Left
                                          55..56: Const(2)
                                        59..60: Right
                                          59..60: Const(3)
                            37..60: Expr
                              37..60: Temp(0)
                "#]]],
        );

        check_fragments(
            "let
                type meter = {m: int, n: int}
                var m := meter {m = 1, n = 10}
            in
                m.m;
                m.n
            end",
            vec![expect![[r#"
                    0..168: Procedure
                      Frame(_main) - 0
                      0..168: Move
                        0..168: Destination
                          0..168: Temp(rv)
                        0..168: Source
                          0..168: ESeq
                            66..96: Stmt
                              66..96: Move
                                66..96: Destination
                                  66..96: Temp(2)
                                75..95: Source
                                  75..95: ESeq
                                    75..95: Stmt
                                      75..95: Seq
                                        75..95: Stmt1
                                          75..95: Seq
                                            75..95: Stmt1
                                              75..95: Move
                                                75..95: Destination
                                                  75..95: Temp(1)
                                                75..95: Source
                                                  75..95: Call
                                                    75..95: Function
                                                      75..95: Name(malloc)
                                                    75..95: Arguments
                                                      75..95: Const(16)
                                            75..95: Stmt2
                                              75..95: Move
                                                75..95: Destination
                                                  75..95: Mem
                                                    75..95: Expr
                                                      75..95: BinOp(+)
                                                        75..95: Left
                                                          75..95: Temp(1)
                                                        75..95: Right
                                                          75..95: Const(0)
                                                86..87: Source
                                                  86..87: Const(1)
                                        75..95: Stmt2
                                          75..95: Move
                                            75..95: Destination
                                              75..95: Mem
                                                75..95: Expr
                                                  75..95: BinOp(+)
                                                    75..95: Left
                                                      75..95: Temp(1)
                                                    75..95: Right
                                                      75..95: Const(8)
                                            93..95: Source
                                              93..95: Const(10)
                                    75..95: Expr
                                      75..95: Temp(1)
                            128..152: Expr
                              128..152: ESeq
                                128..131: Stmt
                                  128..131: StmtExpr
                                    128..131: Mem
                                      128..131: Expr
                                        128..131: BinOp(+)
                                          128..129: Left
                                            128..129: Temp(2)
                                          128..131: Right
                                            128..131: Const(0)
                                149..152: Expr
                                  149..152: Mem
                                    149..152: Expr
                                      149..152: BinOp(+)
                                        149..150: Left
                                          149..150: Temp(2)
                                        149..152: Right
                                          149..152: Const(8)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_recursive_types() {
        check_fragments(
            r#"
            let
                type list = {head: int, tail: list}
                var l := list {head = 1, tail=list { head = 2, tail = nil}}
            in
                l.tail.tail
            end"#,
            vec![expect![[r#"
                    13..203: Procedure
                      Frame(_main) - 0
                      13..203: Move
                        13..203: Destination
                          13..203: Temp(rv)
                        13..203: Source
                          13..203: ESeq
                            85..144: Stmt
                              85..144: Move
                                85..144: Destination
                                  85..144: Temp(2)
                                94..143: Source
                                  94..143: ESeq
                                    94..143: Stmt
                                      94..143: Seq
                                        94..143: Stmt1
                                          94..143: Seq
                                            94..143: Stmt1
                                              94..143: Move
                                                94..143: Destination
                                                  94..143: Temp(1)
                                                94..143: Source
                                                  94..143: Call
                                                    94..143: Function
                                                      94..143: Name(malloc)
                                                    94..143: Arguments
                                                      94..143: Const(16)
                                            94..143: Stmt2
                                              94..143: Move
                                                94..143: Destination
                                                  94..143: Mem
                                                    94..143: Expr
                                                      94..143: BinOp(+)
                                                        94..143: Left
                                                          94..143: Temp(1)
                                                        94..143: Right
                                                          94..143: Const(0)
                                                107..108: Source
                                                  107..108: Const(1)
                                        94..143: Stmt2
                                          94..143: Move
                                            94..143: Destination
                                              94..143: Mem
                                                94..143: Expr
                                                  94..143: BinOp(+)
                                                    94..143: Left
                                                      94..143: Temp(1)
                                                    94..143: Right
                                                      94..143: Const(8)
                                            115..142: Source
                                              115..142: ESeq
                                                115..142: Stmt
                                                  115..142: Seq
                                                    115..142: Stmt1
                                                      115..142: Seq
                                                        115..142: Stmt1
                                                          115..142: Move
                                                            115..142: Destination
                                                              115..142: Temp(0)
                                                            115..142: Source
                                                              115..142: Call
                                                                115..142: Function
                                                                  115..142: Name(malloc)
                                                                115..142: Arguments
                                                                  115..142: Const(16)
                                                        115..142: Stmt2
                                                          115..142: Move
                                                            115..142: Destination
                                                              115..142: Mem
                                                                115..142: Expr
                                                                  115..142: BinOp(+)
                                                                    115..142: Left
                                                                      115..142: Temp(0)
                                                                    115..142: Right
                                                                      115..142: Const(0)
                                                            129..130: Source
                                                              129..130: Const(2)
                                                    115..142: Stmt2
                                                      115..142: Move
                                                        115..142: Destination
                                                          115..142: Mem
                                                            115..142: Expr
                                                              115..142: BinOp(+)
                                                                115..142: Left
                                                                  115..142: Temp(0)
                                                                115..142: Right
                                                                  115..142: Const(8)
                                                        139..142: Source
                                                          139..142: Const(0)
                                                115..142: Expr
                                                  115..142: Temp(0)
                                    94..143: Expr
                                      94..143: Temp(1)
                            176..187: Expr
                              176..187: Mem
                                176..187: Expr
                                  176..187: BinOp(+)
                                    176..182: Left
                                      176..182: Mem
                                        176..182: Expr
                                          176..182: BinOp(+)
                                            176..177: Left
                                              176..177: Temp(2)
                                            176..182: Right
                                              176..182: Const(8)
                                    176..187: Right
                                      176..187: Const(8)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_array() {
        check_fragments(
            "let type ints = array of int var a := ints [10] of 1 in a end",
            vec![expect![[r#"
                    0..61: Procedure
                      Frame(_main) - 0
                      0..61: Move
                        0..61: Destination
                          0..61: Temp(rv)
                        0..61: Source
                          0..61: ESeq
                            29..52: Stmt
                              29..52: Move
                                29..52: Destination
                                  29..52: Temp(2)
                                38..52: Source
                                  38..52: ESeq
                                    38..52: Stmt
                                      38..52: Seq
                                        38..52: Stmt1
                                          38..52: Seq
                                            38..52: Stmt1
                                              38..52: Move
                                                38..52: Destination
                                                  38..52: Temp(1)
                                                38..52: Source
                                                  38..52: BinOp(*)
                                                    44..46: Left
                                                      44..46: Const(10)
                                                    38..52: Right
                                                      38..52: Const(8)
                                            38..52: Stmt2
                                              38..52: Move
                                                38..52: Destination
                                                  38..52: Temp(0)
                                                38..52: Source
                                                  38..52: Call
                                                    38..52: Function
                                                      38..52: Name(malloc)
                                                    38..52: Arguments
                                                      38..52: Temp(1)
                                        38..52: Stmt2
                                          38..52: StmtExpr
                                            38..52: Call
                                              38..52: Function
                                                38..52: Name(initArray)
                                              38..52: Arguments
                                                38..52: Temp(0)
                                                38..52: Temp(1)
                                                51..52: Const(1)
                                    38..52: Expr
                                      38..52: Temp(0)
                            56..57: Expr
                              56..57: Temp(2)
                "#]]],
        );

        check_fragments(
            "let type ints = array of int var a := ints [10] of 3 + 4 in a[2 + 2] end",
            vec![expect![[r#"
                    0..72: Procedure
                      Frame(_main) - 0
                      0..72: Move
                        0..72: Destination
                          0..72: Temp(rv)
                        0..72: Source
                          0..72: ESeq
                            29..56: Stmt
                              29..56: Move
                                29..56: Destination
                                  29..56: Temp(5)
                                38..56: Source
                                  38..56: ESeq
                                    38..56: Stmt
                                      38..56: Seq
                                        38..56: Stmt1
                                          38..56: Seq
                                            38..56: Stmt1
                                              38..56: Move
                                                38..56: Destination
                                                  38..56: Temp(4)
                                                38..56: Source
                                                  38..56: BinOp(*)
                                                    44..46: Left
                                                      44..46: Const(10)
                                                    38..56: Right
                                                      38..56: Const(8)
                                            38..56: Stmt2
                                              38..56: Move
                                                38..56: Destination
                                                  38..56: Temp(3)
                                                38..56: Source
                                                  38..56: Call
                                                    38..56: Function
                                                      38..56: Name(malloc)
                                                    38..56: Arguments
                                                      38..56: Temp(4)
                                        38..56: Stmt2
                                          38..56: StmtExpr
                                            38..56: Call
                                              38..56: Function
                                                38..56: Name(initArray)
                                              38..56: Arguments
                                                38..56: Temp(3)
                                                38..56: Temp(4)
                                                51..56: BinOp(+)
                                                  51..52: Left
                                                    51..52: Const(3)
                                                  55..56: Right
                                                    55..56: Const(4)
                                    38..56: Expr
                                      38..56: Temp(3)
                            60..67: Expr
                              60..67: Mem
                                60..67: Expr
                                  60..67: BinOp(+)
                                    60..61: Left
                                      60..61: Temp(5)
                                    60..67: Right
                                      60..67: BinOp(*)
                                        62..67: Left
                                          62..67: BinOp(+)
                                            62..63: Left
                                              62..63: Const(2)
                                            66..67: Right
                                              66..67: Const(2)
                                        60..67: Right
                                          60..67: Const(8)
                "#]]],
        );

        check_fragments(
            "
            let
                type ints = array of int
                var a := ints [5] of 0
                var b := ints [5] of 0
            in
                a := b
            end
            ",
            vec![expect![[r#"
                    13..189: Procedure
                      Frame(_main) - 0
                      13..189: Move
                        13..189: Destination
                          13..189: Temp(rv)
                        13..189: Source
                          13..189: ESeq
                            13..189: Stmt
                              13..189: Seq
                                74..96: Stmt1
                                  74..96: Move
                                    74..96: Destination
                                      74..96: Temp(8)
                                    83..96: Source
                                      83..96: ESeq
                                        83..96: Stmt
                                          83..96: Seq
                                            83..96: Stmt1
                                              83..96: Seq
                                                83..96: Stmt1
                                                  83..96: Move
                                                    83..96: Destination
                                                      83..96: Temp(7)
                                                    83..96: Source
                                                      83..96: BinOp(*)
                                                        89..90: Left
                                                          89..90: Const(5)
                                                        83..96: Right
                                                          83..96: Const(8)
                                                83..96: Stmt2
                                                  83..96: Move
                                                    83..96: Destination
                                                      83..96: Temp(6)
                                                    83..96: Source
                                                      83..96: Call
                                                        83..96: Function
                                                          83..96: Name(malloc)
                                                        83..96: Arguments
                                                          83..96: Temp(7)
                                            83..96: Stmt2
                                              83..96: StmtExpr
                                                83..96: Call
                                                  83..96: Function
                                                    83..96: Name(initArray)
                                                  83..96: Arguments
                                                    83..96: Temp(6)
                                                    83..96: Temp(7)
                                                    95..96: Const(0)
                                        83..96: Expr
                                          83..96: Temp(6)
                                113..135: Stmt2
                                  113..135: Move
                                    113..135: Destination
                                      113..135: Temp(11)
                                    122..135: Source
                                      122..135: ESeq
                                        122..135: Stmt
                                          122..135: Seq
                                            122..135: Stmt1
                                              122..135: Seq
                                                122..135: Stmt1
                                                  122..135: Move
                                                    122..135: Destination
                                                      122..135: Temp(10)
                                                    122..135: Source
                                                      122..135: BinOp(*)
                                                        128..129: Left
                                                          128..129: Const(5)
                                                        122..135: Right
                                                          122..135: Const(8)
                                                122..135: Stmt2
                                                  122..135: Move
                                                    122..135: Destination
                                                      122..135: Temp(9)
                                                    122..135: Source
                                                      122..135: Call
                                                        122..135: Function
                                                          122..135: Name(malloc)
                                                        122..135: Arguments
                                                          122..135: Temp(10)
                                            122..135: Stmt2
                                              122..135: StmtExpr
                                                122..135: Call
                                                  122..135: Function
                                                    122..135: Name(initArray)
                                                  122..135: Arguments
                                                    122..135: Temp(9)
                                                    122..135: Temp(10)
                                                    134..135: Const(0)
                                        122..135: Expr
                                          122..135: Temp(9)
                            167..173: Expr
                              167..173: ESeq
                                167..173: Stmt
                                  167..173: Move
                                    167..168: Destination
                                      167..168: Temp(8)
                                    172..173: Source
                                      172..173: Temp(11)
                                167..173: Expr
                                  167..173: Const(0)
                "#]]],
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
        check_fragments(
            r#"
            let
                type myint = int
                type arrtype = array of myint

                var arr1: arrtype := arrtype [10] of 0
            in
                arr1
            end
            "#,
            vec![expect![[r#"
                    13..203: Procedure
                      Frame(_main) - 0
                      13..203: Move
                        13..203: Destination
                          13..203: Temp(rv)
                        13..203: Source
                          13..203: ESeq
                            113..151: Stmt
                              113..151: Move
                                113..151: Destination
                                  113..151: Temp(2)
                                134..151: Source
                                  134..151: ESeq
                                    134..151: Stmt
                                      134..151: Seq
                                        134..151: Stmt1
                                          134..151: Seq
                                            134..151: Stmt1
                                              134..151: Move
                                                134..151: Destination
                                                  134..151: Temp(1)
                                                134..151: Source
                                                  134..151: BinOp(*)
                                                    143..145: Left
                                                      143..145: Const(10)
                                                    134..151: Right
                                                      134..151: Const(8)
                                            134..151: Stmt2
                                              134..151: Move
                                                134..151: Destination
                                                  134..151: Temp(0)
                                                134..151: Source
                                                  134..151: Call
                                                    134..151: Function
                                                      134..151: Name(malloc)
                                                    134..151: Arguments
                                                      134..151: Temp(1)
                                        134..151: Stmt2
                                          134..151: StmtExpr
                                            134..151: Call
                                              134..151: Function
                                                134..151: Name(initArray)
                                              134..151: Arguments
                                                134..151: Temp(0)
                                                134..151: Temp(1)
                                                150..151: Const(0)
                                    134..151: Expr
                                      134..151: Temp(0)
                            183..187: Expr
                              183..187: Temp(2)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_bug_2() {
        // It was assiging the type nil to b.
        check_fragments(
            r#"
            let
                type rectype = {name: string, id: int}
                var b: rectype := nil
            in
                b := nil
            end
            "#,
            vec![expect![[r#"
                    13..165: Procedure
                      Frame(_main) - 0
                      13..165: Move
                        13..165: Destination
                          13..165: Temp(rv)
                        13..165: Source
                          13..165: ESeq
                            88..109: Stmt
                              88..109: Move
                                88..109: Destination
                                  88..109: Temp(0)
                                106..109: Source
                                  106..109: Const(0)
                            141..149: Expr
                              141..149: ESeq
                                141..149: Stmt
                                  141..149: Move
                                    141..142: Destination
                                      141..142: Temp(0)
                                    146..149: Source
                                      146..149: Const(0)
                                141..149: Expr
                                  141..149: Const(0)
                "#]]],
        );
    }

    #[test]
    fn test_tyc_bug_3() {
        // The ir generated is too large, and I ain't manually checking that.
        // It was complaining arr2[3] did not have a field named 'name'
        let (_, p) = parse_str(
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
        );
        assert_eq!(p.errors, vec![]);
        let result = translate_program::<Amd64Frame>(p.program.expect("Should have compiled"));
        assert_eq!(result.errors, vec![]);
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
