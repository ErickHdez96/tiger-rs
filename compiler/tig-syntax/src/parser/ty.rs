use crate::{
    ast,
    lexer::{Token, TokenKind},
    T,
};

use super::{PResult, Parser, TYPE_START_TOKENS};

impl<'s> Parser<'s> {
    pub(super) fn parse_type(&mut self) -> PResult<ast::Type> {
        match self.peek() {
            Token {
                kind: TokenKind::Id(id),
                span,
            } => {
                let ty = ast::Type {
                    span: *span,
                    kind: ast::TypeKind::Id(id.clone()), // SmolStr clone O(1)
                };
                self.next();
                Ok(ty)
            }

            Token {
                kind: T!['{'],
                span,
            } => {
                let span = *span;
                self.next();
                let tyfields = self.parse_ty_fields()?;
                let end = self.expect(&T!['}'])?.span;
                Ok(ast::Type {
                    span: span.extend(end),
                    kind: ast::TypeKind::Record(tyfields),
                })
            }

            Token {
                kind: T![array],
                span,
            } => {
                let span = *span;
                self.next();
                self.expect(&T![of])?;
                let ty = self.expect_ident()?;

                Ok(ast::Type {
                    span: span.extend(ty.span),
                    kind: ast::TypeKind::Array(ty),
                })
            }

            _ => {
                self.expected_one_of(&TYPE_START_TOKENS);
                Err(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use expect_test::{expect, Expect};

    use super::super::*;

    fn check(program: &str, expected: Expect) {
        let (_, p) = parse_str(program);
        assert_eq!(p.errors, vec![], "Should have compiled without errors");
        expected.assert_debug_eq(&p.program.expect("to generate a program"));
    }

    #[test]
    fn test_type_id() {
        check(
            "type my_int = int",
            expect![[r#"
                0..17: Decs
                  0..17: TypeDecs
                    0..17: TypeDec
                      5..11: TypeName
                        5..11: Ident(my_int)
                      14..17: Type
                        14..17: TypeId(int)
            "#]],
        );
    }

    #[test]
    fn test_type_record() {
        check(
            "type span = { lo: int, hi: int }",
            expect![[r#"
                0..32: Decs
                  0..32: TypeDecs
                    0..32: TypeDec
                      5..9: TypeName
                        5..9: Ident(span)
                      12..32: Type
                        12..32: Record
                          14..16: Name(lo) - 18..21: Type(int)
                          23..25: Name(hi) - 27..30: Type(int)
            "#]],
        );
    }

    #[test]
    fn test_type_array() {
        check(
            "type my_int = array of int",
            expect![[r#"
                0..26: Decs
                  0..26: TypeDecs
                    0..26: TypeDec
                      5..11: TypeName
                        5..11: Ident(my_int)
                      14..26: Type
                        14..26: TypeArray(int)
            "#]],
        );
    }
}
