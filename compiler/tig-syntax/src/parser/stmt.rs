use tig_error::ParserError;

use crate::{
    ast,
    lexer::{tokenize_source_file, LexerResult, TokenKind},
    T,
};

use super::{can_start_dec, PResult, Parser, DECLARATION_START_TOKENS};

impl<'s> Parser<'s> {
    pub(super) fn parse_decs(&mut self, end: &TokenKind) -> PResult<Vec<ast::Dec>> {
        let mut decs = vec![];

        while &self.peek().kind != end && !self.at_eof() {
            if !can_start_dec(&self.peek().kind) {
                self.expected_one_of(&DECLARATION_START_TOKENS);
                self.synchronize(&DECLARATION_START_TOKENS);
                continue;
            }

            if let Some(dec) = self.parse_dec()? {
                decs.push(dec);
            }
        }

        Ok(decs)
    }

    fn parse_dec(&mut self) -> PResult<Option<ast::Dec>> {
        match &self.peek().kind {
            TokenKind::Type => self.parse_type_dec(),
            TokenKind::Var => self.parse_var_dec(),
            TokenKind::Function => self.parse_func_dec(),
            TokenKind::Primitive => self.parse_primitive_dec(),
            TokenKind::Import => return self.parse_import_dec(),
            k => panic!("ICE: parse_dec received invalid token kind: {}", k),
        }
        .map(Some)
    }

    fn parse_type_dec(&mut self) -> PResult<ast::Dec> {
        let start = self.next().span;
        let name = self.expect_ident()?;
        self.expect(&T![=])?;
        let ty = self.parse_type()?;
        Ok(ast::Dec {
            span: start.extend(ty.span),
            kind: ast::DecKind::Type { name, ty },
        })
    }

    fn parse_var_dec(&mut self) -> PResult<ast::Dec> {
        let start = self.next().span;
        let name = self.expect_ident()?;
        let ty = if self.maybe_expect(&T![:]).is_some() {
            Some(self.expect_ident()?)
        } else {
            None
        };
        self.expect(&T![:=])?;
        let value = self.parse_expr()?;

        Ok(ast::Dec {
            span: start.extend(value.span),
            kind: ast::DecKind::Variable {
                name,
                ty,
                value: Box::new(value),
            },
        })
    }

    fn parse_func_dec(&mut self) -> PResult<ast::Dec> {
        let start = self.next().span;
        let name = self.expect_ident()?;
        self.expect(&T!['('])?;
        let parameters = self.parse_ty_fields()?;
        self.expect(&T![')'])?;

        let ret_ty = if self.maybe_expect(&T![:]).is_some() {
            Some(self.expect_ident()?)
        } else {
            None
        };

        self.expect(&T![=])?;
        let body = self.parse_expr()?;

        Ok(ast::Dec {
            span: start.extend(body.span),
            kind: ast::DecKind::Function {
                name,
                parameters,
                ret_ty,
                body: Box::new(body),
            },
        })
    }

    fn parse_primitive_dec(&mut self) -> PResult<ast::Dec> {
        let start = self.next().span;
        let name = self.expect_ident()?;
        self.expect(&T!['('])?;
        let parameters = self.parse_ty_fields()?;
        let mut end = self.expect(&T![')'])?.span;

        let ret_ty = if self.maybe_expect(&T![:]).is_some() {
            let ty = self.expect_ident()?;
            end = ty.span;
            Some(ty)
        } else {
            None
        };

        Ok(ast::Dec {
            span: start.extend(end),
            kind: ast::DecKind::Primitive {
                name,
                parameters,
                ret_ty,
            },
        })
    }

    fn parse_import_dec(&mut self) -> PResult<Option<ast::Dec>> {
        let start = self.next().span;
        let (path, end_span) = self.expect_string()?;
        let path = self.parse_string(path, end_span)?;

        let file_path = {
            #[cfg(unix)]
            {
                use std::ffi::OsStr;
                use std::os::unix::ffi::OsStrExt;

                OsStr::from_bytes(&path)
            }
            #[cfg(not(unix))]
            {
                use std::ffi::OsString;

                match String::from_utf8(path) {
                    Ok(s) => OsString::from(s),
                    Err(e) => {
                        self.errors.push(ParserError::new(
                            format!(
                                "File name is not UTF-8 - '{}'",
                                String::from_utf8_lossy(e.as_bytes())
                            ),
                            end_span,
                        ));
                        return Err(());
                    }
                }
            }
        };

        match self.add_file(&file_path) {
            Ok(file) => {
                let LexerResult {
                    tokens,
                    unterminated_comment,
                } = tokenize_source_file(file);
                self.tokens.push_tokens(tokens);

                if let Some(span) = unterminated_comment {
                    self.errors
                        .push(ParserError::new("Unterminated comment", span));
                }
                Ok(None)
            }
            Err(e) => {
                let error = match e.kind() {
                    std::io::ErrorKind::NotFound => "Not found".to_string(),
                    _ => {
                        format!("{}", e)
                    }
                };

                self.errors.push(ParserError::new(
                    format!(
                        "Failed to import file - {} - {}",
                        file_path.to_string_lossy(),
                        error
                    ),
                    start.extend(end_span),
                ));
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
    fn test_type_declaration() {
        check(
            "type my_int = int",
            expect![[r#"
                0..17: Decs
                  0..17: TypeDec
                    5..11: TypeName
                      5..11: Ident(my_int)
                    14..17: Type
                      14..17: TypeId(int)
            "#]],
        );
    }

    #[test]
    fn test_var_declaration() {
        check(
            "var a := 3",
            expect![[r#"
                0..10: Decs
                  0..10: VarDec
                    4..5: Variable(a)
                    9..10: Value
                      9..10: Integer(3)
            "#]],
        );

        check(
            "var b: int := add(1, 2)",
            expect![[r#"
                0..23: Decs
                  0..23: VarDec
                    4..5: Variable(b)
                    7..10: Type(int)
                    14..23: Value
                      14..23: Call
                        14..17: Func(add)
                        18..22: Arguments
                          18..19: Integer(1)
                          21..22: Integer(2)
            "#]],
        );
    }

    #[test]
    fn test_function_declaration() {
        check(
            "function add(x: int, y: int): int = x + y",
            expect![[r#"
                0..41: Decs
                  0..41: Function
                    9..12: Name(add)
                    13..19: Parameters
                      13..14: Name(x) - 16..19: Type(int)
                      21..22: Name(y) - 24..27: Type(int)
                    30..33: ReturnType(int)
                    36..41: Body
                      36..41: BinaryOp(+)
                        36..37: Left
                          36..37: LValue
                            36..37: Ident(x)
                        40..41: Right
                          40..41: LValue
                            40..41: Ident(y)
            "#]],
        );

        check(
            "function one() = 1",
            expect![[r#"
                0..18: Decs
                  0..18: Function
                    9..12: Name(one)
                    17..18: Body
                      17..18: Integer(1)
            "#]],
        );
    }

    #[test]
    fn test_primitive_declaration() {
        check(
            "primitive flush()",
            expect![[r#"
                0..17: Decs
                  0..17: Primitive
                    10..15: Name(flush)
            "#]],
        );

        check(
            "primitive exit(status_code: int)",
            expect![[r#"
                0..32: Decs
                  0..32: Primitive
                    10..14: Name(exit)
                    15..31: Parameters
                      15..26: Name(status_code) - 28..31: Type(int)
            "#]],
        );

        check(
            "primitive add(x: int, y: int): int",
            expect![[r#"
                0..34: Decs
                  0..34: Primitive
                    10..13: Name(add)
                    14..20: Parameters
                      14..15: Name(x) - 17..20: Type(int)
                      22..23: Name(y) - 25..28: Type(int)
                    31..34: ReturnType(int)
            "#]],
        );

        check(
            "primitive rand(): int",
            expect![[r#"
                0..21: Decs
                  0..21: Primitive
                    10..14: Name(rand)
                    18..21: ReturnType(int)
            "#]],
        );
    }
}
