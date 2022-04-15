use tig_error::ParserError;

use crate::{
    ast,
    lexer::{Token, TokenKind},
    T,
};

use super::{can_start_expr, PResult, Parser};

fn infix_binding_power(kind: &TokenKind) -> Option<(u8, u8, ast::BinOp)> {
    Some(match kind {
        T![|] => (1, 2, ast::BinOp::Or),
        T![&] => (3, 4, ast::BinOp::And),
        T![>=] => (5, 6, ast::BinOp::Gte),
        T![<=] => (5, 6, ast::BinOp::Lte),
        T![=] => (5, 6, ast::BinOp::Eq),
        T![<>] => (5, 6, ast::BinOp::Neq),
        T![<] => (5, 6, ast::BinOp::Lt),
        T![>] => (5, 6, ast::BinOp::Gt),
        T![+] => (7, 8, ast::BinOp::Add),
        T![-] => (7, 8, ast::BinOp::Subtract),
        T![*] => (9, 10, ast::BinOp::Multiply),
        T![/] => (9, 10, ast::BinOp::Divide),
        _ => return None,
    })
}

impl<'s> Parser<'s> {
    pub(super) fn parse_expr(&mut self) -> PResult<ast::Expr> {
        self.parse_expr_bp(0)
    }

    fn parse_expr_bp(&mut self, min_bp: u8) -> PResult<ast::Expr> {
        let mut lhs = self.parse_atom()?;

        if self.maybe_expect(&T![:=]).is_some() {
            match lhs {
                ast::Expr {
                    kind: ast::ExprKind::LValue(lvalue),
                    span,
                } => {
                    let source = self.parse_expr()?;
                    return Ok(ast::Expr {
                        span: span.extend(source.span),
                        kind: ast::ExprKind::Assign {
                            destination: lvalue,
                            source: Box::new(source),
                        },
                    });
                }
                _ => return Err(()),
            }
        }

        while let Some((l_bp, r_bp, op)) = infix_binding_power(&self.peek().kind) {
            if l_bp < min_bp {
                break;
            }
            self.next();

            let rhs = self.parse_expr_bp(r_bp)?;
            lhs = ast::Expr {
                span: lhs.span.extend(rhs.span),
                kind: ast::ExprKind::BinOp {
                    op,
                    left: Box::new(lhs),
                    right: Box::new(rhs),
                },
            };
        }

        Ok(lhs)
    }

    fn parse_atom(&mut self) -> PResult<ast::Expr> {
        match self.peek() {
            Token {
                kind: T![nil],
                span,
            } => {
                let atom = ast::Expr {
                    span: *span,
                    kind: ast::ExprKind::Nil,
                };
                self.next();
                Ok(atom)
            }

            Token {
                kind: TokenKind::Integer(n),
                span,
            } => {
                let span = *span;
                let n: isize = match n.parse() {
                    Ok(n) => n,
                    Err(_) => {
                        let error = ParserError::new(
                            format!(
                                "Literal out of range for integer, maximum number allowed is {}",
                                isize::MAX,
                            ),
                            span,
                        );
                        self.errors.push(error);
                        0
                    }
                };
                let atom = ast::Expr {
                    span,
                    kind: ast::ExprKind::Integer(n as usize),
                };
                self.next();
                Ok(atom)
            }

            Token {
                kind:
                    TokenKind::String {
                        value: s,
                        terminated,
                    },
                span,
            } => {
                let s = s.clone();
                let span = *span;
                if !terminated {
                    self.errors
                        .push(ParserError::new("Unterminatd string", span));
                }
                self.next();
                let s = self.parse_string(s, span)?;
                Ok(ast::Expr {
                    span,
                    kind: ast::ExprKind::String(s),
                })
            }

            Token { kind: T![-], span } => {
                let span = *span;
                self.next();
                let expr = self.parse_atom()?;
                Ok(ast::Expr {
                    span: span.extend(expr.span),
                    kind: ast::ExprKind::Negate(Box::new(expr)),
                })
            }

            Token {
                kind: TokenKind::Id(id),
                span,
            } => {
                let ident = ast::Ident {
                    span: *span,
                    value: id.clone(), // SmolStr clone is O(1)
                };
                self.next();
                self.expected.insert(T!['{']);
                self.expected.insert(T!['(']);
                if self.peek().kind == T!['{'] {
                    self.parse_record_creation(ident)
                } else if self.peek().kind == T!['('] {
                    self.parse_fn_call(ident)
                } else {
                    self.parse_lvalue_or_array_creation(ident)
                }
            }

            Token { kind: T![if], .. } => self.parse_if(),
            Token {
                kind: T![while], ..
            } => self.parse_while(),
            Token { kind: T![for], .. } => self.parse_for(),
            Token {
                kind: T![break],
                span,
            } => {
                let span = *span;
                self.next();
                Ok(ast::Expr {
                    span,
                    kind: ast::ExprKind::Break,
                })
            }
            Token { kind: T![let], .. } => self.parse_let(),

            Token { kind: T!['('], .. } => self.parse_exprs(),

            // TODO: String
            Token { kind, span } => {
                let error =
                    ParserError::new(format!("Expected an expression, got '{}'", kind,), *span);
                self.errors.push(error);
                Err(())
            }
        }
    }

    fn parse_record_creation(&mut self, type_id: ast::Ident) -> PResult<ast::Expr> {
        self.next();
        let mut fields = vec![];
        while self.peek().kind != T!['}'] && !self.at_eof() {
            let field = self.expect_ident()?;
            self.expect(&T![=])?;
            let value = self.parse_expr()?;
            fields.push(ast::RecordField { field, value });
            if self.maybe_expect(&T![,]).is_none() {
                break;
            }
        }
        let end = self.expect(&T!['}'])?.span;

        Ok(ast::Expr {
            span: type_id.span.extend(end),
            kind: ast::ExprKind::Record { type_id, fields },
        })
    }

    fn parse_lvalue_or_array_creation(&mut self, ident: ast::Ident) -> PResult<ast::Expr> {
        let lvalue = if self.peek().kind == T!['['] {
            self.next();
            let inner_expr = self.parse_expr()?;
            self.expect(&T![']'])?;
            if self.peek().kind == T![of] {
                self.next();
                let init = self.parse_expr()?;
                let span = ident.span.extend(init.span);
                return Ok(ast::Expr {
                    span,
                    kind: ast::ExprKind::Array {
                        type_id: ident,
                        size: Box::new(inner_expr),
                        initial_value: Box::new(init),
                    },
                });
            } else {
                self.parse_lvalue(ast::LValue::ArrayAccess(
                    Box::new(ast::LValue::Ident(ident)),
                    Box::new(inner_expr),
                ))?
            }
        } else {
            self.parse_lvalue(ast::LValue::Ident(ident))?
        };

        let span = lvalue.span();
        Ok(ast::Expr {
            span,
            kind: ast::ExprKind::LValue(lvalue),
        })
    }

    fn parse_lvalue(&mut self, lvalue: ast::LValue) -> PResult<ast::LValue> {
        self.expected.insert(T!['[']);
        self.expected.insert(T![.]);
        match &self.peek().kind {
            T![.] => {
                self.next();
                let field = self.expect_ident()?;
                let field_access = ast::LValue::FieldAccess(
                    Box::new(lvalue),
                    ast::Ident {
                        span: field.span,
                        value: field.value,
                    },
                );
                self.parse_lvalue(field_access)
            }
            T!['['] => {
                self.next();
                let expr = self.parse_expr()?;
                self.expect(&T![']'])?;

                let array_access = ast::LValue::ArrayAccess(Box::new(lvalue), Box::new(expr));
                self.parse_lvalue(array_access)
            }
            _ => Ok(lvalue),
        }
    }

    fn parse_fn_call(&mut self, func: ast::Ident) -> PResult<ast::Expr> {
        self.next();
        let mut arguments = vec![];
        while can_start_expr(&self.peek().kind) {
            arguments.push(self.parse_expr()?);
            if self.maybe_expect(&T![,]).is_none() {
                break;
            }
        }
        let end = self.expect(&T![')'])?.span;
        Ok(ast::Expr {
            span: func.span.extend(end),
            kind: ast::ExprKind::Call { func, arguments },
        })
    }

    fn parse_exprs(&mut self) -> PResult<ast::Expr> {
        let start = self.next().span;
        let mut exprs = vec![];
        while can_start_expr(&self.peek().kind) {
            exprs.push(self.parse_expr()?);
            if self.maybe_expect(&T![;]).is_none() {
                break;
            }
        }
        let end = self.expect(&T![')'])?.span;

        Ok(ast::Expr {
            span: start.extend(end),
            kind: ast::ExprKind::Exprs(exprs),
        })
    }

    fn parse_if(&mut self) -> PResult<ast::Expr> {
        let start = self.next().span;
        let cond = self.parse_expr()?;
        self.expect(&T![then])?;
        let then_branch = self.parse_expr()?;
        let mut end = then_branch.span;

        let else_branch = if self.maybe_expect(&T![else]).is_some() {
            let e = self.parse_expr()?;
            end = e.span;
            Some(e)
        } else {
            None
        };

        Ok(ast::Expr {
            span: start.extend(end),
            kind: ast::ExprKind::If {
                cond: Box::new(cond),
                then_branch: Box::new(then_branch),
                else_branch: else_branch.map(Box::new),
            },
        })
    }

    fn parse_while(&mut self) -> PResult<ast::Expr> {
        let start = self.next().span;
        let cond = self.parse_expr()?;
        self.expect(&T![do])?;
        let body = self.parse_expr()?;
        let end = body.span;

        Ok(ast::Expr {
            span: start.extend(end),
            kind: ast::ExprKind::While {
                cond: Box::new(cond),
                body: Box::new(body),
            },
        })
    }

    fn parse_for(&mut self) -> PResult<ast::Expr> {
        let start = self.next().span;
        let iterator = self.expect_ident()?;
        self.expect(&T![:=])?;
        let init = self.parse_expr()?;
        self.expect(&T![to])?;
        let end = self.parse_expr()?;
        self.expect(&T![do])?;
        let body = self.parse_expr()?;

        Ok(ast::Expr {
            span: start.extend(body.span),
            kind: ast::ExprKind::For {
                iterator,
                escape: false,
                start: Box::new(init),
                end: Box::new(end),
                body: Box::new(body),
            },
        })
    }

    fn parse_let(&mut self) -> PResult<ast::Expr> {
        let start = self.next().span;
        let decs = self.parse_decs(&T![in])?;
        self.expect(&T![in])?;
        let mut exprs = vec![];
        while can_start_expr(&self.peek().kind) {
            exprs.push(self.parse_expr()?);

            if self.maybe_expect(&T![;]).is_none() {
                break;
            }
        }
        let end = self.expect(&T![end])?.span;

        Ok(ast::Expr {
            span: start.extend(start.extend(end)),
            kind: ast::ExprKind::Let { decs, exprs },
        })
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
    fn test_nil() {
        check(
            "nil",
            expect![[r#"
                0..3: Expr
                  0..3: Nil
            "#]],
        );
    }

    #[test]
    fn test_integer() {
        check(
            "1234",
            expect![[r#"
                0..4: Expr
                  0..4: Integer(1234)
            "#]],
        );

        check(
            "0",
            expect![[r#"
                0..1: Expr
                  0..1: Integer(0)
            "#]],
        );

        check(
            "9999999",
            expect![[r#"
                0..7: Expr
                  0..7: Integer(9999999)
            "#]],
        );
    }

    #[test]
    fn test_string() {
        check(
            r#" "Hello, World!" "#,
            expect![[r#"
                1..16: Expr
                  1..16: String(Hello, World!)
            "#]],
        );

        check(
            r#" "\040" "#,
            expect![[r#"
                1..7: Expr
                  1..7: String( )
            "#]],
        );

        check(
            r#" "\\\"Hello\040World\041\\\"" "#,
            expect![[r#"
                1..29: Expr
                  1..29: String(\"Hello World!\")
            "#]],
        );

        check(
            r#" "\x48\x65\x6c\x6c\x6f\x20\x57\x6f\x72\x6c\x64\x21" "#,
            expect![[r#"
                1..51: Expr
                  1..51: String(Hello World!)
            "#]],
        );
    }

    #[test]
    fn test_array_creation() {
        check(
            "int [10] of 0",
            expect![[r#"
                0..13: Expr
                  0..13: Array
                    0..3: Type
                      0..3: Ident(int)
                    5..7: Size
                      5..7: Integer(10)
                    12..13: InitialValue
                      12..13: Integer(0)
            "#]],
        );
    }

    #[test]
    fn test_record_creation() {
        check(
            "span { lo = 0, hi = 3 }",
            expect![[r#"
                0..23: Expr
                  0..23: Record
                    0..4: Type
                      0..4: Ident(span)
                    7..21: Fields
                      7..13: RecordField
                        7..9: Field(lo)
                        12..13: Expr
                          12..13: Integer(0)
                      15..21: RecordField
                        15..17: Field(hi)
                        20..21: Expr
                          20..21: Integer(3)
            "#]],
        );
    }

    #[test]
    fn test_lvalues() {
        check(
            "x",
            expect![[r#"
                0..1: Expr
                  0..1: LValue
                    0..1: Ident(x)
            "#]],
        );

        check(
            "x.a",
            expect![[r#"
                0..3: Expr
                  0..3: LValue
                    0..3: FieldAccess
                      0..1: Object
                        0..1: Ident(x)
                      2..3: Field
                        2..3: Ident(a)
            "#]],
        );

        check(
            "a.b.c.d",
            expect![[r#"
                0..7: Expr
                  0..7: LValue
                    0..7: FieldAccess
                      0..5: Object
                        0..5: FieldAccess
                          0..3: Object
                            0..3: FieldAccess
                              0..1: Object
                                0..1: Ident(a)
                              2..3: Field
                                2..3: Ident(b)
                          4..5: Field
                            4..5: Ident(c)
                      6..7: Field
                        6..7: Ident(d)
            "#]],
        );

        check(
            "x[10]",
            expect![[r#"
                0..4: Expr
                  0..4: LValue
                    0..4: ArrayAccess
                      0..1: Array
                        0..1: Ident(x)
                      2..4: Index
                        2..4: Integer(10)
            "#]],
        );

        check(
            "x[10][1][3][a]",
            expect![[r#"
                0..13: Expr
                  0..13: LValue
                    0..13: ArrayAccess
                      0..10: Array
                        0..10: ArrayAccess
                          0..7: Array
                            0..7: ArrayAccess
                              0..4: Array
                                0..4: ArrayAccess
                                  0..1: Array
                                    0..1: Ident(x)
                                  2..4: Index
                                    2..4: Integer(10)
                              6..7: Index
                                6..7: Integer(1)
                          9..10: Index
                            9..10: Integer(3)
                      12..13: Index
                        12..13: LValue
                          12..13: Ident(a)
            "#]],
        );

        check(
            "a.b.c[d.e[f]].g[h[i.j]]",
            expect![[r#"
                0..21: Expr
                  0..21: LValue
                    0..21: ArrayAccess
                      0..15: Array
                        0..15: FieldAccess
                          0..11: Object
                            0..11: ArrayAccess
                              0..5: Array
                                0..5: FieldAccess
                                  0..3: Object
                                    0..3: FieldAccess
                                      0..1: Object
                                        0..1: Ident(a)
                                      2..3: Field
                                        2..3: Ident(b)
                                  4..5: Field
                                    4..5: Ident(c)
                              6..11: Index
                                6..11: LValue
                                  6..11: ArrayAccess
                                    6..9: Array
                                      6..9: FieldAccess
                                        6..7: Object
                                          6..7: Ident(d)
                                        8..9: Field
                                          8..9: Ident(e)
                                    10..11: Index
                                      10..11: LValue
                                        10..11: Ident(f)
                          14..15: Field
                            14..15: Ident(g)
                      16..21: Index
                        16..21: LValue
                          16..21: ArrayAccess
                            16..17: Array
                              16..17: Ident(h)
                            18..21: Index
                              18..21: LValue
                                18..21: FieldAccess
                                  18..19: Object
                                    18..19: Ident(i)
                                  20..21: Field
                                    20..21: Ident(j)
            "#]],
        );
    }

    #[test]
    fn test_fn_call() {
        check(
            "rand()",
            expect![[r#"
                0..6: Expr
                  0..6: Call
                    0..4: Func(rand)
            "#]],
        );

        check(
            "exit(1)",
            expect![[r#"
                0..7: Expr
                  0..7: Call
                    0..4: Func(exit)
                    5..6: Arguments
                      5..6: Integer(1)
            "#]],
        );

        check(
            "print_ints(1, 2, 3, rand())",
            expect![[r#"
                0..27: Expr
                  0..27: Call
                    0..10: Func(print_ints)
                    11..26: Arguments
                      11..12: Integer(1)
                      14..15: Integer(2)
                      17..18: Integer(3)
                      20..26: Call
                        20..24: Func(rand)
            "#]],
        );
    }

    #[test]
    fn test_negate() {
        check(
            "-a",
            expect![[r#"
                0..2: Expr
                  0..2: Negate
                  1..2: LValue
                    1..2: Ident(a)
            "#]],
        );

        check(
            "-a(1)",
            expect![[r#"
                0..5: Expr
                  0..5: Negate
                  1..5: Call
                    1..2: Func(a)
                    3..4: Arguments
                      3..4: Integer(1)
            "#]],
        );
    }

    #[test]
    fn test_op_precedence() {
        check(
            "1 + 1",
            expect![[r#"
                0..5: Expr
                  0..5: BinaryOp(+)
                    0..1: Left
                      0..1: Integer(1)
                    4..5: Right
                      4..5: Integer(1)
            "#]],
        );

        check(
            "1 + 2 * 3 - 4 / 5",
            expect![[r#"
                0..17: Expr
                  0..17: BinaryOp(-)
                    0..9: Left
                      0..9: BinaryOp(+)
                        0..1: Left
                          0..1: Integer(1)
                        4..9: Right
                          4..9: BinaryOp(*)
                            4..5: Left
                              4..5: Integer(2)
                            8..9: Right
                              8..9: Integer(3)
                    12..17: Right
                      12..17: BinaryOp(/)
                        12..13: Left
                          12..13: Integer(4)
                        16..17: Right
                          16..17: Integer(5)
            "#]],
        );

        check(
            "-a + -3 * -4",
            expect![[r#"
                0..12: Expr
                  0..12: BinaryOp(+)
                    0..2: Left
                      0..2: Negate
                      1..2: LValue
                        1..2: Ident(a)
                    5..12: Right
                      5..12: BinaryOp(*)
                        5..7: Left
                          5..7: Negate
                          6..7: Integer(3)
                        10..12: Right
                          10..12: Negate
                          11..12: Integer(4)
            "#]],
        );
    }

    #[test]
    fn test_exprs() {
        check(
            "(3)",
            expect![[r#"
                0..3: Expr
                  0..3: Exprs
                    1..2: Expr
                      1..2: Integer(3)
            "#]],
        );

        check(
            "(1; 3)",
            expect![[r#"
                0..6: Expr
                  0..6: Exprs
                    1..2: Expr
                      1..2: Integer(1)
                    4..5: Expr
                      4..5: Integer(3)
            "#]],
        );

        check(
            "(a; a := 3)",
            expect![[r#"
                0..11: Expr
                  0..11: Exprs
                    1..2: Expr
                      1..2: LValue
                        1..2: Ident(a)
                    4..10: Expr
                      4..10: Assign
                        4..5: LValue
                          4..5: Ident(a)
                        9..10: Expr
                          9..10: Integer(3)
            "#]],
        );
    }

    #[test]
    fn test_assignment() {
        check(
            "a := 3",
            expect![[r#"
                0..6: Expr
                  0..6: Assign
                    0..1: LValue
                      0..1: Ident(a)
                    5..6: Expr
                      5..6: Integer(3)
            "#]],
        );
    }

    #[test]
    fn test_if() {
        check(
            "if a then b else c",
            expect![[r#"
                0..18: Expr
                  0..18: If
                    3..4: Condition
                      3..4: LValue
                        3..4: Ident(a)
                    10..11: Then
                      10..11: LValue
                        10..11: Ident(b)
                    17..18: Else
                      17..18: LValue
                        17..18: Ident(c)
            "#]],
        );
    }

    #[test]
    fn test_while() {
        check(
            "while 1 do b",
            expect![[r#"
                0..12: Expr
                  0..12: While
                    6..7: Condition
                      6..7: Integer(1)
                    11..12: Body
                      11..12: LValue
                        11..12: Ident(b)
            "#]],
        );
    }

    #[test]
    fn test_for() {
        check(
            "for i := 0 to 10 do a",
            expect![[r#"
                0..21: Expr
                  0..21: For - Escape(false)
                    4..5: Ident
                      4..5: Ident(i)
                    9..10: Start
                      9..10: Integer(0)
                    14..16: End
                      14..16: Integer(10)
                    20..21: Body
                      20..21: LValue
                        20..21: Ident(a)
            "#]],
        );
    }

    #[test]
    fn test_break() {
        check(
            "break",
            expect![[r#"
                0..5: Expr
                  0..5: Break
            "#]],
        );
    }

    #[test]
    fn test_let() {
        check(
            "let in 3 end",
            expect![[r#"
                0..12: Expr
                  0..12: Let
                    7..8: Exprs
                      7..8: Integer(3)
            "#]],
        );

        check(
            "let type a = b type c = d in a end",
            expect![[r#"
                0..34: Expr
                  0..34: Let
                    4..25: Decs
                      4..25: TypeDecs
                        4..14: TypeDec
                          9..10: TypeName
                            9..10: Ident(a)
                          13..14: Type
                            13..14: TypeId(b)
                        15..25: TypeDec
                          20..21: TypeName
                            20..21: Ident(c)
                          24..25: Type
                            24..25: TypeId(d)
                    29..30: Exprs
                      29..30: LValue
                        29..30: Ident(a)
            "#]],
        );

        check(
            "let in a; b; 1 end",
            expect![[r#"
                0..18: Expr
                  0..18: Let
                    7..14: Exprs
                      7..8: LValue
                        7..8: Ident(a)
                      10..11: LValue
                        10..11: Ident(b)
                      13..14: Integer(1)
            "#]],
        );
    }
}
