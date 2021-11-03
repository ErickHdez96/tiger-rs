use super::*;
use crate::T;
use tig_ast::ast;
use tig_common::SmolStr;

// x - Implemented
// - - Incomplete
//   - Not implemented
//
//   exp ::=
// x   # Literals.
// x     nil
// x   | integer
// x   | string
//
//     # Array and record creations.
// x   | type-id [ exp ] of exp
// x   | type-id {[ id = exp { , id = exp } ] }
//
//     # Object creation.
//     | new type-id
//
//     # Variables, field, elements of an array.
// x   | lvalue
//
//     # Function call.
// x   | id ( [ exp { , exp }] )
//
//     # Method call.
//     | lvalue . id ( [ exp { , exp }] )
//
//     # Operations.
// x   | - exp
// x   | exp op exp
// x   | ( exps )
//
//     # Assignment.
// x   | lvalue := exp
//
//     # Control structures.
// x   | if exp then exp [else exp]
// x   | while exp do exp
// x   | for id := exp to exp do exp
// x   | break
// x   | let decs in exps end
//
//
// x lvalue ::= id
// x   | lvalue . id
// x   | lvalue [ exp ]
// x exps ::= [ exp { ; exp } ]

#[derive(Debug)]
enum PrefixOp {
    Negate,
}

impl Parser {
    pub(super) fn parse_expr(&mut self) -> PResult<ast::Expr> {
        self.parse_bp(0)
    }

    fn parse_bp(&mut self, min_bp: u8) -> PResult<ast::Expr> {
        let mut left = if let Some((op, (), r_bp)) = prefix_binding_power(&self.peek().kind) {
            let op_span = self.next().span;

            let e = self.parse_bp(r_bp)?;
            // -e is syntactic sugar for 0 - e
            match op {
                PrefixOp::Negate => ast::Expr {
                    span: op_span.extend(e.span),
                    kind: ast::ExprKind::BinOp {
                        op: ast::BinOp::Sub,
                        left: Box::new(ast::Expr {
                            span: op_span,
                            kind: ast::ExprKind::Int(0),
                        }),
                        right: Box::new(e),
                    },
                },
            }
        } else {
            self.parse_simple_expr()?
        };

        loop {
            if let Some((op, l_bp, r_bp)) = infix_binding_power(&self.peek().kind) {
                if l_bp < min_bp {
                    break;
                }
                self.next();

                let right = self.parse_bp(r_bp)?;
                left = ast! {expr, binop, left.span.extend(right.span), op, left, right};

                continue;
            }

            break;
        }

        Ok(left)
    }

    fn parse_simple_expr(&mut self) -> PResult<ast::Expr> {
        match self.peek() {
            Token {
                kind: TokenKind::Ident(id),
                span,
            } => {
                let span = *span;
                // SmolStr::clone is O(1)
                let id = id.clone();
                self.next();
                self.parse_ident_consumed(id, span)
            }
            Token { kind: T![if], .. } => self.parse_if(),
            Token {
                kind: T![while], ..
            } => self.parse_while(),
            Token { kind: T![for], .. } => self.parse_for(),
            Token { kind: T![let], .. } => self.parse_let(),
            _ => self.parse_atom(),
        }
    }

    fn parse_atom(&mut self) -> PResult<ast::Expr> {
        match self.next() {
            Token {
                span,
                kind: T![nil],
            } => Ok(ast! {expr, nil, span}),
            Token {
                span,
                kind: TokenKind::Int(n),
            } => Ok(ast! {expr, int, span, self.parse_int(&n, span)?}),
            Token {
                span,
                kind: TokenKind::String(s),
            } => Ok(ast! {expr, str, span, s}),
            Token {
                span,
                kind: T![break],
            } => Ok(ast! {expr, break, span}),
            Token {
                span,
                kind: T!['('],
            } => {
                let expr = self.parse_bp(0)?;

                if self.peek().kind == T![;] {
                    let mut exprs = vec![expr];
                    self.next();

                    while can_start_expr(&self.peek().kind) {
                        exprs.push(self.parse_bp(0)?);
                        match self.peek().kind {
                            T![;] => {
                                self.next();
                            }
                            _ => break,
                        }
                    }

                    let end = self.eat(&T![')'])?;
                    Ok(ast::Expr {
                        span: span.extend(end.span),
                        kind: ast::ExprKind::Seq(exprs),
                    })
                } else {
                    let end = self.eat(&T![')'])?;
                    Ok(ast::Expr {
                        span: span.extend(end.span),
                        kind: ast::ExprKind::Paren(Box::new(expr)),
                    })
                }
            }
            Token { span, kind } => Err(SError!(span, "Expected an expression, found `{}`", kind)),
        }
    }

    fn parse_let(&mut self) -> PResult<ast::Expr> {
        let start = self.next().span;
        let decs = self.parse_decs()?;
        self.eat(&T![in])?;

        let expr = self.parse_bp(0)?;
        if self.peek().kind == T![;] {
            self.next();
            let expr_start_span = expr.span;
            let mut last_span = expr.span;
            let mut exprs = vec![expr];

            while can_start_expr(&self.peek().kind) {
                let expr = self.parse_bp(0)?;
                last_span = expr.span;
                exprs.push(expr);

                if self.peek().kind == T![;] {
                    last_span = self.next().span;
                } else {
                    break;
                }
            }

            Ok(ast::Expr {
                span: start.extend(last_span),
                kind: ast::ExprKind::Let {
                    decs,
                    body: Box::new(ast::Expr {
                        span: expr_start_span.extend(last_span),
                        kind: ast::ExprKind::Seq(exprs),
                    }),
                },
            })
        } else {
            Ok(ast::Expr {
                span: start.extend(expr.span),
                kind: ast::ExprKind::Let {
                    decs,
                    body: Box::new(expr),
                },
            })
        }
    }

    fn parse_if(&mut self) -> PResult<ast::Expr> {
        let start = self.next().span;
        let test = self.parse_bp(0)?;
        self.eat(&T![then])?;
        let then_branch = self.parse_bp(0)?;

        let (else_branch, end) = if self.peek().kind == T![else] {
            self.next();
            let else_branch = self.parse_bp(0)?;
            let end = else_branch.span;
            (Some(else_branch), end)
        } else {
            (None, then_branch.span)
        };

        Ok(ast::Expr {
            span: start.extend(end),
            kind: ast::ExprKind::If {
                test: Box::new(test),
                then_branch: Box::new(then_branch),
                else_branch: else_branch.map(Box::new),
            },
        })
    }

    fn parse_while(&mut self) -> PResult<ast::Expr> {
        let start = self.next().span;
        let test = self.parse_bp(0)?;
        self.eat(&T![do])?;
        let body = self.parse_bp(0)?;

        Ok(ast::Expr {
            span: start.extend(body.span),
            kind: ast::ExprKind::While {
                test: Box::new(test),
                body: Box::new(body),
            },
        })
    }

    fn parse_for(&mut self) -> PResult<ast::Expr> {
        let start = self.next().span;
        let id = self.eat_ident()?;
        self.eat(&T![:=])?;
        let lo = self.parse_bp(0)?;
        self.eat(&T![to])?;
        let hi = self.parse_bp(0)?;
        self.eat(&T![do])?;
        let body = self.parse_bp(0)?;

        Ok(ast::Expr {
            span: start.extend(body.span),
            kind: ast::ExprKind::For {
                var: id,
                escape: false,
                lo: Box::new(lo),
                hi: Box::new(hi),
                body: Box::new(body),
            },
        })
    }

    // Parse any expr starting with an <ident>
    //  * Array creation
    //  * Struct creation
    //  * lvalue
    //  * Function call
    //  * Method call
    //  * Assignment
    fn parse_ident_consumed(&mut self, ident: SmolStr, span: Span) -> PResult<ast::Expr> {
        let expr = match self.peek().kind {
            T!['['] => self.parse_array_creation_or_access(ident, span),
            T!['{'] => self.parse_struct(ident, span),
            T!['('] => self.parse_function_call(ident, span),
            _ => self.parse_lvalue_cont(ast! {lvalue, simple, span, ident}),
        }?;

        match expr.kind {
            ast::ExprKind::LValue(l) if self.peek().kind == T![:=] => {
                self.next();
                let expr = self.parse_bp(0)?;

                Ok(ast::Expr {
                    span: l.span.extend(expr.span),
                    kind: ast::ExprKind::Assign {
                        var: l,
                        expr: Box::new(expr),
                    },
                })
            }
            _ => Ok(expr),
        }
    }

    // <type-id> `{` [ id = exp { , id = exp } ] `}`
    //            ^
    //            Exects parser's current token to point here.
    fn parse_struct(&mut self, ident: SmolStr, span: Span) -> PResult<ast::Expr> {
        self.eat(&T!['{'])?;

        let mut fields = vec![];
        while self.peek().kind != T!['}'] {
            fields.push(self.parse_field()?);

            if self.peek().kind == T![,] {
                self.next();
            } else {
                break;
            }
        }

        let end = self.eat(&T!['}'])?;
        Ok(ast::Expr {
            span: span.extend(end.span),
            kind: ast::ExprKind::Record {
                fields,
                ty: ast::Ident { span, value: ident },
            },
        })
    }

    fn parse_field(&mut self) -> PResult<ast::FieldExpr> {
        let field = self.eat_ident()?;
        self.eat(&T![=])?;
        let expr = self.parse_bp(0)?;

        Ok(ast::FieldExpr { field, expr })
    }

    // After parsing an ident and peeking a `[`, parse either an array access, or an array create
    //
    // <id>      [ <expr> ]
    // <type-id> [ <expr> ] of <expr>
    //           ^
    //           Expects parser's current token to point here
    fn parse_array_creation_or_access(&mut self, ident: SmolStr, span: Span) -> PResult<ast::Expr> {
        self.next();
        let size_or_index = self.parse_bp(0)?;
        let rbracket = self.eat(&T![']'])?;

        // To disambiguate between array creation and array access, after <id> [ <expr> ],
        // we peek to see if we find an `of`, if it is there, we parse an array creation,
        // otherwise we transorm it into an lvalue and keep trying to parse an lvalue.
        match self.peek().kind {
            // <type-id> [ <expr> ] of <expr>
            T![of] => {
                self.next();
                let init = self.parse_bp(0)?;
                Ok(ast::Expr {
                    span: span.extend(init.span),
                    kind: ast::ExprKind::Array {
                        ty: ast::Ident { span, value: ident },
                        size: Box::new(size_or_index),
                        init: Box::new(init),
                    },
                })
            }
            _ => self.parse_lvalue_cont(ast::LValue {
                span: span.extend(rbracket.span),
                kind: ast::LValueKind::Subscript(
                    Box::new(ast::LValue {
                        span,
                        kind: ast::LValueKind::Simple(ident),
                    }),
                    Box::new(size_or_index),
                ),
            }),
        }
    }

    // <id> ( [ exp {, exp} (,)? ] )
    //      ^
    //      Exects parser's current token to point here.
    fn parse_function_call(&mut self, ident: SmolStr, span: Span) -> PResult<ast::Expr> {
        self.next();
        let args = self.parse_function_args()?;
        let end = self.eat(&T![')'])?;
        Ok(ast::Expr {
            span: span.extend(end.span),
            kind: ast::ExprKind::Call {
                func: ast::Ident { span, value: ident },
                args,
            },
        })
    }

    fn parse_function_args(&mut self) -> PResult<Vec<ast::Expr>> {
        let mut args = vec![];

        while can_start_expr(&self.peek().kind) {
            args.push(self.parse_bp(0)?);
            match self.peek().kind {
                T![,] => {
                    self.next();
                }
                _ => break,
            }
        }

        Ok(args)
    }

    fn parse_lvalue_cont(&mut self, lvalue: ast::LValue) -> PResult<ast::Expr> {
        match self.peek().kind {
            T!['['] => {
                self.next();
                let index = self.parse_bp(0)?;
                let end = self.eat(&T![']'])?;
                self.parse_lvalue_cont(ast::LValue {
                    span: lvalue.span.extend(end.span),
                    kind: ast::LValueKind::Subscript(Box::new(lvalue), Box::new(index)),
                })
            }
            T![.] => {
                self.next();
                let ident = self.eat_ident()?;
                self.parse_lvalue_cont(ast::LValue {
                    span: lvalue.span.extend(ident.span),
                    kind: ast::LValueKind::Field(Box::new(lvalue), ident),
                })
            }
            _ => Ok(ast! {expr, lvalue, lvalue.span, lvalue}),
        }
    }
}

fn prefix_binding_power(kind: &TokenKind) -> Option<(PrefixOp, (), u8)> {
    Some(match kind {
        T![-] => (PrefixOp::Negate, (), 9),
        _ => return None,
    })
}

fn infix_binding_power(kind: &TokenKind) -> Option<(ast::BinOp, u8, u8)> {
    Some(match kind {
        T![|] => (ast::BinOp::Or, 2, 3),
        T![&] => (ast::BinOp::And, 3, 4),
        T![=] => (ast::BinOp::Eq, 4, 5),
        T![<>] => (ast::BinOp::Neq, 4, 5),
        T![<] => (ast::BinOp::Lt, 4, 5),
        T![<=] => (ast::BinOp::Lte, 4, 5),
        T![>] => (ast::BinOp::Gt, 4, 5),
        T![>=] => (ast::BinOp::Gte, 4, 5),
        T![+] => (ast::BinOp::Add, 5, 6),
        T![-] => (ast::BinOp::Sub, 5, 6),
        T![*] => (ast::BinOp::Mul, 7, 8),
        T![/] => (ast::BinOp::Div, 7, 8),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tig_ast::{binop, Expr};
    use tig_common::Span;

    macro_rules! span {
        ($lo:expr, $hi:expr $(,)?) => {
            Span::new($lo as u32, $hi as u32)
        };
    }

    fn check(input: &str, expected: Expr) {
        let tokens = tokenize(input);
        let mut p = Parser::new(tokens);
        let parsed = p.parse_expr().expect("Could not parse");
        assert_eq!(parsed, expected);
    }

    #[test]
    fn parses_nil() {
        check("nil", ast! {expr, nil, span!(0, 3)});
    }

    #[test]
    fn parses_string() {
        check(
            r#""Hello, World!""#,
            ast! {expr, str, span!(0, 15), "\"Hello, World!\""},
        );
    }

    #[test]
    fn parses_simple_lvalue() {
        check(
            "a",
            ast! {expr, lvalue, span!(0, 1), ast! {lvalue, simple, span!(0, 1), "a"}},
        );
    }

    #[test]
    fn parses_array_access() {
        check(
            "a[3]",
            ast! {expr, lvalue, span!(0, 4),
                ast!{lvalue, subscript, span!(0, 4),
                    ast! {lvalue, simple, span!(0, 1), "a"},
                    ast! {expr, int, span!(2, 3), 3},
                },
            },
        );
    }

    #[test]
    fn parses_array_creation() {
        check(
            "int [100] of 0",
            ast! {expr, array, span!(0, 14),
                ast! {ident, span!(0, 3), "int"},
                ast! {expr, int, span!(5, 8), 100},
                ast! {expr, int, span!(13, 14), 0},
            },
        );
    }

    #[test]
    fn parses_record_creation() {
        check(
            "user { a = 1, b = 2, }",
            ast! {expr, record, span!(0, 22),
                ast! {ident, span!(0, 4), "user"},
                {
                    ast! {ident, span!(7, 8), "a"} => ast! {expr, int, span!(11, 12), 1},
                    ast! {ident, span!(14, 15), "b"} => ast! {expr, int, span!(18, 19), 2},
                },
            },
        );
    }

    #[test]
    fn parses_field_access() {
        check(
            "a.b",
            ast! {expr, lvalue, span!(0, 3),
                ast! {lvalue, field, span!(0, 3),
                    ast! {lvalue, simple, span!(0, 1), "a"},
                    ast! {ident, span!(2, 3), "b"},
                },
            },
        );
    }

    #[test]
    fn parses_function_call() {
        check(
            "print(\"Hi\")",
            ast! {expr, fn, span!(0, 11),
                ast! {ident, span!(0, 5), "print"},
                vec![
                    ast! {expr, str, span!(6, 10), "\"Hi\""},
                ]
            },
        );
    }

    #[test]
    fn parses_operator_precedence() {
        check(
            "0 - 1 * -3 + 2 / --1",
            ast! {
                expr, binop, span!(0, 20),
                binop!(+),
                ast!{
                    expr, binop, span!(0, 10),
                    binop!(-),
                    ast!{expr, int, span!(0, 1), 0},
                    ast!{
                        expr, binop, span!(4, 10),
                        binop!(*),
                        ast!{expr, int, span!(4, 5), 1},
                        ast! {expr, binop, span!(8, 10),
                            binop!(-),
                            ast!{expr, int, span!(8, 9), 0},
                            ast!{expr, int, span!(9, 10), 3},
                        },
                    },
                },
                ast!{
                    expr, binop, span!(13, 20),
                    binop!(/),
                    ast!{expr, int, span!(13, 14), 2},
                    ast!{expr, binop, span!(17, 20),
                        binop!(-),
                        ast!{expr, int, span!(17, 18), 0},
                        ast!{expr, binop, span!(18, 20),
                            binop!(-),
                            ast!{expr, int, span!(18, 19), 0},
                            ast!{expr, int, span!(19, 20), 1},
                        }
                    }
                },
            },
        );

        check(
            "0 | 1 & 3 < 2 = 1",
            ast! {
                expr, binop, span!(0, 17),
                binop!(|),
                ast!{expr, int, span!(0, 1), 0},
                ast!{
                    expr, binop, span!(4, 17),
                    binop!(&),
                    ast!{expr, int, span!(4, 5), 1},
                    ast!{
                        expr, binop, span!(8, 17),
                        binop!(=),
                        ast!{
                            expr, binop, span!(8, 13),
                            binop!(<),
                            ast!(expr, int, span!(8, 9), 3),
                            ast!(expr, int, span!(12, 13), 2),
                        },
                        ast!(expr, int, span!(16, 17), 1),
                    },
                },
            },
        );
    }

    #[test]
    fn parses_parenthesis() {
        check(
            "(1 + 2) * 3",
            ast! {
                expr, binop, span!(0, 11),
                binop!(*),
                ast! {expr, paren, span!(0, 7),
                    ast! {expr, binop, span!(1, 6),
                        binop!(+),
                        ast! {expr, int, span!(1, 2), 1},
                        ast! {expr, int, span!(5, 6), 2},
                    },
                },
                ast! {expr, int, span!(10, 11), 3},
            },
        );
    }

    #[test]
    fn parses_sequence() {
        check(
            "(1; 2;)",
            ast! {expr, seq, span!(0, 7),
                vec![
                    ast! {expr, int, span!(1, 2), 1},
                    ast! {expr, int, span!(4, 5), 2},
                ],
            },
        );
    }

    #[test]
    fn parses_if() {
        check(
            "if 1 then a else b",
            ast! {expr, ife, span!(0, 18),
                ast! {expr, int, span!(3, 4), 1},
                ast! {expr, lvalue, span!(10, 11), ast! {lvalue, simple, span!(10, 11), "a"}},
                ast! {expr, lvalue, span!(17, 18), ast! {lvalue, simple, span!(17, 18), "b"}},
            },
        );

        check(
            "if 1 then a",
            ast! {expr, if, span!(0, 11),
                ast! {expr, int, span!(3, 4), 1},
                ast! {expr, lvalue, span!(10, 11), ast! {lvalue, simple, span!(10, 11), "a"}},
            },
        );
    }

    #[test]
    fn parses_while() {
        check(
            "while 1 do a",
            ast! {expr, while, span!(0, 12),
                ast! {expr, int, span!(6, 7), 1},
                ast! {expr, lvalue, span!(11, 12), ast! {lvalue, simple, span!(11, 12), "a"}},
            },
        );
    }

    #[test]
    fn parses_for() {
        check(
            "for i := 1 to 10 do a",
            ast! {expr, for, span!(0, 21),
                ast! {ident, span!(4, 5), "i"},
                ast! {expr, int, span!(9, 10), 1},
                ast! {expr, int, span!(14, 16), 10},
                ast! {expr, lvalue, span!(20, 21), ast! {lvalue, simple, span!(20, 21), "a"}},
            },
        );
    }

    #[test]
    fn parses_assign() {
        check(
            "a.b := 3",
            ast! {expr, assign, span!(0, 8),
                ast! {lvalue, field, span!(0, 3),
                    ast! {lvalue, simple, span!(0, 1), "a"},
                    ast! {ident, span!(2, 3), "b"},
                },
                ast! {expr, int, span!(7, 8), 3},
            },
        );
    }

    #[test]
    fn parses_let() {
        check(
            "let in a",
            ast! {expr, let, span!(0, 8),
                vec![],
                ast! {expr, lvalue, span!(7, 8), ast! {lvalue, simple, span!(7, 8), "a"}},
            },
        );
    }

    #[test]
    fn parses_break() {
        check("break", ast! {expr, break, span!(0, 5)});
    }
}
