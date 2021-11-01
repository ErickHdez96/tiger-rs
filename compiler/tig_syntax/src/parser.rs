use crate::{tokenize, Token};
use chumsky::{error::Simple, stream::Stream, Parser};
use tig_ast::Program;

pub type PError = Simple<Token>;
//type PStream<'a> = Stream<'a, Token, Range<usize>, PError>;

pub fn parse_str(input: &str) -> (Option<Program>, Vec<PError>) {
    let tokens = tokenize(input);
    let stream = Stream::from_iter(
        tokens.iter().last().map(|(_, s)| s.clone()).unwrap(),
        tokens.into_iter(),
    );

    let (ast, parse_errs) = parsers::program_parser()
    .parse_recovery(stream);

    (ast, parse_errs)
}

mod parsers {
    use super::PError;
    use crate::{Token, T};
    use chumsky::prelude::*;
    use chumsky::{error::Simple, Parser};
    use tig_ast::{Expr, ExprKind, FieldExpr, Program, VarKind};

    pub fn expr_parser() -> impl Parser<Token, Expr, Error = PError> + Clone {
        recursive(|expr| {
            let raw_expr = recursive(|_raw_expr| {
                // nil
                // <integer>
                // <string>
                let val = filter_map(|span, tok| match tok {
                    Token::Nil => Ok(ExprKind::Nil),
                    Token::Number(n) => Ok(ExprKind::Int(n.parse().unwrap())),
                    Token::String(s) => Ok(ExprKind::String(s)),
                    _ => Err(Simple::expected_input_found(span, vec![], Some(tok))),
                })
                .labelled("value");

                // <id>
                let ident = filter_map(|span, tok| match tok {
                    Token::Ident(id) => Ok(id.clone()),
                    _ => Err(Simple::expected_input_found(span, vec![], Some(tok))),
                })
                    .labelled("identifier");

                let ident_span = ident.clone().map_with_span(|i, s| (i, s));

                let lvalue = recursive(|lvalue| {
                    ident_span.clone().debug(1)
                        .map(|id| VarKind::Simple(id))
                        .or(lvalue.clone()
                            .then_ignore(just(T![.]))
                            .then(ident_span.clone())
                            .map(|(lv, id)| VarKind::Field(Box::new(lv), id)))
                        .or(lvalue.clone()
                            .then(expr.clone().delimited_by(T!['['], T![']']))
                            .map(|(lv, expr)| VarKind::Subscript(Box::new(lv), Box::new(expr))))
                        .map_with_span(|lv, s| (lv, s))
                })
                    .labelled("value");

                // array <type-id> `[` <exp> `]` of `[` <exp> `]`
                let array_creation = just(T![array])
                    .ignore_then(ident_span.clone())
                    .then(expr.clone().delimited_by(T!['['], T![']']))
                    .then_ignore(just(T![of]))
                    .then(expr.clone())
                    .map(|((ty, size), init)|
                        ExprKind::Array {
                            ty,
                            size: Box::new(size),
                            init: Box::new(init),
                        },
                    )
                    .labelled("array");

                // <type-id> `{` [ <id> `=` <exp> {, <id> `=` <exp> } ] `}`
                let record_field = ident_span.clone()
                    .then_ignore(just(T![=]))
                    .then(expr.clone())
                    .map(|(field, expr)| FieldExpr {
                        field,
                        expr,
                    });
                let record_creation = ident_span.clone()
                    .then(
                        record_field.clone()
                            .chain(just(T![,]).ignore_then(record_field).repeated())
                            .then_ignore(just(T![,]).or_not())
                            .or_not()
                            .map(|fields| fields.unwrap_or_else(Vec::new))
                            .delimited_by(T!['{'], T!['}'])
                    )
                    .map(|(ty, fields)| ExprKind::Record { ty, fields });

                let dif = record_creation
                    .or(lvalue.map(ExprKind::Var));
                let atom = dif
                    .or(val)
                    .or(array_creation)
                    .map_with_span(|e, s| (e, s))
                    .or(expr.clone().delimited_by(T!['('], T![')']));

                atom
            });

            // if ::= if <expr> then <expr> (else <expr>)
            let if_ = just(Token::If)
                .ignore_then(expr.clone())
                // Parsing an expression for the then branch, handles the issue with the dangling else.
                // The innermost if will eat the closest else.
                .then(just(Token::Then).ignore_then(expr.clone()))
                // Optional else
                .then(just(Token::Else).ignore_then(expr.clone()).or_not())
                .map_with_span(|((cond, a), b), span| {
                    (
                        ExprKind::If {
                            test: Box::new(cond),
                            then_branch: Box::new(a),
                            else_branch: b.map(Box::new),
                        },
                        span,
                    )
                });

            if_.or(raw_expr.clone())
        })
    }

    pub fn program_parser() -> impl Parser<Token, Program, Error = PError> + Clone {
        expr_parser().map(Program::Expr).then_ignore(end())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tig_ast::ast;

    fn check(input: &str, expected: Program) {
        let (p, _e) = parse_str(input);
        dbg!(_e);
        let p = p.expect("Should parse correctly");
        assert_eq!(p, expected);
    }

    #[test]
    fn parses_if_else_expr() {
        check(
            r#"if a then "Hi" else "Hello""#,
            ast! {prog_expr,
                ast!{expr, if_else, 0..27,
                    ast!{expr, varsimple, 3..4, "a"},
                    ast!{expr, str, 10..14, "\"Hi\""},
                    ast!{expr, str, 20..27, "\"Hello\""},
                },
            },
        );
    }

    #[test]
    fn parses_if_expr() {
        check(
            "if a then 3",
            ast! {prog_expr,
                ast!{expr, if, 0..11,
                    ast!{expr, varsimple, 3..4, "a"},
                    ast!{expr, int, 10..11, 3},
                },
            },
        );
    }

    #[test]
    fn handles_if_ambiguity() {
        check(
            "if a then if b then c else nil",
            ast! {prog_expr,
                ast!{expr, if, 0..30,
                    ast!{expr, varsimple, 3..4, "a"},
                    ast!{expr, if_else, 10..30,
                        ast!{expr, varsimple, 13..14, "b"},
                        ast!{expr, varsimple, 20..21, "c"},
                        ast!{expr, nil, 27..30},
                    },
                },
            },
        );
    }

    #[test]
    fn array_creation() {
        check(
            "array int[10] of 0",
            ast! {prog_expr,
                ast!{expr, array, 0..18,
                    ast!{ident, 6..9, "int"},
                    ast!{expr, int, 10..12, 10},
                    ast!{expr, int, 17..18, 0},
                },
            },
        );
    }

    #[test]
    fn empty_record_creation() {
        check(
            "empty {}",
            ast! {prog_expr,
                ast!{expr, record, 0..8,
                    ast!{ident, 0..5, "empty"},
                    vec![],
                },
            },
        );
    }

    #[test]
    fn one_field_record_creation() {
        check(
            "one { a = 3 }",
            ast! {prog_expr,
                ast!{expr, record, 0..13,
                    ast!{ident, 0..3, "one"},
                    vec![
                        ast!{recordfield,
                            ast!{ident, 6..7, "a"},
                            ast!{expr, int, 10..11, 3},
                        },
                    ],
                },
            },
        );
    }

    #[test]
    fn two_field_record_creation() {
        check(
            "one { a = 3, b = 4, }",
            ast! {prog_expr,
                ast!{expr, record, 0..21,
                    ast!{ident, 0..3, "one"},
                    vec![
                        ast!{recordfield,
                            ast!{ident, 6..7, "a"},
                            ast!{expr, int, 10..11, 3},
                        },
                        ast!{recordfield,
                            ast!{ident, 13..14, "b"},
                            ast!{expr, int, 17..18, 4},
                        },
                    ],
                },
            },
        );
    }

    #[test]
    fn parses_lvalues() {
        check(
            "a[3]",
            ast!{prog_expr,
                ast!{expr, var, 0..4,
                    ast!{var, subscript, 0..4,
                        ast!{var, simple, 0..1, "a"},
                        ast!{expr, int, 2..3, 3},
                    },
                },
            },
        );
    }
}
