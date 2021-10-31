use crate::{tokenize, Token};
use chumsky::{error::Simple, stream::Stream, Parser};
use tig_ast::Program;

pub fn parse_str(input: &str) -> (Option<Program>, Vec<Simple<Token>>) {
    let tokens = tokenize(input);
    let stream = Stream::from_iter(
        tokens.iter().last().map(|(_, s)| s.clone()).unwrap(),
        //input.len()..(input.len() + 1),
        tokens.into_iter(),
    );

    let (ast, parse_errs) = parsers::program_parser().parse_recovery(stream);

    (ast, parse_errs)
}

mod parsers {
    use crate::{Token, T};
    use chumsky::prelude::*;
    use chumsky::{error::Simple, Parser};
    use tig_ast::{Expr, ExprKind, Program, VarKind};

    pub fn expr_parser() -> impl Parser<Token, Expr, Error = Simple<Token>> + Clone {
        recursive(|expr| {
            let raw_expr = recursive(|_raw_expr| {
                let val = filter_map(|span, tok| match tok {
                    Token::Nil => Ok(ExprKind::Nil),
                    Token::Number(n) => Ok(ExprKind::Int(n.parse().unwrap())),
                    Token::String(s) => Ok(ExprKind::String(s)),
                    _ => Err(Simple::expected_input_found(span, vec![], Some(tok))),
                })
                .labelled("value");

                let ident = filter_map(|span, tok| match tok {
                    Token::Ident(id) => Ok(id.clone()),
                    _ => Err(Simple::expected_input_found(span, vec![], Some(tok))),
                })
                    .labelled("identifier");

                let ident_span = ident.clone().map_with_span(|i, s| (i, s));

                let array_creation = ident_span
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

                let atom = val
                    .or(array_creation)
                    .or(ident
                        .map(VarKind::Simple)
                        .map_with_span(|e, s| (e, s))
                        .map(ExprKind::Var))
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

    pub fn program_parser() -> impl Parser<Token, Program, Error = Simple<Token>> + Clone {
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
                    ast!{expr, var, 3..4, "a"},
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
                    ast!{expr, var, 3..4, "a"},
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
                    ast!{expr, var, 3..4, "a"},
                    ast!{expr, if_else, 10..30,
                        ast!{expr, var, 13..14, "b"},
                        ast!{expr, var, 20..21, "c"},
                        ast!{expr, nil, 27..30},
                    },
                },
            },
        );
    }

    #[test]
    fn array_creation() {
        check(
            "int[10] of 0",
            ast! {prog_expr,
                ast!{expr, array, 0..12,
                    ast!{ident, 0..3, "int"},
                    ast!{expr, int, 4..6, 10},
                    ast!{expr, int, 11..12, 0},
                },
            },
        );
    }
}
