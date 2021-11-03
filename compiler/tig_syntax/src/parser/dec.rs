use super::*;
use crate::T;
use tig_ast::ast;
use tig_common::SmolStr;

// x - Implemented
// - - Incomplete
//   - Not implemented
//
// - decs ::= { dec }
// - dec ::=
//     # Type declaration.
// x     type id = ty
//     # Class definition (alternative form).
//     | class id [ extends type-id ] { classfields }
//     # Variable declaration.
// x   | vardec
//     # Function declaration.
// x   | function id ( tyfields ) [ : type-id ] = exp
//     # Primitive declaration.
// x   | primitive id ( tyfields ) [ : type-id ]
//     # Importing a set of declarations.
//     | import string
//
//
// x vardec ::= var id [ : type-id ] := exp
//
//
//   classfields ::= { classfield }
//   # Class fields.
//   classfield ::=
//     # Attribute declaration.
//       vardec
//     # Method declaration.
//     | method id ( tyfields ) [ : type-id ] = exp
//
// x tyfields ::= [ id : type-id { , id : type-id } ]

#[derive(Debug)]
enum DecKind {
    F(ast::Fundec),
    V(ast::Vardec),
    P(ast::Primitivedec),
    I(SmolStr),
    T(ast::Typedec),
}

impl Parser {
    pub(super) fn parse_decs(&mut self) -> PResult<Vec<ast::Dec>> {
        let mut decs = vec![];
        let mut f_decs: Vec<ast::Fundec> = vec![];
        let mut t_decs: Vec<ast::Typedec> = vec![];
        let mut start_span = self.peek().span;
        let mut last_span = self.peek().span;

        while can_start_dec(&self.peek().kind) {
            // Declarations in Tiger work in a weird way.
            // All adjacent function/type declarations are treated as possibly
            // mutually recursive, so they're grouped together.
            // If we encounter multiple adjacent function/type declarations,
            // we have to group them together.
            let (decspan, dec) = self.parse_dec()?;
            match dec {
                DecKind::F(fdec) => {
                    // Flush the typedecs if any
                    if !t_decs.is_empty() {
                        decs.push(
                            ast!{dec, ty, start_span.extend(last_span), std::mem::take(&mut t_decs)}
                        );
                    }
                    if f_decs.is_empty() {
                        start_span = decspan;
                    }
                    f_decs.push(fdec);
                }
                DecKind::V(_) | DecKind::P(_) | DecKind::I(_) => {
                    if !f_decs.is_empty() {
                        decs.push(
                            ast!{dec, fn, start_span.extend(last_span), std::mem::take(&mut f_decs)}
                            );
                    }
                    if !t_decs.is_empty() {
                        decs.push(
                            ast!{dec, ty, start_span.extend(last_span), std::mem::take(&mut t_decs)}
                            );
                    }

                    match dec {
                        DecKind::V(vdec) => {
                            decs.push(ast! {dec, var, decspan, vdec});
                        }
                        DecKind::P(odec) => {
                            decs.push(ast! {dec, primitive, decspan, odec});
                        }
                        DecKind::I(import) => {
                            decs.push(ast! {dec, import, decspan, import});
                        }
                        _ => {
                            unreachable!()
                        }
                    }
                }
                DecKind::T(tdec) => {
                    if !f_decs.is_empty() {
                        decs.push(
                            ast!{dec, fn, start_span.extend(last_span), std::mem::take(&mut f_decs)}
                            );
                    }
                    if t_decs.is_empty() {
                        start_span = decspan;
                    }

                    t_decs.push(tdec);
                }
            }
            last_span = decspan;
        }

        if !f_decs.is_empty() {
            decs.push(ast! {dec, fn, start_span.extend(last_span), std::mem::take(&mut f_decs)});
        }
        if !t_decs.is_empty() {
            decs.push(ast! {dec, ty, start_span.extend(last_span), std::mem::take(&mut t_decs)});
        }

        Ok(decs)
    }

    fn parse_dec(&mut self) -> PResult<(Span, DecKind)> {
        let t = self.peek();
        match t.kind {
            T![function] => self.parse_functiondec(),
            T![primitive] => self.parse_primitivedec(),
            T![var] => self.parse_vardec(),
            T![type] => self.parse_typedec(),
            T![import] => {
                let start = self.next().span;
                let (end_span, import) = self.eat_string()?;
                Ok((start.extend(end_span), DecKind::I(import)))
            }
            _ => Err(SError!(
                t.span,
                "Expected function, primitive, var or type, found `{}`",
                t.kind
            )),
        }
    }

    /// function <ident> `(` <params> `)` `=` <body>
    fn parse_functiondec(&mut self) -> PResult<(Span, DecKind)> {
        let start = self.next().span;
        let name = self.eat_ident()?;
        self.eat(&T!['('])?;
        let params = self.parse_params()?;
        self.eat(&T![')'])?;
        let ty = if self.peek().kind == T![:] {
            self.next();
            Some(self.eat_ident()?)
        } else {
            None
        };
        self.eat(&T![=])?;
        let body = self.parse_expr()?;
        Ok((
            start.extend(body.span),
            DecKind::F(ast! {fundec, name, params, ty, body}),
        ))
    }

    /// primitive <ident> `(` <params> `)`
    fn parse_primitivedec(&mut self) -> PResult<(Span, DecKind)> {
        let start = self.next().span;
        let name = self.eat_ident()?;
        self.eat(&T!['('])?;
        let params = self.parse_params()?;
        let rparen_span = self.eat(&T![')'])?.span;
        let (ty, end_span) = if self.peek().kind == T![:] {
            self.next();
            let ty = self.eat_ident()?;
            let end_span = ty.span;
            (Some(ty), end_span)
        } else {
            (None, rparen_span)
        };
        Ok((
            start.extend(end_span),
            DecKind::P(ast! {primitivedec, name, params, ty}),
        ))
    }

    fn parse_params(&mut self) -> PResult<Vec<ast::Field>> {
        let mut fields = vec![];
        loop {
            match self.peek() {
                Token {
                    span,
                    kind: TokenKind::Ident(id),
                } => {
                    let span = *span;
                    let id = id.clone();
                    self.next();
                    self.eat(&T![:])?;
                    let ty = self.eat_ident()?;
                    fields.push(ast::Field {
                        field: ast::Ident { span, value: id },
                        escape: false,
                        ty,
                    });
                }
                _ => break,
            }

            if self.peek().kind == T![,] {
                self.next();
            } else {
                break;
            }
        }
        Ok(fields)
    }

    /// var <ident> [ `:` <type-id> ] `:=` <init>
    fn parse_vardec(&mut self) -> PResult<(Span, DecKind)> {
        let start = self.next().span;
        let name = self.eat_ident()?;
        let ty = if self.peek().kind == T![:] {
            self.next();
            Some(self.eat_ident()?)
        } else {
            None
        };
        self.eat(&T![:=])?;
        let init = self.parse_expr()?;
        Ok((
            start.extend(init.span),
            DecKind::V(ast! {vardec, name, false, ty, init}),
        ))
    }

    /// type <ident> `=` <type>
    fn parse_typedec(&mut self) -> PResult<(Span, DecKind)> {
        let start = self.next().span;
        let name = self.eat_ident()?;
        self.eat(&T![=])?;
        let ty = self.parse_type()?;
        Ok((start.extend(ty.span), DecKind::T(ast! {tydec, name, ty})))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tig_common::Span;

    macro_rules! span {
        ($lo:expr, $hi:expr $(,)?) => {
            Span::new($lo as u32, $hi as u32)
        };
    }

    fn check(input: &str, expected: &[ast::Dec]) {
        let tokens = tokenize(input);
        let mut p = Parser::new(tokens);
        let parsed = p.parse_decs().expect("Could not parse");
        assert_eq!(&parsed, expected);
    }

    #[test]
    fn parses_main() {
        check(
            "function _main () = nil",
            &[ast! {
                dec, fn, span!(0, 23),
                vec![
                    ast!{
                        fundec,
                        ast!{ident, span!(9, 14), "_main"},
                        vec![],
                        None,
                        ast!{expr, nil, span!(20, 23)},
                    },
                ],
            }],
        );
    }

    #[test]
    fn parses_function_dec() {
        check(
            "function a (a: int, b: string): int = 3",
            &[ast! {
                dec, fn, span!(0, 39),
                vec![
                    ast!{
                        fundec,
                        ast!{ident, span!(9, 10), "a"},
                        vec![
                            ast!{param,
                                ast!{ident, span!(12, 13), "a"},
                                ast!{ident, span!(15, 18), "int"},
                            },
                            ast!{param,
                                ast!{ident, span!(20, 21), "b"},
                                ast!{ident, span!(23, 29), "string"},
                            },
                        ],
                        Some(ast!{ident, span!(32, 35), "int"}),
                        ast!{expr, int, span!(38, 39), 3},
                    },
                ],
            }],
        );
    }

    #[test]
    fn parses_primitive_dec() {
        check(
            "primitive atoi(s: string): int",
            &[ast! {
                dec, primitive, span!(0, 30),
                    ast!{
                        primitivedec,
                        ast!{ident, span!(10, 14), "atoi"},
                        vec![
                            ast!{param,
                                ast!{ident, span!(15, 16), "s"},
                                ast!{ident, span!(18, 24), "string"},
                            },
                        ],
                        Some(ast!{ident, span!(27, 30), "int"}),
                    },
            }],
        );
    }

    #[test]
    fn parses_var() {
        check(
            "var a := 1",
            &[ast! {
                dec, var, span!(0, 10),
                ast!{
                    vardec,
                    ast!{ident, span!(4, 5), "a"},
                    false,
                    None,
                    ast!{expr, int, span!(9, 10), 1},
                },
            }],
        );

        check(
            "var a: int := 1",
            &[ast! {
                dec, var, span!(0, 15),
                ast!{
                    vardec,
                    ast!{ident, span!(4, 5), "a"},
                    false,
                    Some(ast!{ident, span!(7, 10), "int"}),
                    ast!{expr, int, span!(14, 15), 1},
                },
            }],
        );
    }

    #[test]
    fn parses_typedec() {
        check(
            "type a = int",
            &[ast! {
                dec, ty, span!(0, 12),
                vec![
                    ast!{
                        tydec,
                        ast!{ident, span!(5, 6), "a"},
                        ast!{type, name, span!(9, 12), ast!{ident, span!(9, 12), "int"}},
                    },
                ]
            }],
        );
    }

    #[test]
    fn parses_import() {
        check(
            "import \"std\"",
            &[ast! {
                dec, import, span!(0, 12),
                "\"std\"",
            }],
        );
    }
}
