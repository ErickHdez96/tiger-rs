use super::*;
use crate::T;
use tig_ast::ast;

#[derive(Debug)]
enum DecKind {
    F(ast::Fundec),
    V(ast::Vardec),
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
                DecKind::V(vdec) => {
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
                    decs.push(ast! {dec, var, decspan, vdec});
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
            TokenKind::Function => self.parse_functiondec(),
            TokenKind::Var => self.parse_vardec(),
            TokenKind::Type => self.parse_typedec(),
            _ => Err(SError!(
                t.span,
                "Expected function, var or type, found `{}`",
                t.kind
            )),
        }
    }

    /// function <ident> (<params>) = <body>
    fn parse_functiondec(&mut self) -> PResult<(Span, DecKind)> {
        let start = self.next().span;
        let name = self.eat_ident()?;
        self.eat(&T!['('])?;
        self.eat(&T![')'])?;
        self.eat(&T![=])?;
        let body = self.parse_expr()?;
        Ok((
            start.extend(body.span),
            DecKind::F(ast! {fundec, name, vec![], None, body}),
        ))
    }

    /// var <ident> := <init>
    fn parse_vardec(&mut self) -> PResult<(Span, DecKind)> {
        let start = self.next().span;
        let name = self.eat_ident()?;
        self.eat(&T![:=])?;
        let init = self.parse_expr()?;
        Ok((
            start.extend(init.span),
            DecKind::V(ast! {vardec, name, false, None, init}),
        ))
    }

    /// type <ident> = <type>
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
    fn test_main() {
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
    fn test_var() {
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
    }

    #[test]
    fn test_typedec() {
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
}
