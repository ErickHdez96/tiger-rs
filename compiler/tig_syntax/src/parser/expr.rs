use super::*;
use tig_ast::ast;

impl Parser {
    pub(super) fn parse_expr(&mut self) -> PResult<ast::Expr> {
        self.parse_bp(0)
    }

    fn parse_bp(&mut self, min_bp: u8) -> PResult<ast::Expr> {
        let mut left = self.parse_atom()?;

        loop {
            //if let Some((l_bp, ()) = postfix_binding_power(&self.peek().kind) {
            //    if l_bp < min_bp {
            //        break;
            //    }
            //    self.next();
            //    continue;
            //}

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

    fn parse_atom(&mut self) -> PResult<ast::Expr> {
        match self.next() {
            Token {
                span,
                kind: TokenKind::Nil,
            } => Ok(ast! {expr, nil, span}),
            Token {
                span,
                kind: TokenKind::Ident(id),
            } => Ok(ast! {expr, var, span, id}),
            Token {
                span,
                kind: TokenKind::Int(n),
            } => Ok(ast! {expr, int, span, self.parse_int(&n, span)?}),
            Token { span, kind } => Err(SError!(span, "Expected an expression, found `{}`", kind)),
        }
    }
}

//fn postfix_binding_power(kind: &TokenKind) -> Option<(u8, u8)> {
//    None
//}

fn infix_binding_power(kind: &TokenKind) -> Option<(ast::BinOp, u8, u8)> {
    Some(match kind {
        TokenKind::Plus => (ast::BinOp::Add, 5, 6),
        TokenKind::Minus => (ast::BinOp::Sub, 5, 6),
        TokenKind::Star => (ast::BinOp::Mul, 7, 8),
        TokenKind::Slash => (ast::BinOp::Div, 7, 8),
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
    fn test_nil() {
        check("nil", ast! {expr, nil, span!(0, 3)});
    }

    #[test]
    fn test_simple_var() {
        check("a", ast! {expr, var, span!(0, 1), "a"});
    }

    #[test]
    fn test_operator_precedence() {
        check(
            "0 - 1 * 3 + 2 / 1",
            ast! {
                expr, binop, span!(0, 17),
                binop!(+),
                ast!{
                    expr, binop, span!(0, 9),
                    binop!(-),
                    ast!{expr, int, span!(0, 1), 0},
                    ast!{
                        expr, binop, span!(4, 9),
                        binop!(*),
                        ast!(expr, int, span!(4, 5), 1),
                        ast!(expr, int, span!(8, 9), 3),
                    },
                },
                ast!{
                    expr, binop, span!(12, 17),
                    binop!(/),
                    ast!{expr, int, span!(12, 13), 2},
                    ast!{expr, int, span!(16, 17), 1},
                },
            },
        );
    }
}
