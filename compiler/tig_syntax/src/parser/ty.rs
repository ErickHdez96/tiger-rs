use super::*;
use tig_ast::ast;

impl Parser {
    pub(super) fn parse_type(&mut self) -> PResult<ast::Type> {
        let t = self.next();
        match t.kind {
            TokenKind::Ident(id) => Ok(ast! {type, name, t.span, ast!{ident, t.span, id}}),
            _ => Err(SError!(t.span, "Expected a type, found `{}`", t.kind)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tig_ast::Type;
    use tig_common::Span;

    macro_rules! span {
        ($lo:expr, $hi:expr $(,)?) => {
            Span::new($lo as u32, $hi as u32)
        };
    }

    fn check(input: &str, expected: Type) {
        let tokens = tokenize(input);
        let mut p = Parser::new(tokens);
        let parsed = p.parse_type().expect("Could not parse");
        assert_eq!(parsed, expected);
    }

    #[test]
    fn test_name_type() {
        check(
            "int",
            ast! {type, name, span!(0, 3), ast!{ident, span!(0, 3), "int"}},
        );
    }
}
