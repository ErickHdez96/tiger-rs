use super::*;
use crate::T;
use tig_ast::ast;

// x - Implemented
// - - Incomplete
//   - Not implemented
//
//   # Types.
//   ty ::=
//      # Type alias.
// x      type-id
//      # Record type definition.
// x    | { tyfields  }
//      # Array type definition.
//      | array of type-id
//      # Class definition (canonical form).
//      | class [ extends type-id ] { classfields }
//   tyfields ::= [ id : type-id { , id : type-id } ]
//   type-id ::= id

impl Parser {
    pub(super) fn parse_type(&mut self) -> PResult<ast::Type> {
        let t = self.next();
        match t.kind {
            TokenKind::Ident(id) => Ok(ast! {type, name, t.span, ast!{ident, t.span, id}}),
            T!['{'] => {
                let tyfields = self.parse_tyfields()?;
                let end = self.eat(&T!['}'])?;
                Ok(ast::Type {
                    span: t.span.extend(end.span),
                    kind: ast::TypeKind::Record(tyfields),
                })
            }
            T![array] => {
                self.eat(&T![of])?;
                let ty = self.eat_ident()?;
                Ok(ast::Type {
                    span: t.span.extend(ty.span),
                    kind: ast::TypeKind::Array(ty),
                })
            }
            _ => Err(SError!(t.span, "Expected a type, found `{}`", t.kind)),
        }
    }

    fn parse_tyfields(&mut self) -> PResult<Vec<ast::Field>> {
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
                        // TODO: is this necessary?
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

    #[test]
    fn test_record_type() {
        check(
            "{ name: string, age: int, }",
            ast! {type, record, span!(0, 27),
                {
                    ast! {ident, span!(2, 6), "name"} => ast! {ident, span!(8, 14), "string"},
                    ast! {ident, span!(16, 19), "age"} => ast! {ident, span!(21, 24), "int"},
                },
            },
        );
    }

    #[test]
    fn test_array_type() {
        check(
            "array of int",
            ast! {type, array, span!(0, 12), ast!{ident, span!(9, 12), "int"}},
        );
    }
}
