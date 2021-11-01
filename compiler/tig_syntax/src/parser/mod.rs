mod dec;
mod expr;
mod ty;

use tig_ast as ast;
use tig_ast::ast;
use tig_common::Span;
use tig_error::{SError, SpannedError};
use crate::{tokenize, Token, TokenKind};

type PResult<T> = Result<T, SpannedError>;

pub fn parse_string(input: &str) -> PResult<ast::Program> {
    let tokens = tokenize(input);
    let mut p = Parser::new(tokens);
    p.parse()
}

#[derive(Debug)]
struct Tokens {
    tokens: Vec<Token>,
    offset: usize,
    dummy: Token,
}

impl Tokens {
    fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens,
            offset: 0,
            dummy: Token::dummy(),
        }
    }

    fn peek_nth(&self, n: usize) -> &Token {
        self.tokens.get(self.offset + n).unwrap_or(&self.dummy)
    }

    fn peek(&self) -> &Token {
        self.peek_nth(0)
    }

    fn at_eof(&self) -> bool {
        self.offset >= self.tokens.len() - 1
    }

    fn next(&mut self) -> Token {
        match self.tokens.get_mut(self.offset) {
            None => Token::dummy(),
            Some(elem) => {
                self.offset += 1;
                std::mem::replace(elem, Token::dummy())
            }
        }
    }
}

#[derive(Debug)]
struct Parser {
    tokens: Tokens,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens: Tokens::new(tokens),
        }
    }

    fn parse(&mut self) -> PResult<ast::Program> {
        let res = if can_start_expr(&self.peek().kind) {
            self.parse_expr().map(ast::Program::Expr)
        } else if can_start_dec(&self.peek().kind) {
            self.parse_decs().map(ast::Program::Decs)
        } else {
            let t = self.peek();
            Err(SError!(
                t.span,
                "Expected an expression or a declaration, found `{}`",
                t.kind
            ))
        };

        if !self.tokens.at_eof() {
            // Force any parser error to bubble up first
            res?;
            let t = self.peek();
            Err(SError!(t.span, "Expected <eof>, found `{}`", t.kind))
        } else {
            res
        }
    }

    fn parse_int(&self, int: &str, span: Span) -> PResult<u64> {
        int.parse::<u64>()
            // The lexer already makes sure an integer is only [0-9]
            // Hence, only possible error is integer overflow
            .map_err(|_| SError!(span, "Integer too large to fit in 64 bits"))
    }

    fn peek(&self) -> &Token {
        self.tokens.peek()
    }

    fn next(&mut self) -> Token {
        self.tokens.next()
    }

    fn eat_ident(&mut self) -> PResult<ast::Ident> {
        match self.next() {
            Token {
                span,
                kind: TokenKind::Ident(id),
            } => Ok(ast! {ident, span, id}),
            Token { span, kind } => Err(SError!(span, "Expected an identifier, found `{}`", kind)),
        }
    }

    fn eat(&mut self, kind: &TokenKind) -> PResult<Token> {
        let t = self.next();
        if &t.kind == kind {
            Ok(t)
        } else {
            Err(SError!(t.span, "Expected `{}`, found `{}`", kind, t.kind))
        }
    }
}

/// Test whether a token can appear at the start of an expression.
fn can_start_expr(kind: &TokenKind) -> bool {
    use TokenKind::*;
    matches!(kind, Nil)
}

/// Test whether a token can appear at the start of a declaration.
fn can_start_dec(kind: &TokenKind) -> bool {
    use TokenKind::*;
    matches!(kind, Function | Var | Type)
}
