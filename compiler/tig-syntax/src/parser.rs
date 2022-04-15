mod expr;
mod stmt;
mod ty;

use std::{collections::HashSet, io, path::PathBuf};

use smol_str::SmolStr;
use tig_common::{SourceCode, SourceFile, Span};
use tig_error::ParserError;

use crate::{
    ast::{self, Program},
    lexer::{tokenize_source_file, LexerResult, Token, TokenKind},
    T,
};

/// The tokens that can begin a declaration.
const DECLARATION_START_TOKENS: [TokenKind; 5] = [
    T![type],
    //T![class],
    T![var],
    T![function],
    T![primitive],
    T![import],
];

/// The tokens that can begin a declaration.
const TYPE_START_TOKENS: [TokenKind; 3] = [
    TokenKind::Id(SmolStr::new_inline("")),
    T!['{'],
    T![array],
    //T![class],
];

/// Parses a file, possibly more if it contains imports.
pub fn parse_file(file_path: impl Into<PathBuf>) -> io::Result<(SourceCode, ParseResult)> {
    let mut source_code = SourceCode::default();
    let mut parser = Parser::from_source_code(&mut source_code);
    parser.add_file(file_path)?;
    let result = parser.parse();
    Ok((source_code, result))
}

/// Parses a file, possibly more if it contains imports.
pub fn parse_source_code(source_code: &mut SourceCode) -> ParseResult {
    let parser = Parser::from_source_code(source_code);
    parser.parse()
}

/// Parses a file, possibly more if it contains imports.
pub fn parse_str(input: impl Into<String>) -> (SourceCode, ParseResult) {
    let input = input.into();
    let mut source_code = SourceCode::new(vec![SourceFile::from_string(input, 0)]);
    let parser = Parser::from_source_code(&mut source_code);
    let result = parser.parse();
    (source_code, result)
}

/// The result of parsing a program. The parser tries to catch multiple parser errors, by jumping
/// to the next appropriate boundary (e.g. function, let, in, etc.). However, the AST cannot be
/// partially built, so while the parser can return multiple errors, it may not be able to build
/// the AST if any errors were found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseResult {
    pub program: Option<Program>,
    pub errors: Vec<ParserError>,
}

/// A global parser for a whole Tiger's program. Files can be added one after the other, in which
/// case they will be parsed in that order.
///
/// ### Imports
///
/// Tiger has the possibility of importing other files. The way the parser deals with that, is by
/// tokenizing the imported file, and insert the tokens into the stream, exactly between the import
/// and the next token. In other words, once the parser is done parsing an import, the next token
/// it will read will be the first token from the imported file.
#[derive(Debug)]
struct Parser<'s> {
    source_code: &'s mut SourceCode,
    errors: Vec<ParserError>,
    tokens: TokenStream,

    /// When calling a maybe_expect, the expected token will be pushed here if it didn't match.  
    /// The next call to `next` will clear it.
    /// The next call to an expect method which fails, will generate an error message including
    /// this array in the expected one of list.
    expected: HashSet<TokenKind>,
}

// To allow to use ?.
type PResult<T> = Result<T, ()>;

impl<'s> Parser<'s> {
    fn from_source_code(source_code: &'s mut SourceCode) -> Self {
        Self {
            source_code,
            errors: vec![],
            tokens: TokenStream::default(),
            expected: HashSet::new(),
        }
    }

    fn add_file(&mut self, file_path: impl Into<PathBuf>) -> io::Result<&SourceFile> {
        self.source_code.add_file(file_path)
    }

    fn tokenize_files(&mut self) {
        for file in self.source_code.files().iter().rev() {
            let LexerResult {
                tokens,
                unterminated_comment,
            } = tokenize_source_file(file);
            self.tokens.push_tokens(tokens);

            if let Some(span) = unterminated_comment {
                self.errors
                    .push(ParserError::new("Unterminated comment", span));
            }
        }
    }

    /// Get the next token without advancing the pointer.
    fn next(&mut self) -> Token {
        self.expected.clear();
        self.tokens.next()
    }

    /// Get the next token without advancing the pointer.
    fn peek(&self) -> &Token {
        self.tokens.peek()
    }

    fn at_eof(&self) -> bool {
        self.tokens.at_eof()
    }

    fn parse(mut self) -> ParseResult {
        self.tokenize_files();

        let program = self.parse_program();

        ParseResult {
            program,
            errors: self.errors,
        }
    }

    fn parse_program(&mut self) -> Option<Program> {
        if can_start_dec(&self.peek().kind) {
            self.parse_decs(&T![eof]).ok().map(Program::Decs)
        } else {
            self.parse_expr().ok().map(Program::Expr)
        }
    }

    /// Skip tokens until one of the `boundary` tokens is found, or eof is reached.
    fn synchronize(&mut self, boundary: &[TokenKind]) {
        while !self.at_eof() {
            let current = &self.peek().kind;
            for expected in boundary {
                if current == expected {
                    return;
                }
            }

            self.next();
        }
    }

    fn maybe_expect(&mut self, kind: &TokenKind) -> Option<Token> {
        if &self.peek().kind == kind {
            Some(self.next())
        } else {
            self.expected.insert(kind.clone());
            None
        }
    }

    fn maybe_expect_ident(&mut self) -> Option<ast::Ident> {
        match self.peek() {
            Token {
                kind: TokenKind::Id(id),
                span,
            } => {
                let ident = ast::Ident {
                    span: *span,
                    value: id.clone(), // SmolStr clonning is O(1)
                };
                self.next();
                Some(ident)
            }
            _ => {
                self.expected.insert(TokenKind::Id(SmolStr::new_inline("")));
                None
            }
        }
    }

    fn expect(&mut self, kind: &TokenKind) -> PResult<Token> {
        if &self.peek().kind == kind {
            Ok(self.next())
        } else {
            self.expected_one(kind);
            Err(())
        }
    }

    fn expect_ident(&mut self) -> PResult<ast::Ident> {
        match self.peek() {
            Token {
                kind: TokenKind::Id(id),
                span,
            } => {
                let ident = ast::Ident {
                    span: *span,
                    value: id.clone(), // SmolStr clonning is O(1)
                };
                self.next();
                Ok(ident)
            }
            _ => {
                self.expected_one(&T![id, ""]);
                Err(())
            }
        }
    }

    fn expect_string(&mut self) -> PResult<(SmolStr, Span)> {
        match self.peek() {
            Token {
                kind: TokenKind::String { value, terminated },
                span,
            } => {
                let span = *span;
                let value = value.clone(); // SmolStr clone is O(1)
                if !terminated {
                    self.errors
                        .push(ParserError::new("Unterminated string".to_string(), span));
                }
                self.next();

                Ok((value, span))
            }

            _ => {
                self.expected_one(&T![str, ""]);
                Err(())
            }
        }
    }

    /// Push an error, saying one of the `self.expected` tokens were expected, but the current
    /// token was found.
    fn expected(&mut self) {
        let got = self.peek();
        let mut tokens = self
            .expected
            .iter()
            .map(|e| e.to_kind_string())
            .collect::<Vec<_>>();
        tokens.sort();
        let error = ParserError::new(
            format!(
                "Expected one of '{}', got '{}'",
                tokens.join(", "),
                got.kind,
            ),
            got.span,
        );
        self.errors.push(error);
    }

    /// Push an error, saying the `expected` token and the tokens in `self.expected` (if any), were
    /// expected next, but the current token was found.
    fn expected_one(&mut self, expected: &TokenKind) {
        if self.expected.is_empty() {
            let got = self.peek();
            let error = ParserError::new(
                format!(
                    "Expected '{}', got '{}'",
                    expected.to_kind_string(),
                    got.kind
                ),
                got.span,
            );
            self.errors.push(error);
        } else {
            // Cloning a TokenKind is O(1).
            self.expected.insert(expected.clone());
            self.expected();
            self.expected.clear();
        }
    }

    /// Push an error, saying one of the `expected` tokens was expected to be the next token, but
    /// the current token was found.
    fn expected_one_of(&mut self, expected: &[TokenKind]) {
        for e in expected {
            self.expected.insert(e.clone()); // TokenKind clone is O(1)
        }
        self.expected();
    }

    fn parse_ty_fields(&mut self) -> PResult<Vec<ast::TyField>> {
        let mut ty_fields = vec![];

        while let Some(name) = self.maybe_expect_ident() {
            self.expect(&T![:])?;
            let ty = self.expect_ident()?;
            ty_fields.push(ast::TyField { name, ty });

            if self.maybe_expect(&T![,]).is_none() {
                break;
            }
        }

        Ok(ty_fields)
    }

    fn parse_string(&mut self, s: SmolStr, span: Span) -> PResult<Vec<u8>> {
        let mut string: Vec<u8> = vec![];
        let mut chars = s.chars().skip(1);
        let mut offset = 1;

        loop {
            let current = span.lo + offset;
            match chars.next() {
                None | Some('"') => break,
                Some('\\') => {
                    let checkpoint = chars.clone();
                    match chars.next() {
                        None => {
                            // It is unterminated, and that is already handled.
                            break;
                        }
                        Some('a') => {
                            offset += 2;
                            string.push(b'\x07')
                        }
                        Some('b') => {
                            offset += 2;
                            string.push(b'\x08')
                        }
                        Some('f') => {
                            offset += 2;
                            string.push(b'\x0C')
                        }
                        Some('n') => {
                            offset += 2;
                            string.push(b'\n')
                        }
                        Some('r') => {
                            offset += 2;
                            string.push(b'\r')
                        }
                        Some('t') => {
                            offset += 2;
                            string.push(b'\t')
                        }
                        Some('v') => {
                            offset += 2;
                            string.push(b'\x0B')
                        }
                        Some('\\') => {
                            offset += 2;
                            string.push(b'\\')
                        }
                        Some('"') => {
                            offset += 2;
                            string.push(b'"')
                        }
                        Some('x') => {
                            chars.next();
                            chars.next();
                            let escape_sequence = checkpoint.skip(1).take(2).collect::<String>();
                            let n = match u8::from_str_radix(&escape_sequence, 16) {
                                Ok(n) => n as u8,
                                Err(e) => {
                                    self.errors.push(ParserError::new(
                                        format!(
                                            "Could not parse hex escape sequence '{}' - {}",
                                            escape_sequence, e,
                                        ),
                                        Span::new(current + 1, current + 4),
                                    ));
                                    0
                                }
                            };
                            string.push(n);
                        }
                        Some(c) if ('0'..='9').contains(&c) => {
                            chars.next();
                            chars.next();
                            let escape_sequence = checkpoint.take(3).collect::<String>();
                            let n = match u8::from_str_radix(&escape_sequence, 8) {
                                Ok(n) => n,
                                Err(e) => {
                                    self.errors.push(ParserError::new(
                                        format!(
                                            "Could not parse octal escape sequence '{}' - {}",
                                            escape_sequence, e,
                                        ),
                                        Span::new(current + 1, current + 4),
                                    ));
                                    0
                                }
                            };
                            string.push(n);
                        }
                        Some(c) => {
                            offset += 1 + c.len_utf8() as u32;
                            self.errors.push(ParserError::new(
                                format!("Unexpected escape character '{}'", c),
                                Span::new(current + 1, current + c.len_utf8() as u32),
                            ));
                        }
                    }
                }
                Some(c) => {
                    let c_len = c.len_utf8();
                    offset += c_len as u32;
                    let mut b = [0; 4];
                    c.encode_utf8(&mut b);
                    string.extend_from_slice(&b[..c_len]);
                }
            }
        }

        Ok(string)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct TokenStream {
    stack_tokens: Vec<Vec<Token>>,
    stack_offsets: Vec<usize>,
    current_tokens: Vec<Token>,
    current_offset: usize,
}

impl TokenStream {
    fn push_tokens(&mut self, tokens: impl Into<Vec<Token>>) {
        if !self.current_tokens.is_empty() {
            self.stack_tokens
                .push(std::mem::take(&mut self.current_tokens));
            self.stack_offsets.push(self.current_offset);
        }
        self.current_tokens = tokens.into();
        self.current_offset = 0;
    }

    fn next(&mut self) -> Token {
        let offset = std::cmp::min(self.current_offset, self.current_tokens.len() - 1);
        self.current_offset += 1;
        if offset >= self.current_tokens.len() - 1 && !self.stack_tokens.is_empty() {
            self.current_offset = self
                .stack_offsets
                .pop()
                .expect("ICE: Should have stacked offset");
            self.current_tokens = self
                .stack_tokens
                .pop()
                .expect("ICE: Should have stacked tokens");
            self.next()
        } else {
            std::mem::take(&mut self.current_tokens[offset])
        }
    }

    fn peek(&self) -> &Token {
        if self.current_offset < self.current_tokens.len() - 1 {
            &self.current_tokens[self.current_offset]
        } else {
            for (i, tokens) in self.stack_tokens.iter().rev().enumerate() {
                if let Some(tok) = tokens.get(self.stack_offsets[i]) {
                    return tok;
                }
            }
            &self.current_tokens[self.current_tokens.len() - 1]
        }
    }

    fn at_eof(&self) -> bool {
        // The last token should always be <eof>
        self.current_offset >= self.current_tokens.len() - 1 && self.stack_tokens.is_empty()
    }
}

/// Test whether the token can be at the beginning of a declaration.
fn can_start_dec(kind: &TokenKind) -> bool {
    use TokenKind::*;

    matches!(
        kind,
        Type
        // | Class
        | Var
        | Function
        | Primitive
        | Import,
    )
}

/// Test whether the token can be at the beginning of an expression.
fn can_start_expr(kind: &TokenKind) -> bool {
    use TokenKind::*;

    matches!(
        kind,
        Nil
        | Integer(_)
        | String{..}
        | Id(_)
        // | New
        | Minus
        | LParen
        | If
        | While
        | For
        | Break
        | Let,
    )
}
