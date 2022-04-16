# Tiger compiler architecture

The compiler follows a straightforward compiler architecture.

```
  ---------                   ----------                ---------------------
  |       |                   |        |                |                   |
  | Lexer | -- Vec<Token> --> | Parser | -- Program --> | Semantic Analyzer |
  |       |                   |        |                |                   |
  ---------                   ----------                ---------------------

Lexer - compiler/tig-syntax/src/lexer.rs - tokenize*

Token - compiler/tig-syntax/src/lexer.rs

Parser - compiler/tig-syntax/src/parser.rs - parse*

Program - compiler/tig-syntax/src/ast.rs

Semantic Analyzer - compiler/tig-semant/src/semant.rs - translate_program
```

There is another important module, `compiler/tig-compiler/src/lib.rs`, which contains an orchestrator for calling the entire pipeline. And the main binary is in `compiler/tig-driver/src/main.rs`.

The compiler loads each file used into a `SourceFile`, which are compiled in `SourceCode`, both in `compiler/tig-common/src/lib.rs`. Every file is loaded into memory and stored in a `SourceFile`. All the loaded source files are compiled in a root `SourceCode`. This also means that when compiling from stdin, it will wait for an EOF before it starts to compile.

## Pipeline

1. The compiler loads the main program into its own source code.
2. The compiler parses the program through the `parse_source_code` function.
  2.1. The parser first tokenizes the whole file and stores the tokens into memory.
    2.1.1. The lexer goes through every character, generating a new token.
  2.2. The parser then transforms the token stream into a `Program`, which is the root node of the `AST`.
  2.3. In case an import is found.
    2.3.1. The parser loads the file as another `SourceFile`.
    2.3.2. The file is tokenized.
    2.3.3. The new file's tokens are pushed into the token stream (the token stream has a stack of tokens, and current offsets to allow getting back to the previous file).
    2.3.4. The parser continues parsing as if nothing happened, the stack of tokens is handled transparently by `TokenStream`.
    2.3.5. Once the parser reaches the end of the imported file, the tokens are discarded, and it returns to the previous file.
  2.4. In case an error is found.
    2.4.1. If the error occurred while parsing declarations, it logs the error, then it ignores tokens until it finds one that can start another declaration.
    2.4.2. If the error happens in an expr, it logs the error and returns.
3. The compiled `Program` is sent to `translate_program` for typechecking.
  3.1. The semantic analyzer recursively translates every expr, declaration and type.
  3.2. In case of an error.
    3.2.1. It logs an error
    3.2.2. It either returns the expected type (e.g. int for +, -, etc.), or it returns a special type `hole`, which indicates an error, but typecheks with every other type to prevent cascading more errors.
