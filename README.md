# Tiger compiler

Compiler for the tiger languaged, based on the book `Modern Compiler Implementation in ML`.

## Example

```tiger
```

### Quirks

* Records and arrays don't contain their original names, and since tiger uses nominal typing, comparing two identical, but not the same types, will output something like `Expected type '{a: int}', got '{a: int}'`.
* Error reporting is underdeveloped, it cannnot output erros spanning multiple lines.
* Types don't contain their original declaration spans, it might be possible that some errors are reported on lines where the don't belong (I haven't come accross this).
* The semantic analyzer has functions beginning with `translate`, but there is also a translate module, I decided to go with the naming in the book.

### Improvements

* The typechecker stores the types using reference counting, self referential types cause memory leaks.
* The unit type `()` is represented in the AST as an empty list of exprs `Exprs(Vec<Expr>)`. Could be its own node.
* A parenthesized expression is a list of exprs with one element. Could be its own node.
* When creating a Frame, a static link is passed to all of them, but not all of them need one.
* Support more formals than can be passed through registers (support formals that have to be passed in memory).
* Handling of assembly instructions is not performant at all.
