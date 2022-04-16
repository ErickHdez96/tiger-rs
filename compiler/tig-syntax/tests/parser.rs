use expect_test::expect;
use std::io::Write;
use tig_syntax::parser::parse_file;

#[test]
fn test_parser_import() {
    let mut imported_file = tempfile::NamedTempFile::new().expect("a temp file");
    let mut main_program_file = tempfile::NamedTempFile::new().expect("a temp file");

    let imported = r#"
        function factorial(x: int): int =
            if x = 0
            then 1
            else x * factorial(x - 1)
    "#;
    let main_program = format!(
        "
        let
            var a := 1
            import \"{}\"
            type b = int
        in
            factorial(a)
        end
    ",
        imported_file.path().to_string_lossy()
    );

    write!(imported_file, "{}", imported.trim()).expect("shuld write to imported file");
    write!(main_program_file, "{}", main_program.trim()).expect("shuld write to main program file");

    let (_, result) = parse_file(main_program_file.path()).expect("should parse the file");
    let expected = expect![[r#"
        0..136: Expr
          0..136: Let
            16..88: Decs
              16..26: VarDec - Escape(false)
                20..21: Variable(a)
                25..26: Value
                  25..26: Integer(1)
              136..247: Functions
                145..247: Function
                  145..154: Name(factorial)
                  155..161: Parameters
                    155..156: Name(x) - 158..161: Type(int) - Escape(false)
                  164..167: ReturnType(int)
                  182..247: Body
                    182..247: If
                      185..190: Condition
                        185..190: BinaryOp(=)
                          185..186: Left
                            185..186: LValue
                              185..186: Ident(x)
                          189..190: Right
                            189..190: Integer(0)
                      208..209: Then
                        208..209: Integer(1)
                      227..247: Else
                        227..247: BinaryOp(*)
                          227..228: Left
                            227..228: LValue
                              227..228: Ident(x)
                          231..247: Right
                            231..247: Call
                              231..240: Func(factorial)
                              241..246: Arguments
                                241..246: BinaryOp(-)
                                  241..242: Left
                                    241..242: LValue
                                      241..242: Ident(x)
                                  245..246: Right
                                    245..246: Integer(1)
              76..88: TypeDecs
                76..88: TypeDec
                  81..82: TypeName
                    81..82: Ident(b)
                  85..88: Type
                    85..88: TypeId(int)
            112..124: Expr
              112..124: Exprs
                112..124: Expr
                  112..124: Call
                    112..121: Func(factorial)
                    122..123: Arguments
                      122..123: LValue
                        122..123: Ident(a)
    "#]];
    expected.assert_debug_eq(&result.program.expect("should have compiled"));
}
