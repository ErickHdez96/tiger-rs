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

    write!(imported_file, "{}", imported).expect("shuld write to imported file");
    write!(main_program_file, "{}", main_program).expect("shuld write to main program file");

    let result = parse_file(main_program_file.path()).expect("should parse the file");
    let expected = expect![[r#"
        9..189: Expr
          9..189: Let
            25..141: Decs
              25..35: VarDec
                29..30: Variable(a)
                34..35: Value
                  34..35: Integer(1)
              203..314: Function
                212..221: Name(factorial)
                222..228: Parameters
                  222..223: Name(x) - 225..228: Type(int)
                231..234: ReturnType(int)
                249..314: Body
                  249..314: If
                    252..257: Condition
                      252..257: BinaryOp(=)
                        252..253: Left
                          252..253: LValue
                            252..253: Ident(x)
                        256..257: Right
                          256..257: Integer(0)
                    275..276: Then
                      275..276: Integer(1)
                    294..314: Else
                      294..314: BinaryOp(*)
                        294..295: Left
                          294..295: LValue
                            294..295: Ident(x)
                        298..314: Right
                          298..314: Call
                            298..307: Func(factorial)
                            308..313: Arguments
                              308..313: BinaryOp(-)
                                308..309: Left
                                  308..309: LValue
                                    308..309: Ident(x)
                                312..313: Right
                                  312..313: Integer(1)
              129..141: TypeDec
                134..135: TypeName
                  134..135: Ident(b)
                138..141: Type
                  138..141: TypeId(int)
            165..177: Exprs
              165..177: Call
                165..174: Func(factorial)
                175..176: Arguments
                  175..176: LValue
                    175..176: Ident(a)
    "#]];
    dbg!(result.errors);
    expected.assert_debug_eq(&result.program.expect("should have compiled"));
}
