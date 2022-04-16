use std::collections::HashMap;

//#![allow(dead_code)]
//#![allow(unused_variables)]
use tig_common::SmolStr;
use tig_syntax::ast;

pub fn find_escapes(program: &mut ast::Program) {
    EscapeAnalyzer::find_escapes(program)
}

struct EscapeAnalyzer<'a> {
    stack: Vec<HashMap<SmolStr, DepthEscape<'a>>>,
    env: HashMap<SmolStr, DepthEscape<'a>>,
}

type DepthEscape<'escape> = (usize, &'escape mut bool);

impl<'a> EscapeAnalyzer<'a> {
    fn find_escapes(program: &mut ast::Program) {
        let mut s = EscapeAnalyzer {
            stack: vec![],
            env: HashMap::new(),
        };

        match program {
            ast::Program::Expr(e) => s.traverse_expr(e, 0),
            ast::Program::Decs(decs) => {
                s.traverse_decs(decs, 0);
            }
        }
    }

    fn enter_scope(&mut self) {
        self.stack.push(std::mem::take(&mut self.env));
    }

    fn exit_scope(&mut self) {
        self.env = self.stack.pop().expect("No scope present");
    }

    fn escapes(&mut self, key: &SmolStr, depth: usize) {
        if let Some((d, escape)) = self.env.get_mut(key) {
            if depth > *d {
                **escape = true;
            }
        } else {
            for env in self.stack.iter_mut().rev() {
                if let Some((d, escape)) = env.get_mut(key) {
                    if depth > *d {
                        **escape = true;
                    }
                    return;
                }
            }
        }
    }

    fn traverse_var(&mut self, var: &'a mut ast::LValue, depth: usize) {
        match var {
            ast::LValue::Ident(id) => {
                self.escapes(&id.value, depth);
            }
            ast::LValue::FieldAccess(object, _) => {
                self.traverse_var(object, depth);
            }
            ast::LValue::ArrayAccess(array, _) => {
                self.traverse_var(array, depth);
            }
        }
    }

    fn traverse_expr(&mut self, expr: &'a mut ast::Expr, depth: usize) {
        match &mut expr.kind {
            ast::ExprKind::Nil => {}
            ast::ExprKind::Integer(_) => {}
            ast::ExprKind::String(_) => {}
            ast::ExprKind::Array {
                size,
                initial_value,
                ..
            } => {
                self.traverse_expr(size, depth);
                self.traverse_expr(initial_value, depth);
            }
            ast::ExprKind::Record { fields, .. } => {
                for f in fields {
                    self.traverse_expr(&mut f.value, depth);
                }
            }
            ast::ExprKind::LValue(lvalue) => self.traverse_var(lvalue, depth),
            ast::ExprKind::Call { arguments, .. } => {
                for a in arguments {
                    self.traverse_expr(a, depth);
                }
            }
            ast::ExprKind::Negate(e) => self.traverse_expr(e, depth),
            ast::ExprKind::BinOp { left, right, .. } => {
                self.traverse_expr(left, depth);
                self.traverse_expr(right, depth);
            }
            ast::ExprKind::Exprs(ref mut exprs) => {
                for e in exprs {
                    self.traverse_expr(e, depth);
                }
            }
            ast::ExprKind::Assign {
                destination,
                source,
            } => {
                self.traverse_var(destination, depth);
                self.traverse_expr(source, depth);
            }
            ast::ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.traverse_expr(cond, depth);
                self.traverse_expr(then_branch, depth);
                if let Some(else_branch) = else_branch {
                    self.traverse_expr(else_branch, depth);
                }
            }
            ast::ExprKind::While { cond, body } => {
                self.traverse_expr(cond, depth);
                self.traverse_expr(body, depth);
            }
            ast::ExprKind::For {
                iterator,
                escape,
                start,
                end,
                body,
            } => {
                self.enter_scope();
                self.env.insert(iterator.value.clone(), (depth, escape));
                self.traverse_expr(start, depth);
                self.traverse_expr(end, depth);
                self.traverse_expr(body, depth);
                self.exit_scope();
            }
            ast::ExprKind::Break => {}
            ast::ExprKind::Let { decs, expr } => {
                self.enter_scope();
                self.traverse_decs(decs, depth);
                self.traverse_expr(expr, depth);
                self.exit_scope();
            }
        }
    }

    fn traverse_decs(&mut self, decs: &'a mut Vec<ast::Dec>, depth: usize) {
        for d in decs {
            match &mut d.kind {
                ast::DecKind::Type(_) => {}
                ast::DecKind::Variable {
                    name,
                    escape,
                    value,
                    ..
                } => {
                    // The variable cannot be referenced in the initial value.
                    // So we first traverse the initial value, and then add the
                    // variable to the environment (see test_variable_invalid_reference).
                    self.traverse_expr(value, depth);
                    self.env.insert(name.value.clone(), (depth, escape));
                }
                ast::DecKind::Function(functions) => {
                    let depth = depth + 1;
                    for f in functions {
                        self.enter_scope();
                        for p in &mut f.parameters {
                            self.env
                                .insert(p.name.value.clone(), (depth, &mut p.escape));
                        }
                        self.traverse_expr(&mut f.body, depth);
                        self.exit_scope();
                    }
                }
                ast::DecKind::Primitive { .. } => {}
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use expect_test::{expect, Expect};

    use super::*;
    use tig_syntax::{parse_str, ParseResult};

    fn check(program: &str, expected: Expect) {
        let (_, p) = parse_str(program);
        assert_eq!(p.errors, vec![]);
        let ParseResult { program, errors } = p;
        assert_eq!(errors, vec![]);
        let mut program = program.expect("Should have compiled");
        find_escapes(&mut program);
        expected.assert_debug_eq(&program);
    }

    #[test]
    fn test_simple_escape() {
        check(
            r#"
            let
                function double(x: int) =
                    let
                        function add(y: int) =
                            x + y
                    in
                        add(x)
                    end
            in
                double(2)
            end
            "#,
            expect![[r#"
                13..298: Expr
                  13..298: Let
                    33..241: Decs
                      33..241: Functions
                        42..241: Function
                          42..48: Name(double)
                          49..55: Parameters
                            49..50: Name(x) - 52..55: Type(int) - Escape(true)
                          79..241: Body
                            79..241: Let
                              107..163: Decs
                                107..163: Functions
                                  116..163: Function
                                    116..119: Name(add)
                                    120..126: Parameters
                                      120..121: Name(y) - 123..126: Type(int) - Escape(false)
                                    158..163: Body
                                      158..163: BinaryOp(+)
                                        158..159: Left
                                          158..159: LValue
                                            158..159: Ident(x)
                                        162..163: Right
                                          162..163: LValue
                                            162..163: Ident(y)
                              211..217: Expr
                                211..217: Exprs
                                  211..217: Expr
                                    211..217: Call
                                      211..214: Func(add)
                                      215..216: Arguments
                                        215..216: LValue
                                          215..216: Ident(x)
                    273..282: Expr
                      273..282: Exprs
                        273..282: Expr
                          273..282: Call
                            273..279: Func(double)
                            280..281: Arguments
                              280..281: Integer(2)
            "#]],
        );
    }

    #[test]
    fn test_for_escape() {
        check(
            r#"
            for i := 0 to 10 do
                let
                    function p() = print(i)
                in
                    p()
                end
            "#,
            expect![[r#"
                13..159: Expr
                  13..159: For - Escape(true)
                    17..18: Ident
                      17..18: Ident(i)
                    22..23: Start
                      22..23: Integer(0)
                    27..29: End
                      27..29: Integer(10)
                    49..159: Body
                      49..159: Let
                        73..96: Decs
                          73..96: Functions
                            82..96: Function
                              82..83: Name(p)
                              88..96: Body
                                88..96: Call
                                  88..93: Func(print)
                                  94..95: Arguments
                                    94..95: LValue
                                      94..95: Ident(i)
                        136..139: Expr
                          136..139: Exprs
                            136..139: Expr
                              136..139: Call
                                136..137: Func(p)
            "#]],
        );
    }

    #[test]
    fn test_nested_let() {
        check(
            r#"
            let
                var i := 3
                var j := 3
            in
                let
                    function p() = print(i)
                in
                    p()
                end
            end
            "#,
            expect![[r#"
                13..228: Expr
                  13..228: Let
                    33..70: Decs
                      33..43: VarDec - Escape(true)
                        37..38: Variable(i)
                        42..43: Value
                          42..43: Integer(3)
                      60..70: VarDec - Escape(false)
                        64..65: Variable(j)
                        69..70: Value
                          69..70: Integer(3)
                    102..212: Expr
                      102..212: Exprs
                        102..212: Expr
                          102..212: Let
                            126..149: Decs
                              126..149: Functions
                                135..149: Function
                                  135..136: Name(p)
                                  141..149: Body
                                    141..149: Call
                                      141..146: Func(print)
                                      147..148: Arguments
                                        147..148: LValue
                                          147..148: Ident(i)
                            189..192: Expr
                              189..192: Exprs
                                189..192: Expr
                                  189..192: Call
                                    189..190: Func(p)
            "#]],
        );
    }

    #[test]
    fn test_variable_invalid_reference() {
        check(
            r#"
            let
                var i :=
                    let
                        function p() = p(i)
                    in
                        p()
                    end
            in
                i
            end
            "#,
            expect![[r#"
                13..233: Expr
                  13..233: Let
                    33..184: Decs
                      33..184: VarDec - Escape(false)
                        37..38: Variable(i)
                        62..184: Value
                          62..184: Let
                            90..109: Decs
                              90..109: Functions
                                99..109: Function
                                  99..100: Name(p)
                                  105..109: Body
                                    105..109: Call
                                      105..106: Func(p)
                                      107..108: Arguments
                                        107..108: LValue
                                          107..108: Ident(i)
                            157..160: Expr
                              157..160: Exprs
                                157..160: Expr
                                  157..160: Call
                                    157..158: Func(p)
                    216..217: Expr
                      216..217: Exprs
                        216..217: Expr
                          216..217: LValue
                            216..217: Ident(i)
            "#]],
        );
    }

    #[test]
    fn test_nested_functions() {
        check(
            r#"
            type tree = {key: string, left: tree, right: tree }

            function prettyprint(tree: tree): string =
                let
                    var output := ""
                    function write(s: string) =
                        output := concat(output, s)
                    function show(n: int, t: tree) =
                        let
                            function indent(s: string) =
                                (
                                    for i := i to 5 do write(" ");
                                    output := concat(output, s);
                                    write("\n")
                                )
                        in
                            if t = nil
                            then indent(".")
                            else (indent(t, key);
                                  show(n + 1, t.left);
                                  show(n + 1, t.right))
                        end
                in
                    show(0, tree);
                    output
                end
            "#,
            expect![[r#"
                13..1064: Decs
                  13..64: TypeDecs
                    13..64: TypeDec
                      18..22: TypeName
                        18..22: Ident(tree)
                      25..64: Type
                        25..64: Record
                          26..29: Name(key) - 31..37: Type(string)
                          39..43: Name(left) - 45..49: Type(tree)
                          51..56: Name(right) - 58..62: Type(tree)
                  78..1064: Functions
                    87..1064: Function
                      87..98: Name(prettyprint)
                      99..109: Parameters
                        99..103: Name(tree) - 105..109: Type(tree) - Escape(false)
                      112..118: ReturnType(string)
                      137..1064: Body
                        137..1064: Let
                          161..963: Decs
                            161..177: VarDec - Escape(true)
                              165..171: Variable(output)
                              175..177: Value
                                175..177: String()
                            198..963: Functions
                              207..277: Function
                                207..212: Name(write)
                                213..222: Parameters
                                  213..214: Name(s) - 216..222: Type(string) - Escape(false)
                                250..277: Body
                                  250..277: Assign
                                    250..256: LValue
                                      250..256: Ident(output)
                                    260..277: Expr
                                      260..277: Call
                                        260..266: Func(concat)
                                        267..276: Arguments
                                          267..273: LValue
                                            267..273: Ident(output)
                                          275..276: LValue
                                            275..276: Ident(s)
                              307..963: Function
                                307..311: Name(show)
                                312..318: Parameters
                                  312..313: Name(n) - 315..318: Type(int) - Escape(false)
                                  320..321: Name(t) - 323..327: Type(tree) - Escape(false)
                                355..963: Body
                                  355..963: Let
                                    387..663: Decs
                                      387..663: Functions
                                        396..663: Function
                                          396..402: Name(indent)
                                          403..412: Parameters
                                            403..404: Name(s) - 406..412: Type(string) - Escape(false)
                                          448..663: Body
                                            448..663: Exprs
                                              486..515: Expr
                                                486..515: For - Escape(false)
                                                  490..491: Ident
                                                    490..491: Ident(i)
                                                  495..496: Start
                                                    495..496: LValue
                                                      495..496: Ident(i)
                                                  500..501: End
                                                    500..501: Integer(5)
                                                  505..515: Body
                                                    505..515: Call
                                                      505..510: Func(write)
                                                      511..514: Arguments
                                                        511..514: String( )
                                              553..580: Expr
                                                553..580: Assign
                                                  553..559: LValue
                                                    553..559: Ident(output)
                                                  563..580: Expr
                                                    563..580: Call
                                                      563..569: Func(concat)
                                                      570..579: Arguments
                                                        570..576: LValue
                                                          570..576: Ident(output)
                                                        578..579: LValue
                                                          578..579: Ident(s)
                                              618..629: Expr
                                                618..629: Call
                                                  618..623: Func(write)
                                                  624..628: Arguments
                                                    624..628: String(
                )
                                    719..935: Expr
                                      719..935: Exprs
                                        719..935: Expr
                                          719..935: If
                                            722..729: Condition
                                              722..729: BinaryOp(=)
                                                722..723: Left
                                                  722..723: LValue
                                                    722..723: Ident(t)
                                                726..729: Right
                                                  726..729: Nil
                                            763..774: Then
                                              763..774: Call
                                                763..769: Func(indent)
                                                770..773: Arguments
                                                  770..773: String(.)
                                            808..935: Else
                                              808..935: Exprs
                                                809..823: Expr
                                                  809..823: Call
                                                    809..815: Func(indent)
                                                    816..822: Arguments
                                                      816..817: LValue
                                                        816..817: Ident(t)
                                                      819..822: LValue
                                                        819..822: Ident(key)
                                                859..878: Expr
                                                  859..878: Call
                                                    859..863: Func(show)
                                                    864..877: Arguments
                                                      864..869: BinaryOp(+)
                                                        864..865: Left
                                                          864..865: LValue
                                                            864..865: Ident(n)
                                                        868..869: Right
                                                          868..869: Integer(1)
                                                      871..877: LValue
                                                        871..877: FieldAccess
                                                          871..872: Object
                                                            871..872: Ident(t)
                                                          873..877: Field
                                                            873..877: Ident(left)
                                                914..934: Expr
                                                  914..934: Call
                                                    914..918: Func(show)
                                                    919..933: Arguments
                                                      919..924: BinaryOp(+)
                                                        919..920: Left
                                                          919..920: LValue
                                                            919..920: Ident(n)
                                                        923..924: Right
                                                          923..924: Integer(1)
                                                      926..933: LValue
                                                        926..933: FieldAccess
                                                          926..927: Object
                                                            926..927: Ident(t)
                                                          928..933: Field
                                                            928..933: Ident(right)
                          1003..1044: Expr
                            1003..1044: Exprs
                              1003..1016: Expr
                                1003..1016: Call
                                  1003..1007: Func(show)
                                  1008..1015: Arguments
                                    1008..1009: Integer(0)
                                    1011..1015: LValue
                                      1011..1015: Ident(tree)
                              1038..1044: Expr
                                1038..1044: LValue
                                  1038..1044: Ident(output)
            "#]],
        );
    }
}
