#![allow(clippy::vec_box)] // PERF: See performs better
use std::collections::{HashMap, HashSet, VecDeque};

use tig_common::{
    temp::{Label, Temp},
    Span,
};

use crate::{ir, IR};

pub type Block = Vec<Box<ir::Stmt>>;

/// Returnd a Block from an IR tree with the following properties:
///
/// * No `StmtKind::Seq` or `ExprKind::ESeq`.
/// * The parent of every `ExprKind::Call` is `StmtKind::Exp`, or
/// `StmtKind::Move`(`ExprKind::Temp` t, ..)
pub fn linearize(stmt: Box<ir::Stmt>) -> Block {
    let stmt = do_stmt(stmt);
    let mut block = Vec::new();

    fn linear(stmt: Box<ir::Stmt>, block: &mut Block) {
        match stmt.kind {
            ir::StmtKind::Seq(s1, s2) => {
                linear(s1, block);
                linear(s2, block);
            }
            _ => {
                block.push(stmt);
            }
        }
    }

    linear(stmt, &mut block);
    block
}

/// From a cleaned block, produce a list of basic blocks with the following properties:
///
/// * Every block begins with a Label.
/// * A Label appears only at the beginning of a block.
/// * Any Jump or CJump is the last statement in a block.
/// * Every block ends with a Jump or CJump.
pub fn basic_blocks(stmts: Block) -> (Vec<Block>, Label) {
    let done = Label::named("done");
    let mut blocks = vec![];
    let mut current_block = vec![];

    #[derive(PartialEq)]
    enum State {
        /// Expecting a label
        Label,
        /// Expecting a statement
        Stmt,
    }

    let mut state = State::Label;
    for stmt in stmts {
        if state == State::Label {
            state = State::Stmt;

            if !current_block.is_empty() {
                blocks.push(std::mem::take(&mut current_block));
            }
            match &stmt.kind {
                ir::StmtKind::Label(_) => {
                    current_block.push(stmt);
                    continue;
                }
                _ => current_block.push(IR![s label, stmt.span, Label::new()]),
            }
        }

        match &stmt.kind {
            ir::StmtKind::Label(l) => {
                current_block.push(IR![s jmpl, stmt.span, l.clone()]);
                blocks.push(std::mem::take(&mut current_block));
                current_block.push(stmt);
            }
            ir::StmtKind::Jump { .. } | ir::StmtKind::CJump { .. } => {
                current_block.push(stmt);
                state = State::Label;
            }
            _ => current_block.push(stmt),
        }
    }

    if state == State::Stmt {
        // It is a compile error without the clone.
        #[allow(clippy::redundant_clone)]
        current_block.push(IR![s jmpl, Span::new(0, 1), done.clone()]);
    }
    if !current_block.is_empty() {
        blocks.push(current_block);
    }

    (blocks, done)
}

/// Given a list of basic blocks, and an exit Label, produce a block with the
/// following properties:
///
/// * Every CJump(_, t, f) is immediately followed by Label f.
pub fn trace_schedule(mut basic_blocks: Vec<Block>, end_l: Label) -> Block {
    let mut label_mapping = HashMap::from([(&end_l, usize::MAX)]);
    let mut blocks = vec![];
    for (i, b) in basic_blocks.iter().enumerate() {
        blocks.push(i);
        match &b.get(0).expect("ICE: Blocks must have a label").kind {
            ir::StmtKind::Label(l) => {
                label_mapping.insert(l, i);
            }
            _ => panic!("ICE: Blocks must begin with a label"),
        }
    }

    // We build a trace of jumps through the different basic blocks. If a
    // CJump is found, we first choose the false branch.
    // E.g. If block 1 jumps to either 2 on true or 3 on false, and both join on 4
    // We would get the trace [[1, 3, 4], [2]].
    let mut marked = HashSet::from([usize::MAX]);
    let mut traces = vec![];
    let mut current_trace;
    for mut i in blocks {
        current_trace = vec![];

        while !marked.contains(&i) {
            marked.insert(i);
            current_trace.push(i);

            match &basic_blocks[i]
                .last()
                .expect("ICE: Block must have at least one stmt")
                .kind
            {
                ir::StmtKind::Jump { targets, .. } => {
                    for label in targets {
                        let next_index = label_mapping[label];
                        if !marked.contains(&next_index) {
                            i = next_index;
                            break;
                        }
                    }
                }
                ir::StmtKind::CJump {
                    true_label,
                    false_label,
                    ..
                } => {
                    let false_index = label_mapping[false_label];
                    if !marked.contains(&false_index) {
                        i = false_index;
                    } else {
                        let true_index = label_mapping[true_label];
                        if !marked.contains(&true_index) {
                            i = true_index;
                        }
                    }
                }
                k => panic!("ICE: Block must end with jump - {:?}", k),
            }
        }

        if !current_trace.is_empty() {
            traces.push(current_trace);
        }
    }

    let mut traced_stmts = VecDeque::new();
    for trace in traces {
        for index in trace {
            let stmts = std::mem::take(&mut basic_blocks[index]);
            for stmt in stmts {
                traced_stmts.push_back(stmt);
            }
        }
    }

    let mut end_block = vec![];

    let mut current = traced_stmts.pop_front();
    while let Some(s) = current {
        match s.kind {
            // Remove unconditional jumps
            ir::StmtKind::Jump { .. } => {
                match (s.is_simple_jmp(), traced_stmts.front().map(|s| &s.kind)) {
                    (Some(tl), Some(ir::StmtKind::Label(l))) if tl == l => {
                        // We still want to include the label, as it might be
                        // the target to other jumps.
                        current = traced_stmts.pop_front();
                        continue;
                    }
                    _ => end_block.push(s),
                }
            }
            ir::StmtKind::CJump {
                true_label,
                false_label,
                op,
                left,
                right,
            } => {
                let next = traced_stmts.pop_front().unwrap_or_default();

                match &next.kind {
                    ir::StmtKind::Label(l) if l == &true_label => {
                        // If a CJmp is followed by its true label, negate the
                        // condition, and switch labels. Now it is followed
                        // by its false label.
                        end_block.push(IR![s cjmp, s.span,
                            op.negate(),
                            left,
                            right,
                            false_label,
                            true_label,
                        ]);
                    }
                    ir::StmtKind::Label(l) if l == &false_label => {
                        // The CJmp was partially moved, just rebuild it
                        // without any modifications.
                        end_block.push(IR![s cjmp, s.span,
                            op,
                            left,
                            right,
                            true_label,
                            false_label,
                        ]);
                    }
                    _ => {
                        // If the condition is not followed by its label, create a new
                        // false label, and an unconditional jump to the previous false
                        // label.
                        let new_false = Label::named("new_false");
                        end_block.push(IR![s cjmp, s.span,
                            op,
                            left,
                            right,
                            true_label,
                            new_false.clone(),
                        ]);
                        end_block.push(IR![s label, s.span, new_false]);
                        end_block.push(IR![s jmpl, s.span, false_label]);
                    }
                };

                end_block.push(next);
            }
            _ => end_block.push(s),
        }

        current = traced_stmts.pop_front();
    }

    end_block.push(IR![s label, Span::new(0, 1), end_l]);
    end_block
}

/// Calculates whether a statement and an expression commute (whether they can be evaluated in any
/// order and without affecting the result).
fn commute(l: &ir::Stmt, r: &ir::Expr) -> bool {
    if let ir::StmtKind::Expr(e) = &l.kind {
        if let ir::ExprKind::Const(_) = &e.kind {
            return true;
        }
    }

    matches!(r.kind, ir::ExprKind::Const(_) | ir::ExprKind::Name(_))
}

/// Takes a list of expressions and returns a pair of (Statement, Vec<Expr>). The statement
/// contains all the things that must be executed before the expression-list. If the expression
/// list contains no statements, then the Statement returned is Exp(Const (0)).
fn reorder(mut exprs: Vec<Box<ir::Expr>>) -> (Box<ir::Stmt>, Vec<Box<ir::Expr>>) {
    if exprs.is_empty() {
        return (
            IR![s expr, Span::new(0, 1), IR![e const, Span::new(0, 1), 0]],
            vec![],
        );
    }

    let e1 = exprs.remove(0);

    if let ir::ExprKind::Call { .. } = e1.kind {
        let tmp = IR![e temp, e1.span, Temp::new()];
        exprs.insert(
            0,
            IR![e eseq, e1.span,
            IR![s move, e1.span, tmp.clone(), e1],
                tmp
            ],
        );
        return reorder(exprs);
    }

    let (s1, e1) = do_expr(e1);
    let (s2, mut e2) = reorder(exprs);

    // If s2 commutes with e1, we can just pull s2 and place it in front of e1.
    if commute(&s2, &e1) {
        e2.insert(0, e1);
        (append(s1, s2), e2)
    } else {
        // Otherwise create a new temp, move e1 to the temp,
        // Create a new seq s1 -> (mov tmp, e1) -> s2, and return
        // the new seq, tmp, e2
        let tmp = IR![e temp, e1.span, Temp::new()];
        e2.insert(0, tmp.clone());
        let mov = IR![s move, e1.span, tmp, e1];
        (append(s1, append(mov, s2)), e2)
    }
}

fn reorder1(e: Box<ir::Expr>) -> (Box<ir::Stmt>, Box<ir::Expr>) {
    if let ir::ExprKind::Call { .. } = e.kind {
        let tmp = IR![e temp, e.span, Temp::new()];
        return reorder1(IR![e eseq, e.span,
            IR![s move, e.span, tmp.clone(), e],
            tmp
        ]);
    }

    do_expr(e)
}

fn reorder2(e1: Box<ir::Expr>, e2: Box<ir::Expr>) -> (Box<ir::Stmt>, Box<ir::Expr>, Box<ir::Expr>) {
    if let ir::ExprKind::Call { .. } = e1.kind {
        let tmp = IR![e temp, e1.span, Temp::new()];
        return reorder2(
            IR![e eseq, e1.span,
                IR![s move, e1.span, tmp.clone(), e1],
                tmp
            ],
            e2,
        );
    }

    let (s1, e1) = do_expr(e1);
    let (s2, e2) = reorder1(e2);

    // If s2 commutes with e1, we can just pull s2 and place it in front of e1.
    if commute(&s2, &e1) {
        (IR![s seq, s1.span.extend(s2.span), s1, s2], e1, e2)
    } else {
        // Otherwise create a new temp, move e1 to the temp,
        // Create a new seq s1 -> (mov tmp, e1) -> s2, and return
        // the new seq, tmp, e2
        let tmp = IR![e temp, e1.span, Temp::new()];
        let mov = IR![s move, e1.span, tmp.clone(), e1];
        (
            IR![s seq, s1.span.extend(s2.span),
                s1,
                mov,
                s2,
            ],
            tmp,
            e2,
        )
    }
}

/// It takes a list _l_ of subexpressions, and a _build_ function.
/// It pulls all the ESeqs out of the _l_, yielding a statement _s1_ that contains all the
/// statements from the ESeqs and a list _l'_ of cleaned-up expressions. Then it makes
/// Seq(s1, build(l')).
fn reorder_stmt(
    e: Vec<Box<ir::Expr>>,
    builder: impl FnOnce(Vec<Box<ir::Expr>>) -> Box<ir::Stmt>,
) -> Box<ir::Stmt> {
    let (s, e) = reorder(e);
    IR![s seq, s.span.extend(e.last().map(|e| e.span).expect("ICE: Should have at least the function expr")), s, builder(e)]
}

fn reorder_stmt1(
    e: Box<ir::Expr>,
    builder: impl FnOnce(Box<ir::Expr>) -> Box<ir::Stmt>,
) -> Box<ir::Stmt> {
    let (s, e) = reorder1(e);
    IR![s seq, s.span.extend(e.span), s, builder(e)]
}

fn reorder_stmt2(
    e1: Box<ir::Expr>,
    e2: Box<ir::Expr>,
    builder: impl FnOnce(Box<ir::Expr>, Box<ir::Expr>) -> Box<ir::Stmt>,
) -> Box<ir::Stmt> {
    let (s, e1, e2) = reorder2(e1, e2);
    IR![s seq, s.span.extend(e2.span), s, builder(e1, e2)]
}

/// Similar to `reorder_stmt`, but it returns a pair (s, e) where _s_ is a statement containing all
/// the side effects pulled out of _l_ and _e_ is build(l').
fn reorder_expr(
    exprs: Vec<Box<ir::Expr>>,
    builder: impl FnOnce(Vec<Box<ir::Expr>>) -> Box<ir::Expr>,
) -> (Box<ir::Stmt>, Box<ir::Expr>) {
    let (s, e) = reorder(exprs);
    (s, builder(e))
}

fn reorder_expr1(
    expr: Box<ir::Expr>,
    builder: impl FnOnce(Box<ir::Expr>) -> Box<ir::Expr>,
) -> (Box<ir::Stmt>, Box<ir::Expr>) {
    let (s, lp) = reorder1(expr);
    (s, builder(lp))
}

fn reorder_expr2(
    e1: Box<ir::Expr>,
    e2: Box<ir::Expr>,
    builder: impl FnOnce(Box<ir::Expr>, Box<ir::Expr>) -> Box<ir::Expr>,
) -> (Box<ir::Stmt>, Box<ir::Expr>) {
    let (s, e1, e2) = reorder2(e1, e2);
    (s, builder(e1, e2))
}

fn do_stmt(stmt: Box<ir::Stmt>) -> Box<ir::Stmt> {
    use ir::StmtKind::*;

    let span = stmt.span;
    match stmt.kind {
        Label(_) => stmt,

        Move(e, b) => {
            let espan = e.span;
            match e.kind {
                ir::ExprKind::Temp(t) => {
                    let bspan = b.span;
                    match b.kind {
                        // These nodes are generated by reorder, if we reorder the call
                        // expression again, it will turn into infinite recursion.
                        ir::ExprKind::Call {
                            func,
                            mut arguments,
                        } => {
                            arguments.insert(0, func);
                            reorder_stmt(arguments, move |mut exprs| {
                                let func = exprs.remove(0);
                                IR![s move, span,
                                    IR![e temp, espan, t],
                                    IR![e call, bspan, func, exprs]
                                ]
                            })
                        }
                        _ => reorder_stmt1(b, |e| IR![s move, span, IR![e temp, span, t], e]),
                    }
                }
                ir::ExprKind::Mem(d) => {
                    reorder_stmt2(d, b, |d, b| IR![s move, span, IR![e mem, span, d], b])
                }
                e => panic!("ICE: Invalid move statement {:?}", e),
            }
        }
        Expr(e) => {
            let espan = e.span;
            match e.kind {
                // These nodes are generated by reorder, if we reorder the call
                // expression again, it will turn into infinite recursion.
                ir::ExprKind::Call {
                    func,
                    mut arguments,
                } => {
                    arguments.insert(0, func);
                    reorder_stmt(arguments, move |mut exprs| {
                        let func = exprs.remove(0);
                        IR![s expr, span,
                            IR![e call, espan, func, exprs]
                        ]
                    })
                }
                _ => reorder_stmt1(e, |e| IR![s expr, span, e]),
            }
        }
        Jump {
            destination,
            targets,
        } => reorder_stmt1(destination, |e| IR![s jmp, span, e, targets]),
        CJump {
            op,
            left,
            right,
            true_label,
            false_label,
        } => reorder_stmt2(
            left,
            right,
            move |a, b| IR![s cjmp, span, op, a, b, true_label, false_label],
        ),
        Seq(s1, s2) => {
            let s1 = do_stmt(s1);
            let s2 = do_stmt(s2);
            append(s1, s2)
        }
    }
}

fn do_expr(expr: Box<ir::Expr>) -> (Box<ir::Stmt>, Box<ir::Expr>) {
    use ir::ExprKind::*;

    let span = expr.span;
    match expr.kind {
        Const(_) => (IR![s expr, span, IR![e const, span, 0]], expr),
        Name(_) => (IR![s expr, span, IR![e const, span, 0]], expr),
        Temp(_) => (IR![s expr, span, IR![e const, span, 0]], expr),

        BinOp { op, left, right } => {
            reorder_expr2(left, right, |a, b| IR![e binop, span, op, a, b])
        }
        Mem(e) => reorder_expr1(e, |e| IR![e mem, span, e]),
        Call {
            func,
            mut arguments,
        } => {
            arguments.insert(0, func);
            reorder_expr(arguments, |mut e| {
                let func = e.remove(0);
                IR![e call, span, func, e]
            })
        }
        ESeq(s, e) => {
            let s1 = do_stmt(s);
            let (s2, e) = do_expr(e);
            (append(s1, s2), e)
        }
    }
}

fn append(s1: Box<ir::Stmt>, s2: Box<ir::Stmt>) -> Box<ir::Stmt> {
    //return IR![s seq, s1.span.extend(s2.span), s1, s2];
    match (&s1.kind, &s2.kind) {
        (ir::StmtKind::Expr(e), _) => {
            if let ir::ExprKind::Const(_) = e.kind {
                return s2;
            }
        }
        (_, ir::StmtKind::Expr(e)) => {
            if let ir::ExprKind::Const(_) = e.kind {
                return s1;
            }
        }
        (_, _) => {}
    }

    IR![s seq, s1.span.extend(s2.span), s1, s2]
}

#[cfg(test)]
mod tests {
    use crate::{
        frame::{amd64::Amd64Frame, Fragment},
        translate_program,
    };

    use super::*;
    use expect_test::{expect, Expect};
    use tig_syntax::parse_str;

    fn check_linearize(program: &str, blocks: Vec<Expect>) {
        let (_, p) = parse_str(program);
        assert_eq!(p.errors, vec![]);
        let result = translate_program::<Amd64Frame>(p.program.expect("Should have compiled"));
        assert_eq!(result.errors, vec![]);
        let rf_len = result.fragments.len();
        let ef_len = blocks.len();
        for (f, e) in result.fragments.into_iter().zip(blocks.into_iter()) {
            match f {
                Fragment::Proc { body, .. } => {
                    e.assert_debug_eq(&linearize(body));
                }
                _ => {}
            }
        }
        assert_eq!(rf_len, ef_len);
    }

    fn check_trace(program: &str, blocks: Vec<Expect>) {
        let (_, p) = parse_str(program);
        assert_eq!(p.errors, vec![]);
        let result = translate_program::<Amd64Frame>(p.program.expect("Should have compiled"));
        assert_eq!(result.errors, vec![]);
        let rf_len = result.fragments.len();
        let ef_len = blocks.len();
        for (f, e) in result.fragments.into_iter().zip(blocks.into_iter()) {
            match f {
                Fragment::Proc { body, .. } => {
                    let b = linearize(body);
                    let (bb, l) = basic_blocks(b);
                    e.assert_debug_eq(&trace_schedule(bb, l));
                }
                _ => {}
            }
        }
        assert_eq!(rf_len, ef_len);
    }

    #[test]
    fn test_linearize() {
        check_linearize(
            "if 2 > 3 then 1 else 2",
            vec![expect![[r#"
                    [
                        3..4: StmtExpr
                          3..4: Const(0),
                        7..8: StmtExpr
                          7..8: Const(0),
                        3..8: CJmp(>) -> true0 | false1
                          3..4: Left
                            3..4: Const(2)
                          7..8: Right
                            7..8: Const(3),
                        3..22: Label(true0),
                        14..15: StmtExpr
                          14..15: Const(0),
                        14..15: Move
                          14..15: Destination
                            14..15: Temp(0)
                          14..15: Source
                            14..15: Const(1),
                        14..15: StmtExpr
                          14..15: Const(0),
                        14..15: Jump([end2])
                          14..15: Target
                            14..15: Name(end2),
                        3..22: Label(false1),
                        21..22: StmtExpr
                          21..22: Const(0),
                        21..22: Move
                          21..22: Destination
                            21..22: Temp(0)
                          21..22: Source
                            21..22: Const(2),
                        21..22: StmtExpr
                          21..22: Const(0),
                        21..22: Jump([end2])
                          21..22: Target
                            21..22: Name(end2),
                        3..22: Label(end2),
                        3..22: Move
                          3..22: Destination
                            3..22: Temp(rv)
                          3..22: Source
                            3..22: Temp(0),
                    ]
                "#]]],
        );

        check_linearize(
            "
            let
                primitive rand(): int
            in
                rand() + rand()
            end
            ",
            vec![expect![[r#"
                    [
                        0..1: StmtExpr
                          0..1: Const(0),
                        86..92: Move
                          86..92: Destination
                            86..92: Temp(1)
                          86..92: Source
                            86..92: Call
                              86..92: Function
                                86..92: Name(rand),
                        86..92: Move
                          86..92: Destination
                            86..92: Temp(3)
                          86..92: Source
                            86..92: Temp(1),
                        0..1: StmtExpr
                          0..1: Const(0),
                        95..101: Move
                          95..101: Destination
                            95..101: Temp(2)
                          95..101: Source
                            95..101: Call
                              95..101: Function
                                95..101: Name(rand),
                        86..101: Move
                          86..101: Destination
                            86..101: Temp(rv)
                          86..101: Source
                            86..101: BinOp(+)
                              86..92: Left
                                86..92: Temp(3)
                              95..101: Right
                                95..101: Temp(2),
                    ]
                "#]]],
        );
    }

    #[test]
    fn test_trace_schedule() {
        check_trace(
            "
            while 1 > 2 do if 2 > 3 then break else break
            ",
            vec![expect![[r#"
                [
                    19..58: Label(test4),
                    19..20: StmtExpr
                      19..20: Const(0),
                    23..24: StmtExpr
                      23..24: Const(0),
                    19..24: CJmp(>) -> body5 | while_end0
                      19..20: Left
                        19..20: Const(1)
                      23..24: Right
                        23..24: Const(2),
                    19..58: Label(while_end0),
                    19..58: Move
                      19..58: Destination
                        19..58: Temp(rv)
                      19..58: Source
                        19..58: Const(0),
                    0..1: Jump([done6])
                      0..1: Target
                        0..1: Name(done6),
                    19..58: Label(body5),
                    31..32: StmtExpr
                      31..32: Const(0),
                    35..36: StmtExpr
                      35..36: Const(0),
                    31..36: CJmp(>) -> true1 | false2
                      31..32: Left
                        31..32: Const(2)
                      35..36: Right
                        35..36: Const(3),
                    31..58: Label(false2),
                    53..58: StmtExpr
                      53..58: Const(0),
                    53..58: Jump([while_end0])
                      53..58: Target
                        53..58: Name(while_end0),
                    31..58: Label(true1),
                    42..47: StmtExpr
                      42..47: Const(0),
                    42..47: Jump([while_end0])
                      42..47: Target
                        42..47: Name(while_end0),
                    42..47: Label(7),
                    42..47: StmtExpr
                      42..47: Const(0),
                    31..58: Label(end3),
                    31..58: StmtExpr
                      31..58: Const(0),
                    31..58: Jump([test4])
                      31..58: Target
                        31..58: Name(test4),
                    53..58: Label(8),
                    53..58: StmtExpr
                      53..58: Const(0),
                    53..58: Jump([end3])
                      53..58: Target
                        53..58: Name(end3),
                    0..1: Label(done6),
                ]
            "#]]],
        );

        check_trace(
            "
            let
                function max(a: int, b: int): int = if a >= b then a else b
            in
                max(2, 3)
            end
            ",
            vec![
                expect![[r#"
                    [
                        72..73: Label(14),
                        72..73: StmtExpr
                          72..73: Const(0),
                        77..78: StmtExpr
                          77..78: Const(0),
                        72..78: CJmp(>=) -> true10 | false11
                          72..73: Left
                            72..73: Temp(0)
                          77..78: Right
                            77..78: Temp(1),
                        72..92: Label(false11),
                        91..92: StmtExpr
                          91..92: Const(0),
                        91..92: Move
                          91..92: Destination
                            91..92: Temp(2)
                          91..92: Source
                            91..92: Temp(1),
                        91..92: StmtExpr
                          91..92: Const(0),
                        72..92: Label(end12),
                        33..92: Move
                          33..92: Destination
                            33..92: Temp(rv)
                          72..92: Source
                            72..92: Temp(2),
                        0..1: Jump([done13])
                          0..1: Target
                            0..1: Name(done13),
                        72..92: Label(true10),
                        84..85: StmtExpr
                          84..85: Const(0),
                        84..85: Move
                          84..85: Destination
                            84..85: Temp(2)
                          84..85: Source
                            84..85: Temp(0),
                        84..85: StmtExpr
                          84..85: Const(0),
                        84..85: Jump([end12])
                          84..85: Target
                            84..85: Name(end12),
                        0..1: Label(done13),
                    ]
                "#]],
                expect![[r#"
                    [
                        0..1: Label(16),
                        0..1: StmtExpr
                          0..1: Const(0),
                        124..133: Move
                          124..133: Destination
                            124..133: Temp(rv)
                          124..133: Source
                            124..133: Call
                              124..133: Function
                                124..133: Name(max9)
                              124..132: Arguments
                                124..133: Temp(fp)
                                128..129: Const(2)
                                131..132: Const(3),
                        0..1: Jump([done15])
                          0..1: Target
                            0..1: Name(done15),
                        0..1: Label(done15),
                    ]
                "#]],
            ],
        );

        check_trace(
            "
            let
                function factorial(n: int): int =
                    if n = 0
                    then 1
                    else n * factorial(n - 1)
            in
                factorial(2)
            end
            ",
            vec![
                expect![[r#"
                    [
                        90..91: Label(22),
                        90..91: StmtExpr
                          90..91: Const(0),
                        94..95: StmtExpr
                          94..95: Const(0),
                        90..95: CJmp(=) -> true18 | false19
                          90..91: Left
                            90..91: Temp(3)
                          94..95: Right
                            94..95: Const(0),
                        90..168: Label(false19),
                        148..149: StmtExpr
                          148..149: Const(0),
                        148..149: Move
                          148..149: Destination
                            148..149: Temp(7)
                          148..149: Source
                            148..149: Temp(3),
                        152..168: StmtExpr
                          152..168: Const(0),
                        152..168: StmtExpr
                          152..168: Const(0),
                        152..168: Move
                          152..168: Destination
                            152..168: Temp(6)
                          152..168: Source
                            152..168: Mem
                              152..168: Expr
                                152..168: BinOp(-)
                                  152..168: Left
                                    152..168: Temp(fp)
                                  152..168: Right
                                    152..168: Const(8),
                        162..163: StmtExpr
                          162..163: Const(0),
                        166..167: StmtExpr
                          166..167: Const(0),
                        152..168: Move
                          152..168: Destination
                            152..168: Temp(5)
                          152..168: Source
                            152..168: Call
                              152..168: Function
                                152..168: Name(factorial17)
                              152..167: Arguments
                                152..168: Temp(6)
                                162..167: BinOp(-)
                                  162..163: Left
                                    162..163: Temp(3)
                                  166..167: Right
                                    166..167: Const(1),
                        148..168: Move
                          148..168: Destination
                            148..168: Temp(4)
                          148..168: Source
                            148..168: BinOp(*)
                              148..149: Left
                                148..149: Temp(7)
                              152..168: Right
                                152..168: Temp(5),
                        148..168: StmtExpr
                          148..168: Const(0),
                        90..168: Label(end20),
                        33..168: Move
                          33..168: Destination
                            33..168: Temp(rv)
                          90..168: Source
                            90..168: Temp(4),
                        0..1: Jump([done21])
                          0..1: Target
                            0..1: Name(done21),
                        90..168: Label(true18),
                        121..122: StmtExpr
                          121..122: Const(0),
                        121..122: Move
                          121..122: Destination
                            121..122: Temp(4)
                          121..122: Source
                            121..122: Const(1),
                        121..122: StmtExpr
                          121..122: Const(0),
                        121..122: Jump([end20])
                          121..122: Target
                            121..122: Name(end20),
                        0..1: Label(done21),
                    ]
                "#]],
                expect![[r#"
                    [
                        0..1: Label(24),
                        0..1: StmtExpr
                          0..1: Const(0),
                        200..212: Move
                          200..212: Destination
                            200..212: Temp(rv)
                          200..212: Source
                            200..212: Call
                              200..212: Function
                                200..212: Name(factorial17)
                              200..211: Arguments
                                200..212: Temp(fp)
                                210..211: Const(2),
                        0..1: Jump([done23])
                          0..1: Target
                            0..1: Name(done23),
                        0..1: Label(done23),
                    ]
                "#]],
            ],
        );
    }
}
