use tig_common::{SmolStr, Span};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Program {
    Expr(Expr),
    Decs(Vec<Dec>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LValue {
    pub span: Span,
    pub kind: LValueKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LValueKind {
    Simple(SmolStr),
    Field(Box<LValue>, Ident),
    Subscript(Box<LValue>, Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    Nil,
    LValue(LValue),
    Int(u64),
    String(SmolStr),
    Paren(Box<Expr>),
    Call {
        func: Ident,
        args: Vec<Expr>,
    },
    BinOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Record {
        fields: Vec<FieldExpr>,
        ty: Ident,
    },
    Seq(Vec<Expr>),
    Assign {
        var: LValue,
        expr: Box<Expr>,
    },
    If {
        test: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },
    While {
        test: Box<Expr>,
        body: Box<Expr>,
    },
    For {
        var: Ident,
        escape: bool,
        lo: Box<Expr>,
        hi: Box<Expr>,
        body: Box<Expr>,
    },
    Break,
    Let {
        decs: Vec<Dec>,
        body: Box<Expr>,
    },
    Array {
        ty: Ident,
        size: Box<Expr>,
        init: Box<Expr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dec {
    pub span: Span,
    pub kind: DecKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecKind {
    Function(Vec<Fundec>),
    Var(Vardec),
    Type(Vec<Typedec>),
    Primitive(Primitivedec),
    Import(SmolStr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fundec {
    pub name: Ident,
    pub params: Vec<Field>,
    pub result: Option<Ident>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Primitivedec {
    pub name: Ident,
    pub params: Vec<Field>,
    pub result: Option<Ident>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Vardec {
    pub name: Ident,
    pub escape: bool,
    pub ty: Option<Ident>,
    pub init: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Typedec {
    pub name: Ident,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
    pub span: Span,
    pub kind: TypeKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    Name(Ident),
    Record(Vec<Field>),
    Array(Ident),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
    pub span: Span,
    pub value: SmolStr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    pub field: Ident,
    pub escape: bool,
    pub ty: Ident,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldExpr {
    pub field: Ident,
    pub expr: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
}

#[macro_export]
macro_rules! ast {
    (lvalue, simple, $span:expr, $lvalue:expr $(,)?) => {
        tig_ast::LValue {
            span: $span,
            kind: tig_ast::LValueKind::Simple($lvalue.into()),
        }
    };

    (lvalue, field, $span:expr, $lvalue:expr, $field:expr $(,)?) => {
        tig_ast::LValue {
            span: $span,
            kind: tig_ast::LValueKind::Field(Box::new($lvalue), $field),
        }
    };

    (lvalue, subscript, $span:expr, $lvalue:expr, $index:expr $(,)?) => {
        tig_ast::LValue {
            span: $span,
            kind: tig_ast::LValueKind::Subscript(Box::new($lvalue), Box::new($index)),
        }
    };

    (lvalue, subscript, $span:expr, $lvalue:expr, $index:expr $(,)?) => {
        tig_ast::LValue {
            span: $span,
            kind: tig_ast::LValueKind::Subscript(Box::new($lvalue), Box::new($index)),
        }
    };

    (expr, nil, $span:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::Nil,
        }
    };

    (expr, lvalue, $span:expr, $lvalue:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::LValue($lvalue),
        }
    };

    (expr, int, $span:expr, $int:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::Int($int as u64),
        }
    };

    (expr, str, $span:expr, $str:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::String($str.into()),
        }
    };

    (expr, paren, $span:expr, $expr:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::Paren(Box::new($expr)),
        }
    };

    (expr, seq, $span:expr, $exprs:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::Seq($exprs),
        }
    };

    (expr, array, $span:expr, $ty:expr, $size:expr, $init:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::Array {
                ty: $ty,
                size: Box::new($size),
                init: Box::new($init),
            },
        }
    };

    (expr, record, $span:expr, $ty:expr, { $($field:expr => $expr:expr),* $(,)? } $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::Record {
                ty: $ty,
                fields: vec![
                    $(ast::FieldExpr {
                        field: $field,
                        expr: $expr,
                    }),*
                ],
            },
        }
    };

    (expr, fn, $span:expr, $fn:expr, $args:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::Call {
                func: $fn,
                args: $args,
            },
        }
    };

    (expr, if, $span:expr, $test:expr, $then_branch:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::If {
                test: Box::new($test),
                then_branch: Box::new($then_branch),
                else_branch: None,
            },
        }
    };

    (expr, ife, $span:expr, $test:expr, $then_branch:expr, $else_branch:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::If {
                test: Box::new($test),
                then_branch: Box::new($then_branch),
                else_branch: Some(Box::new($else_branch)),
            },
        }
    };

    (expr, while, $span:expr, $test:expr, $body:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::While {
                test: Box::new($test),
                body: Box::new($body),
            },
        }
    };

    (expr, for, $span:expr, $id:expr, $lo:expr, $hi:expr, $body:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::For {
                var: $id,
                escape: false,
                lo: Box::new($lo),
                hi: Box::new($hi),
                body: Box::new($body),
            },
        }
    };

    (expr, break, $span:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::Break,
        }
    };

    (expr, array, $span:expr, $ty:expr, $size:expr, $init:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::Array {
                ty: $ty,
                size: Box::new($size),
                init: Box::new($init),
            },
        }
    };

    (expr, binop, $span:expr, $binop:expr, $left:expr, $right:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::BinOp {
                op: $binop,
                left: Box::new($left),
                right: Box::new($right),
            },
        }
    };

    (expr, assign, $span:expr, $lvalue:expr, $expr:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::Assign {
                var: $lvalue,
                expr: Box::new($expr),
            },
        }
    };

    (expr, let, $span:expr, $decs:expr, $expr:expr $(,)?) => {
        tig_ast::Expr {
            span: $span,
            kind: tig_ast::ExprKind::Let {
                decs: $decs,
                body: Box::new($expr),
            },
        }
    };

    (dec, fn, $span:expr, $fundecs:expr $(,)?) => {
        tig_ast::Dec {
            span: $span,
            kind: tig_ast::DecKind::Function($fundecs),
        }
    };

    (dec, ty, $span:expr, $typedecs:expr $(,)?) => {
        tig_ast::Dec {
            span: $span,
            kind: tig_ast::DecKind::Type($typedecs),
        }
    };

    (dec, var, $span:expr, $vardec:expr $(,)?) => {
        tig_ast::Dec {
            span: $span,
            kind: tig_ast::DecKind::Var($vardec),
        }
    };

    (dec, primitive, $span:expr, $primitivedec:expr $(,)?) => {
        tig_ast::Dec {
            span: $span,
            kind: tig_ast::DecKind::Primitive($primitivedec),
        }
    };

    (dec, import, $span:expr, $import:expr $(,)?) => {
        tig_ast::Dec {
            span: $span,
            kind: tig_ast::DecKind::Import($import.into()),
        }
    };

    (type, name, $span:expr, $id:expr $(,)?) => {
        tig_ast::Type {
            span: $span,
            kind: tig_ast::TypeKind::Name($id),
        }
    };

    (type, record, $span:expr, { $($field:expr => $ty:expr),* $(,)? } $(,)?) => {
        tig_ast::Type {
            span: $span,
            kind: tig_ast::TypeKind::Record(vec![
                $(ast::Field {
                    field: $field,
                    escape: false,
                    ty: $ty
                }),*
            ]),
        }
    };

    (type, array, $span:expr, $ty:expr $(,)?) => {
        tig_ast::Type {
            span: $span,
            kind: tig_ast::TypeKind::Array($ty),
        }
    };

    (ident, $span:expr, $name:expr $(,)?) => {
        tig_ast::Ident {
            span: $span,
            value: $name.into(),
        }
    };

    (fundec, $name:expr, $params:expr, $result:expr, $body:expr $(,)?) => {
        tig_ast::Fundec {
            name: $name,
            params: $params,
            result: $result,
            body: $body,
        }
    };

    (primitivedec, $name:expr, $params:expr, $result:expr $(,)?) => {
        tig_ast::Primitivedec {
            name: $name,
            params: $params,
            result: $result,
        }
    };

    (param, $name:expr, $ty:expr $(,)?) => {
        tig_ast::Field {
            field: $name,
            escape: false,
            ty: $ty,
        }
    };

    (vardec, $name:expr, $escape:expr, $ty:expr, $init:expr $(,)?) => {
        tig_ast::Vardec {
            name: $name,
            escape: $escape,
            ty: $ty,
            init: $init,
        }
    };

    (tydec, $name:expr, $ty:expr $(,)?) => {
        tig_ast::Typedec {
            name: $name,
            ty: $ty,
        }
    };
}

#[macro_export]
macro_rules! binop {
    (+) => {
        tig_ast::BinOp::Add
    };
    (-) => {
        tig_ast::BinOp::Sub
    };
    (*) => {
        tig_ast::BinOp::Mul
    };
    (/) => {
        tig_ast::BinOp::Div
    };
    (=) => {
        tig_ast::BinOp::Eq
    };
    (<>) => {
        tig_ast::BinOp::Neq
    };
    (<) => {
        tig_ast::BinOp::Lt
    };
    (<=) => {
        tig_ast::BinOp::Lte
    };
    (>) => {
        tig_ast::BinOp::Gt
    };
    (>=) => {
        tig_ast::BinOp::Gte
    };
    (&) => {
        tig_ast::BinOp::And
    };
    (|) => {
        tig_ast::BinOp::Or
    };
}
