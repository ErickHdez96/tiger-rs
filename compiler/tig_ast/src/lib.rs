use tig_common::{SmolStr, Span, Spanned};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Program {
    Expr(Expr),
    Decs(Vec<Dec>),
}

pub type Var = Spanned<VarKind>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VarKind {
    Simple(Ident),
    Field(Box<Var>, Ident),
    Subscript(Box<Var>, Box<Expr>),
}

pub type Expr = Spanned<ExprKind>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    Nil,
    Var(Var),
    Int(u64),
    String(SmolStr),
    //Call {
    //    func: Ident,
    //    args: Vec<Expr>,
    //},
    BinOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Record {
        fields: Vec<FieldExpr>,
        ty: Ident,
    },
    //Seq(Vec<Expr>),
    //Assign {
    //    var: Var,
    //    expr: Box<Expr>,
    //},
    If {
        test: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },
    //While {
    //    test: Box<Expr>,
    //    body: Box<Expr>,
    //},
    //For {
    //    var: Ident,
    //    escape: bool,
    //    lo: Box<Expr>,
    //    hi: Box<Expr>,
    //    body: Box<Expr>,
    //},
    //Break,
    //Let {
    //    decs: Vec<Dec>,
    //    body: Box<Expr>,
    //},
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fundec {
    pub name: Ident,
    pub params: Vec<Field>,
    pub result: Option<Ident>,
    pub body: Expr,
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

pub type Ident = Spanned<SmolStr>;

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
    //Eq,
    //Neq,
    //Lt,
    //Lte,
    //Gt,
    //Gte,
}

#[macro_export]
macro_rules! ast {
    (var, simple, $span:expr, $var:expr $(,)?) => {
        (tig_ast::VarKind::Simple(($var.into(), $span)), $span)
    };

    (var, subscript, $span:expr, $var:expr, $idx:expr $(,)?) => {
        (tig_ast::VarKind::Subscript(Box::new($var), Box::new($idx)), $span)
    };

    (prog_expr, $expr:expr $(,)?) => {
        tig_ast::Program::Expr($expr)
    };

    (expr, nil, $span:expr $(,)?) => {
        (tig_ast::ExprKind::Nil, $span)
    };

    (expr, varsimple, $span:expr, $var:expr $(,)?) => {
        (
            tig_ast::ExprKind::Var(ast! {var, simple, $span, $var}),
            $span,
        )
    };

    (expr, var, $span:expr, $var:expr $(,)?) => {
        (
            tig_ast::ExprKind::Var($var),
            $span,
        )
    };

    (expr, int, $span:expr, $int:expr $(,)?) => {
        (tig_ast::ExprKind::Int($int as u64), $span)
    };

    (expr, str, $span:expr, $str:expr $(,)?) => {
        (tig_ast::ExprKind::String($str.into()), $span)
    };

    (expr, if, $span:expr, $if:expr, $then:expr $(,)?) => {
        (
            tig_ast::ExprKind::If {
                test: Box::new($if),
                then_branch: Box::new($then),
                else_branch: None,
            },
            $span,
        )
    };

    (expr, if_else, $span:expr, $if:expr, $then:expr, $else:expr $(,)?) => {
        (
            tig_ast::ExprKind::If {
                test: Box::new($if),
                then_branch: Box::new($then),
                else_branch: Some(Box::new($else)),
            },
            $span,
        )
    };

    (expr, array, $span:expr, $ty:expr, $size:expr, $init:expr $(,)?) => {
        (
            tig_ast::ExprKind::Array {
                ty: $ty,
                size: Box::new($size),
                init: Box::new($init),
            },
            $span,
        )
    };

    (expr, record, $span:expr, $ty:expr, $fields:expr $(,)?) => {
        (
            tig_ast::ExprKind::Record {
                ty: $ty,
                fields: $fields,
            },
            $span,
        )
    };

    (recordfield, $field:expr, $expr:expr $(,)?) => {
        tig_ast::FieldExpr {
            field: $field,
            expr: $expr,
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

    (type, name, $span:expr, $id:expr $(,)?) => {
        tig_ast::Type {
            span: $span,
            kind: tig_ast::TypeKind::Name($id),
        }
    };

    (ident, $span:expr, $name:expr $(,)?) => {
        ($name.into(), $span)
    };

    (fundec, $name:expr, $params:expr, $result:expr, $body:expr $(,)?) => {
        tig_ast::Fundec {
            name: $name,
            params: $params,
            result: $result,
            body: $body,
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
}
