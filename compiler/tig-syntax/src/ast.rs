#![allow(unused_variables)]
use core::fmt;

use smol_str::SmolStr;
use tig_common::Span;

#[derive(Clone, PartialEq, Eq)]
pub enum Program {
    Expr(Expr),
    Decs(Vec<Dec>),
}

impl fmt::Debug for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            let width = f.width().unwrap_or_default();
            let padding = " ".repeat(width);
            match self {
                Program::Expr(expr) => write!(
                    f,
                    "{}{}..{}: Expr\n{:#width$?}",
                    padding,
                    expr.span.lo,
                    expr.span.hi,
                    expr,
                    width = width + 2,
                ),
                Program::Decs(decs) => write!(
                    f,
                    "{}{}..{}: Decs\n{}",
                    padding,
                    decs.iter().next().map(|s| s.span.lo).unwrap_or_default(),
                    decs.iter().last().map(|s| s.span.hi).unwrap_or_default(),
                    decs.iter()
                        .map(|d| format!("{:#width$?}", d, width = width + 2))
                        .collect::<Vec<_>>()
                        .join("\n")
                ),
            }
        } else {
            match self {
                Program::Expr(expr) => f.debug_tuple("Expr").field(&expr).finish(),
                Program::Decs(decs) => f.debug_tuple("Decs").field(&decs).finish(),
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let width = f.width().unwrap_or_default();
        let padding = " ".repeat(width);
        if f.alternate() {
            match &self.kind {
                ExprKind::Nil => write!(f, "{}{}..{}: Nil", padding, self.span.lo, self.span.hi,),
                ExprKind::Integer(n) => write!(
                    f,
                    "{}{}..{}: Integer({})",
                    padding, self.span.lo, self.span.hi, n
                ),
                ExprKind::String(s) => write!(
                    f,
                    "{}{}..{}: String({})",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    String::from_utf8_lossy(s),
                ),
                ExprKind::Array {
                    type_id,
                    size,
                    initial_value,
                } => write!(
                    f,
                    "{}{}..{}: Array\n\
                     {}{}..{}: Type\n{:#width$?}\n\
                     {}{}..{}: Size\n{:#width$?}\n\
                     {}{}..{}: InitialValue\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    type_id.span.lo,
                    type_id.span.hi,
                    type_id,
                    " ".repeat(width + 2),
                    size.span.lo,
                    size.span.hi,
                    size,
                    " ".repeat(width + 2),
                    initial_value.span.lo,
                    initial_value.span.hi,
                    initial_value,
                    width = width + 4,
                ),
                ExprKind::Record { type_id, fields } => write!(
                    f,
                    "{}{}..{}: Record\n\
                     {}{}..{}: Type\n{:#width$?}\
                     {}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    type_id.span.lo,
                    type_id.span.hi,
                    type_id,
                    if !fields.is_empty() {
                        format!(
                            "\n{}{}..{}: Fields\n{}",
                            " ".repeat(width + 2),
                            fields
                                .iter()
                                .next()
                                .map(|f| f.field.span.lo)
                                .unwrap_or_default(),
                            fields
                                .iter()
                                .last()
                                .map(|f| f.value.span.hi)
                                .unwrap_or_default(),
                            fields
                                .iter()
                                .map(|f| format!("{:#width$?}", f, width = width + 4))
                                .collect::<Vec<_>>()
                                .join("\n"),
                        )
                    } else {
                        "".to_string()
                    },
                    width = width + 4,
                ),
                ExprKind::LValue(lvalue) => write!(
                    f,
                    "{}{}..{}: LValue\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    lvalue,
                    width = width + 2,
                ),
                ExprKind::Call { func, arguments } => write!(
                    f,
                    "{}{}..{}: Call\n\
                     {}{}..{}: Func({}){}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    func.span.lo,
                    func.span.hi,
                    func.value,
                    if !arguments.is_empty() {
                        format!(
                            "\n{}{}..{}: Arguments\n{}",
                            " ".repeat(width + 2),
                            arguments
                                .iter()
                                .next()
                                .map(|a| a.span.lo)
                                .unwrap_or_default(),
                            arguments
                                .iter()
                                .last()
                                .map(|a| a.span.hi)
                                .unwrap_or_default(),
                            arguments
                                .iter()
                                .map(|a| format!("{:#width$?}", a, width = width + 4))
                                .collect::<Vec<_>>()
                                .join("\n")
                        )
                    } else {
                        "".to_string()
                    },
                ),
                ExprKind::Negate(expr) => write!(
                    f,
                    "{}{}..{}: Negate\n{:#width$?}",
                    padding, self.span.lo, self.span.hi, expr,
                ),
                ExprKind::BinOp { op, left, right } => write!(
                    f,
                    "{}{}..{}: BinaryOp({})\n\
                     {}{}..{}: Left\n{:#width$?}\n\
                     {}{}..{}: Right\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    op,
                    " ".repeat(width + 2),
                    left.span.lo,
                    left.span.hi,
                    left,
                    " ".repeat(width + 2),
                    right.span.lo,
                    right.span.hi,
                    right,
                    width = width + 4,
                ),
                ExprKind::Exprs(exprs) => write!(
                    f,
                    "{}{}..{}: Exprs\n{}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    exprs
                        .iter()
                        .map(|e| format!(
                            "{}{}..{}: Expr\n{:#width$?}",
                            " ".repeat(width + 2),
                            e.span.lo,
                            e.span.hi,
                            e,
                            width = width + 4,
                        ))
                        .collect::<Vec<_>>()
                        .join("\n"),
                ),
                ExprKind::Assign {
                    destination,
                    source,
                } => write!(
                    f,
                    "{}{}..{}: Assign\n\
                     {}{}..{}: LValue\n{:#width$?}\n\
                     {}{}..{}: Expr\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    destination.span().lo,
                    destination.span().hi,
                    destination,
                    " ".repeat(width + 2),
                    source.span.lo,
                    source.span.hi,
                    source,
                    width = width + 4,
                ),
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                } => write!(
                    f,
                    "{}{}..{}: If\n\
                     {}{}..{}: Condition\n{:#width$?}\n\
                     {}{}..{}: Then\n{:#width$?}{}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    cond.span.lo,
                    cond.span.hi,
                    cond,
                    " ".repeat(width + 2),
                    then_branch.span.lo,
                    then_branch.span.hi,
                    then_branch,
                    if let Some(else_) = else_branch {
                        format!(
                            "\n{}{}..{}: Else\n{:#width$?}",
                            " ".repeat(width + 2),
                            else_.span.lo,
                            else_.span.hi,
                            else_,
                            width = width + 4
                        )
                    } else {
                        "".to_string()
                    },
                    width = width + 4,
                ),
                ExprKind::While { cond, body } => write!(
                    f,
                    "{}{}..{}: While\n\
                     {}{}..{}: Condition\n{:#width$?}\n\
                     {}{}..{}: Body\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    cond.span.lo,
                    cond.span.hi,
                    cond,
                    " ".repeat(width + 2),
                    body.span.lo,
                    body.span.hi,
                    body,
                    width = width + 4,
                ),
                ExprKind::For {
                    iterator,
                    start,
                    end,
                    body,
                } => write!(
                    f,
                    "{}{}..{}: For\n\
                     {}{}..{}: Ident\n{:#width$?}\n\
                     {}{}..{}: Start\n{:#width$?}\n\
                     {}{}..{}: End\n{:#width$?}\n\
                     {}{}..{}: Body\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    iterator.span.lo,
                    iterator.span.hi,
                    iterator,
                    " ".repeat(width + 2),
                    start.span.lo,
                    start.span.hi,
                    start,
                    " ".repeat(width + 2),
                    end.span.lo,
                    end.span.hi,
                    end,
                    " ".repeat(width + 2),
                    body.span.lo,
                    body.span.hi,
                    body,
                    width = width + 4,
                ),
                ExprKind::Break => {
                    write!(f, "{}{}..{}: Break", padding, self.span.lo, self.span.hi)
                }
                ExprKind::Let { decs, exprs } => write!(
                    f,
                    "{}{}..{}: Let{}\n\
                     {}{}..{}: Exprs\n{}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    if !decs.is_empty() {
                        format!(
                            "\n{}{}..{}: Decs\n{}",
                            " ".repeat(width + 2),
                            decs.iter().next().map(|d| d.span.lo).unwrap_or_default(),
                            decs.iter().last().map(|d| d.span.hi).unwrap_or_default(),
                            decs.iter()
                                .map(|d| format!("{:#width$?}", d, width = width + 4))
                                .collect::<Vec<_>>()
                                .join("\n")
                        )
                    } else {
                        "".to_string()
                    },
                    " ".repeat(width + 2),
                    exprs.iter().next().map(|e| e.span.lo).unwrap_or_default(),
                    exprs.iter().last().map(|e| e.span.hi).unwrap_or_default(),
                    exprs
                        .iter()
                        .map(|e| format!("{:#width$?}", e, width = width + 4))
                        .collect::<Vec<_>>()
                        .join("\n")
                ),
            }
        } else {
            f.debug_struct("Expr")
                .field("span", &self.span)
                .field("kind", &self.kind)
                .finish()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    // Literals
    Nil,
    Integer(usize),
    String(Vec<u8>), // Strings aren't utf-8, as they can contain arbitrary bytes through escape sequences

    // Array and record creations.
    Array {
        type_id: Ident,
        size: Box<Expr>,
        initial_value: Box<Expr>,
    },

    Record {
        type_id: Ident,
        fields: Vec<RecordField>,
    },

    // Object creation
    // New { type_id: Ident },

    // Variables, field, elements of an array
    LValue(LValue),

    // Function call
    Call {
        func: Ident,
        arguments: Vec<Expr>,
    },

    // Method call
    // MethodCall { object: LValue, func: Ident, arguments: Vec<Expr> },

    // Operations
    Negate(Box<Expr>),
    BinOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Exprs(Vec<Expr>),

    // Assignment
    Assign {
        destination: LValue,
        source: Box<Expr>,
    },

    // Control structures
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },
    While {
        cond: Box<Expr>,
        body: Box<Expr>,
    },
    For {
        iterator: Ident,
        start: Box<Expr>,
        end: Box<Expr>,
        body: Box<Expr>,
    },
    Break,
    Let {
        decs: Vec<Dec>,
        exprs: Vec<Expr>,
    },
}

#[derive(Clone, PartialEq, Eq)]
pub struct RecordField {
    pub field: Ident,
    pub value: Expr,
}

impl fmt::Debug for RecordField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            let width = f.width().unwrap_or_default();
            let padding = " ".repeat(width);
            write!(
                f,
                "{}{}..{}: RecordField\n\
                 {}{}..{}: Field({})\n\
                 {}{}..{}: Expr\n{:#width$?}",
                padding,
                self.field.span.lo,
                self.value.span.hi,
                " ".repeat(width + 2),
                self.field.span.lo,
                self.field.span.hi,
                self.field.value,
                " ".repeat(width + 2),
                self.value.span.lo,
                self.value.span.hi,
                self.value,
                width = width + 4,
            )
        } else {
            f.debug_struct("RecordField")
                .field("field", &self.field)
                .field("value", &self.value)
                .finish()
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum LValue {
    Ident(Ident),
    FieldAccess(Box<LValue>, Ident),
    ArrayAccess(Box<LValue>, Box<Expr>),
}

impl LValue {
    pub fn span(&self) -> Span {
        match self {
            LValue::Ident(id) => id.span,
            LValue::FieldAccess(lvalue, field) => lvalue.span().extend(field.span),
            LValue::ArrayAccess(lvalue, expr) => lvalue.span().extend(expr.span),
        }
    }
}

impl fmt::Debug for LValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            let width = f.width().unwrap_or_default();
            let padding = " ".repeat(width);
            match self {
                LValue::Ident(id) => write!(
                    f,
                    "{}{}..{}: Ident({})",
                    padding, id.span.lo, id.span.hi, id.value,
                ),
                LValue::FieldAccess(lvalue, field) => write!(
                    f,
                    "{}{}..{}: FieldAccess\n\
                     {}{}..{}: Object\n{:#width$?}\n\
                     {}{}..{}: Field\n{:#width$?}",
                    padding,
                    self.span().lo,
                    self.span().hi,
                    " ".repeat(width + 2),
                    lvalue.span().lo,
                    lvalue.span().hi,
                    lvalue,
                    " ".repeat(width + 2),
                    field.span.lo,
                    field.span.hi,
                    field,
                    width = width + 4,
                ),
                LValue::ArrayAccess(lvalue, expr) => write!(
                    f,
                    "{}{}..{}: ArrayAccess\n\
                     {}{}..{}: Array\n{:#width$?}\n\
                     {}{}..{}: Index\n{:#width$?}",
                    padding,
                    self.span().lo,
                    self.span().hi,
                    " ".repeat(width + 2),
                    lvalue.span().lo,
                    lvalue.span().hi,
                    lvalue,
                    " ".repeat(width + 2),
                    expr.span.lo,
                    expr.span.hi,
                    expr,
                    width = width + 4,
                ),
            }
        } else {
            match self {
                LValue::Ident(_) => todo!(),
                LValue::FieldAccess(_, _) => todo!(),
                LValue::ArrayAccess(_, _) => todo!(),
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Eq,
    Neq,
    Gt,
    Lt,
    Gte,
    Lte,
    And,
    Or,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                BinOp::Add => "+",
                BinOp::Subtract => "-",
                BinOp::Multiply => "*",
                BinOp::Divide => "/",
                BinOp::Eq => "=",
                BinOp::Neq => "<>",
                BinOp::Gt => ">",
                BinOp::Lt => "<",
                BinOp::Gte => ">=",
                BinOp::Lte => "<=",
                BinOp::And => "&",
                BinOp::Or => "|",
            }
        )
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Dec {
    pub span: Span,
    pub kind: DecKind,
}

impl fmt::Debug for Dec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            let width = f.width().unwrap_or_default();
            let padding = " ".repeat(width);
            match &self.kind {
                DecKind::Type { name, ty } => write!(
                    f,
                    "{}{}..{}: TypeDec\n\
                     {}{}..{}: TypeName\n{:#width$?}\n\
                     {}{}..{}: Type\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    name.span.lo,
                    name.span.hi,
                    name,
                    " ".repeat(width + 2),
                    ty.span.lo,
                    ty.span.hi,
                    ty,
                    width = width + 4,
                ),
                DecKind::Variable { name, ty, value } => write!(
                    f,
                    "{}{}..{}: VarDec\n\
                     {}{}..{}: Variable({}){}\n\
                     {}{}..{}: Value\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    name.span.lo,
                    name.span.hi,
                    name.value,
                    if let Some(ty) = ty {
                        format!(
                            "\n{}{}..{}: Type({})",
                            " ".repeat(width + 2),
                            ty.span.lo,
                            ty.span.hi,
                            ty.value,
                        )
                    } else {
                        "".to_string()
                    },
                    " ".repeat(width + 2),
                    value.span.lo,
                    value.span.hi,
                    value,
                    width = width + 4,
                ),
                DecKind::Function {
                    name,
                    parameters,
                    ret_ty,
                    body,
                } => write!(
                    f,
                    "{}{}..{}: Function\n\
                     {}{}..{}: Name({}){}{}\n\
                     {}{}..{}: Body\n{:#width$?}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    name.span.lo,
                    name.span.hi,
                    name.value,
                    if parameters.is_empty() {
                        "".to_string()
                    } else {
                        format!(
                            "\n{}{}..{}: Parameters\n{}",
                            " ".repeat(width + 2),
                            parameters
                                .iter()
                                .next()
                                .map(|p| p.name.span.lo)
                                .unwrap_or_default(),
                            parameters
                                .iter()
                                .next()
                                .map(|p| p.ty.span.hi)
                                .unwrap_or_default(),
                            parameters
                                .iter()
                                .map(|p| format!("{:#width$?}", p, width = width + 4))
                                .collect::<Vec<_>>()
                                .join("\n"),
                        )
                    },
                    match ret_ty {
                        Some(ret_ty) => format!(
                            "\n{}{}..{}: ReturnType({})",
                            " ".repeat(width + 2),
                            ret_ty.span.lo,
                            ret_ty.span.hi,
                            ret_ty.value,
                        ),
                        None => "".to_string(),
                    },
                    " ".repeat(width + 2),
                    body.span.lo,
                    body.span.hi,
                    body,
                    width = width + 4,
                ),
                DecKind::Primitive {
                    name,
                    parameters,
                    ret_ty,
                } => write!(
                    f,
                    "{}{}..{}: Primitive\n{}{}..{}: Name({}){}{}",
                    padding,
                    self.span.lo,
                    self.span.hi,
                    " ".repeat(width + 2),
                    name.span.lo,
                    name.span.hi,
                    name.value,
                    if parameters.is_empty() {
                        "".to_string()
                    } else {
                        format!(
                            "\n{}{}..{}: Parameters\n{}",
                            " ".repeat(width + 2),
                            parameters
                                .iter()
                                .next()
                                .map(|p| p.name.span.lo)
                                .unwrap_or_default(),
                            parameters
                                .iter()
                                .next()
                                .map(|p| p.ty.span.hi)
                                .unwrap_or_default(),
                            parameters
                                .iter()
                                .map(|p| format!("{:#width$?}", p, width = width + 4))
                                .collect::<Vec<_>>()
                                .join("\n"),
                        )
                    },
                    match ret_ty {
                        Some(ret_ty) => format!(
                            "\n{}{}..{}: ReturnType({})",
                            " ".repeat(width + 2),
                            ret_ty.span.lo,
                            ret_ty.span.hi,
                            ret_ty.value,
                        ),
                        None => "".to_string(),
                    }
                ),
            }
        } else {
            f.debug_struct("Dec")
                .field("span", &self.span)
                .field("kind", &self.kind)
                .finish()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecKind {
    /// Type declaration.
    Type { name: Ident, ty: Type },
    // Class definition (alternative form).
    // Class { name: Ident, extends: Option<Ident>, fields: Vec<ClassField> },
    /// Variable declaration.
    Variable {
        name: Ident,
        ty: Option<Ident>,
        value: Box<Expr>,
    },

    /// Function declaration.
    Function {
        name: Ident,
        parameters: Vec<TyField>,
        ret_ty: Option<Ident>,
        body: Box<Expr>,
    },

    /// Primitive declaration.
    Primitive {
        name: Ident,
        parameters: Vec<TyField>,
        ret_ty: Option<Ident>,
    },
    // Imports are evaluated during parsing.
}

#[derive(Clone, PartialEq, Eq)]
pub struct Ident {
    pub span: Span,
    pub value: SmolStr,
}

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(
                f,
                "{}{}..{}: Ident({})",
                " ".repeat(f.width().unwrap_or_default()),
                self.span.lo,
                self.span.hi,
                self.value
            )
        } else {
            f.debug_struct("Ident")
                .field("span", &self.span)
                .field("value", &self.value)
                .finish()
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct TyField {
    pub name: Ident,
    pub ty: Ident,
}

impl fmt::Debug for TyField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            let width = f.width().unwrap_or_default();
            write!(
                f,
                "{}{}..{}: Name({}) - {}..{}: Type({})",
                " ".repeat(width),
                self.name.span.lo,
                self.name.span.hi,
                self.name.value,
                self.ty.span.lo,
                self.ty.span.hi,
                self.ty.value,
            )
        } else {
            f.debug_struct("Ident")
                .field("name", &self.name)
                .field("ty", &self.ty)
                .finish()
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Type {
    pub span: Span,
    pub kind: TypeKind,
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            let width = f.width().unwrap_or_default();
            let padding = " ".repeat(width);
            match &self.kind {
                TypeKind::Id(id) => {
                    write!(
                        f,
                        "{}{}..{}: TypeId({})",
                        padding, self.span.lo, self.span.hi, id,
                    )
                }
                TypeKind::Record(fields) => {
                    write!(
                        f,
                        "{}{}..{}: Record\n{}",
                        padding,
                        self.span.lo,
                        self.span.hi,
                        fields
                            .iter()
                            .map(|field| format!("{:#width$?}", field, width = width + 2,))
                            .collect::<Vec<_>>()
                            .join("\n"),
                    )
                }
                TypeKind::Array(id) => {
                    write!(
                        f,
                        "{}{}..{}: TypeArray({})",
                        padding, self.span.lo, self.span.hi, id,
                    )
                }
            }
        } else {
            f.debug_struct("Ident")
                .field("span", &self.span)
                .field("kind", &self.kind)
                .finish()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    Id(SmolStr),
    Record(Vec<TyField>),
    Array(SmolStr),
    // Class definition
    // Class { extends: Option<Ident>, fields: Vec<ClassField> },
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::expect;

    #[test]
    fn test_basic_debug_impl() {
        let ident = Ident {
            span: Span::new(1, 2),
            value: "x".into(),
        };

        let expected = expect![["1..2: Ident(x)"]];
        expected.assert_eq(&format!("{:#?}", ident));

        let expected = expect![["  1..2: Ident(x)"]];
        expected.assert_eq(&format!("{:#2?}", ident));

        let expected = expect![["        1..2: Ident(x)"]];
        expected.assert_eq(&format!("{:#8?}", ident));

        let ty = Type {
            span: Span::new(0, 19),
            kind: TypeKind::Record(vec![
                TyField {
                    name: Ident {
                        span: Span::new(1, 2),
                        value: "x".into(),
                    },
                    ty: Ident {
                        span: Span::new(4, 7),
                        value: "int".into(),
                    },
                },
                TyField {
                    name: Ident {
                        span: Span::new(9, 10),
                        value: "y".into(),
                    },
                    ty: Ident {
                        span: Span::new(12, 18),
                        value: "string".into(),
                    },
                },
            ]),
        };

        let expected = expect![[r#"
            0..19: Record
              1..2: Name(x) - 4..7: Type(int)
              9..10: Name(y) - 12..18: Type(string)"#]];
        expected.assert_eq(&format!("{:#?}", ty));
    }
}
