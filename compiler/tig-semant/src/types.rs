use std::{cell::RefCell, fmt, rc::Rc};

use tig_common::Unique;
use tig_syntax::ast;

pub type RType = Rc<Type>;

#[derive(Debug, Clone, Eq)]
pub enum Type {
    Int,
    String,
    Record {
        fields: Vec<RecordField>,
        unique: Unique,
    },
    Array {
        ty: RType,
        unique: Unique,
    },
    Nil,
    Unit,
    // FIXME Self referential types are probably a cycle.
    Name {
        name: ast::Ident,
        ty: RefCell<Option<RType>>,
    },
    /// To allow to generate multiple typecheck errors, a hole is generated.
    /// A hole matches with every other type, thus preventing an invalid type from generating more
    /// types along the way.
    ///
    /// For example, in the expression `a = b`, if b has type string, and a is an undefined
    /// variable, looking up `a` will generate an error and return a hole. Then when checking the
    /// comparsion, it will typecheck correctly, generating only one error instead of two, and
    /// allowing more errors to be generated, instead of exiting on the first one.
    Hole,
}

impl Type {
    pub fn int() -> RType {
        INT_TYPE.with(|i| i.clone())
    }

    pub fn string() -> RType {
        STRING_TYPE.with(|s| s.clone())
    }

    pub fn record(fields: Vec<RecordField>) -> RType {
        Rc::new(Type::Record {
            fields,
            unique: Unique::new(),
        })
    }

    pub fn array(ty: RType) -> RType {
        Rc::new(Type::Array {
            ty,
            unique: Unique::new(),
        })
    }

    pub fn nil() -> RType {
        NIL_TYPE.with(|n| n.clone())
    }

    pub fn unit() -> RType {
        UNIT_TYPE.with(|u| u.clone())
    }

    pub fn name(name: ast::Ident, ty: Option<RType>) -> RType {
        Rc::new(Type::Name {
            name,
            ty: RefCell::new(ty),
        })
    }

    pub fn hole() -> RType {
        HOLE_TYPE.with(|h| h.clone())
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => write!(f, "int"),
            Type::String => write!(f, "string"),
            Type::Record { fields, .. } => write!(
                f,
                "{{{}}}",
                fields
                    .iter()
                    .map(|f| f.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Type::Array { ty, .. } => write!(f, "{}[]", ty),
            Type::Nil => write!(f, "nil"),
            Type::Unit => write!(f, "unit"),
            Type::Name { name, .. } => write!(f, "{}", name.value),
            Type::Hole => write!(f, "_"),
        }
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Int, Type::Int) => true,
            (Type::String, Type::String) => true,
            (
                Type::Record {
                    unique: lunique, ..
                },
                Type::Record {
                    unique: runique, ..
                },
            ) => lunique == runique,
            (
                Type::Array {
                    unique: lunique, ..
                },
                Type::Array {
                    unique: runique, ..
                },
            ) => lunique == runique,
            // Nil returns true when compared to a record,
            // but nil = nil is invalid
            (Type::Record { .. }, Type::Nil) => true,
            (Type::Nil, Type::Record { .. }) => true,
            (Type::Unit, Type::Unit) => true,
            (
                Type::Name { name, ty },
                Type::Name {
                    name: rname,
                    ty: rty,
                },
            ) => name == rname && ty == rty,
            (_, Type::Hole) | (Type::Hole, _) => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordField {
    pub name: ast::Ident,
    pub ty: RType,
}

impl fmt::Display for RecordField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.name.value, self.ty)
    }
}

thread_local! {
    static INT_TYPE: RType = Rc::new(Type::Int);
    static STRING_TYPE: RType = Rc::new(Type::String);
    static NIL_TYPE: RType = Rc::new(Type::Nil);
    static UNIT_TYPE: RType = Rc::new(Type::Unit);
    static HOLE_TYPE: RType = Rc::new(Type::Hole);
}
