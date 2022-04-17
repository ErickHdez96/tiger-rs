use std::{cell::RefCell, rc::Rc};

use crate::Frame;
use tig_common::{temp::Label, Unique};

#[derive(Debug, Clone, Eq)]
pub struct Level<F: Frame> {
    pub frame: Rc<RefCell<F>>,
    // Use Rc?
    pub parent: Option<Box<Level<F>>>,
    unique: Unique,
}

// Faster level equality, as a level can only be equal to itself.
impl<F: Frame> PartialEq for Level<F> {
    fn eq(&self, other: &Self) -> bool {
        self.unique == other.unique
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Access<F: Frame> {
    pub level: Level<F>,
    pub access: F::Access,
}

impl<F: Frame> Level<F> {
    pub fn outermost() -> Self {
        let frame = F::new(Label::raw("root"), vec![]);
        Self {
            frame: Rc::new(RefCell::new(frame)),
            parent: None,
            unique: Unique::new(),
        }
    }

    pub fn new_level(&self, name: Label, formals: impl Into<Vec<bool>>) -> Level<F> {
        let frame = F::new(name, formals);

        Self {
            frame: Rc::new(RefCell::new(frame)),
            parent: Some(Box::new(self.clone())),
            unique: Unique::new(),
        }
    }

    pub fn formals(&self) -> Vec<Access<F>> {
        self.frame
            .borrow()
            .formals()
            .iter()
            .map(|f| Access {
                level: self.clone(),
                access: f.clone(),
            })
            .collect()
    }

    pub fn alloc_local(&mut self, escapes: bool) -> Access<F> {
        Access {
            level: self.clone(),
            access: self.frame.borrow_mut().alloc_local(escapes),
        }
    }
}
