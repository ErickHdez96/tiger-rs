#![allow(dead_code)]
#![allow(unused_variables)]

use std::{cell::RefCell, rc::Rc};

use tig_arch::Frame;
use tig_common::temp::Label;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Level<F: Frame> {
    frame: Rc<RefCell<F>>,
    // Use Rc?
    parent: Option<Box<Level<F>>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Access<F: Frame> {
    level: Level<F>,
    access: F::Access,
}

impl<F: Frame> Level<F> {
    pub fn outermost() -> Self {
        let frame = F::new(Label::raw("root"), vec![]);
        Self {
            frame: Rc::new(RefCell::new(frame)),
            parent: None,
        }
    }

    pub fn new_level(&self, name: Label, formals: impl Into<Vec<bool>>) -> Level<F> {
        let frame = F::new(name, formals);

        Self {
            frame: Rc::new(RefCell::new(frame)),
            parent: Some(Box::new(self.clone())),
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
