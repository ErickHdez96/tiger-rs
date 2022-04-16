use std::cell::Cell;

use smol_str::SmolStr;

/// A Label allows to reference a specific memory location, before knowing where it lays.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Label {
    Generated(usize),
    Raw(SmolStr),
    Named(SmolStr),
}

impl Label {
    /// Creates a new unique label.
    pub fn new() -> Self {
        LABEL_COUNTER.with(|counter| {
            let c = counter.get();
            counter.set(c + 1);
            Self::Generated(c)
        })
    }

    /// Creates a new label named exactly `raw` (that will be the name in the asm).
    pub fn raw(name: impl Into<SmolStr>) -> Self {
        Self::Raw(name.into())
    }

    /// Creates a new label named `name`, the name may be modified before printing to the asm.
    pub fn named(name: impl AsRef<str>) -> Self {
        LABEL_COUNTER.with(|counter| {
            let c = counter.get();
            counter.set(c + 1);
            Self::Named(format!("{}{}", name.as_ref(), c).into())
        })
    }
}

impl Default for Label {
    fn default() -> Self {
        Self::new()
    }
}

/// A Temp is similar to a register. But we are allowed to allocate an infinite number of Temps.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Temp {
    Generated(usize),
    Named(SmolStr),
}

impl Temp {
    /// Creates a new unique temp.
    pub fn new() -> Self {
        TEMP_COUNTER.with(|counter| {
            let c = counter.get();
            counter.set(c + 1);
            Self::Generated(c)
        })
    }

    /// Creates a new temp named `name`.
    pub fn named(name: impl Into<SmolStr>) -> Self {
        Self::Named(name.into())
    }
}

impl Default for Temp {
    fn default() -> Self {
        Self::new()
    }
}

thread_local! {
    static LABEL_COUNTER: Cell<usize>  = Cell::new(0);
    static TEMP_COUNTER: Cell<usize>  = Cell::new(0);
}
