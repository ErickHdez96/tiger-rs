use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Style {
    bold: bool,
    color: Option<Color>,
}

impl Style {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn clear() -> Self {
        Self::default()
    }

    pub fn color(mut self, c: Color) -> Self {
        self.color = Some(c);
        self
    }

    pub fn bold(mut self) -> Self {
        self.bold = true;
        self
    }
}

impl fmt::Display for Style {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let modifier = match (self.bold, self.color) {
            (false, None) => return write!(f, "\x1b[0m"),
            (true, None) => return write!(f, "\x1b[1m"),
            (b, Some(fg)) => {
                let mut modifiers = vec![];
                if b {
                    modifiers.push("1".to_string());
                }
                modifiers.push(fg.to_string());
                modifiers.join(";")
            }
        };
        write!(f, "\x1b[{}m", modifier)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Color {
    BrightRed,
    BrightCyan,
}

impl fmt::Display for Color {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Color::BrightRed => "31",
                Color::BrightCyan => "96",
            }
        )
    }
}
