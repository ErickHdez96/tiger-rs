use std::fmt;

use tig_common::{
    terminal::{Color, Style},
    SourceCode, Span,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpannedError {
    pub msg: String,
    pub span: Span,
}

impl SpannedError {
    pub fn new(msg: impl Into<String>, span: Span) -> Self {
        Self {
            msg: msg.into(),
            span,
        }
    }

    pub fn pretty_print(&self, source_code: &SourceCode) -> String {
        let mut file = None;

        for f in source_code.files() {
            if self.span.lo >= f.offset() as u32
                && self.span.hi < f.offset() as u32 + f.len() as u32
            {
                file = Some(f);
                break;
            }
        }

        let file = match file {
            Some(file) => file,
            None => {
                eprintln!("{}", self);
                eprintln!("Displaying errors spanning multiple files is still not supported.");
                return String::new();
            }
        };

        let span = Span::new(
            self.span.lo - file.offset() as u32,
            self.span.hi - file.offset() as u32,
        );

        let mut output = vec![format!(
            "{}{}{}: {}{}{}",
            Style::new().bold().color(Color::BrightCyan),
            if let Some(f) = file.file_path().file_name() {
                f.to_string_lossy()
            } else {
                file.file_path().to_string_lossy()
            },
            Style::clear(),
            Style::new().bold().color(Color::BrightRed),
            self.msg,
            Style::clear(),
        )];

        let (linenumber, line_offset, line) = {
            let mut linenumber = 1;
            let mut line_offset = 0;
            for (i, c) in file.content()[..span.lo as usize].chars().enumerate() {
                if c == '\n' {
                    linenumber += 1;
                    line_offset = i + 1;
                }
            }

            let mut line_end = file.len();
            for (i, c) in file.content()[line_offset..].chars().enumerate() {
                if c == '\n' {
                    line_end = i + line_offset;
                    break;
                }
            }

            let newline_hi = (&file.content()[..span.hi as usize]).lines().count();
            if linenumber != newline_hi {
                eprintln!(
                    "{}: {}-{} {} {}",
                    if let Some(f) = file.file_path().file_name() {
                        f.to_string_lossy()
                    } else {
                        file.file_path().to_string_lossy()
                    },
                    linenumber,
                    newline_hi,
                    span,
                    self
                );
                eprintln!("Displaying errors over multiple lines is still not supported.");
                return String::new();
            }

            (
                linenumber.to_string(),
                line_offset,
                &file.content()[line_offset..line_end],
            )
        };

        output.push(format!(
            "{}{} |{} {}",
            Style::new().color(Color::BrightCyan),
            linenumber,
            Style::clear(),
            line,
        ));

        output.push(format!(
            "{}{}{}{}",
            " ".repeat(linenumber.len() + " | ".len() + (self.span.lo as usize - line_offset)),
            Style::new().bold().color(Color::BrightRed),
            "^".repeat((span.hi - span.lo) as usize),
            Style::clear(),
        ));
        output.join("\n")
    }
}

impl fmt::Display for SpannedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {}): {}", self.span.lo, self.span.hi, self.msg)
    }
}

impl std::error::Error for SpannedError {}
