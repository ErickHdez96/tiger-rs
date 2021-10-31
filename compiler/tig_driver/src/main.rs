use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use std::{fs, io, io::prelude::*, path::Path};
use tig_syntax::parse_str;

#[derive(Debug)]
struct Compiler {
    source: String,
}

impl Compiler {
    fn new() -> Self {
        Self {
            source: String::new(),
        }
    }

    fn add_file(mut self, p: impl AsRef<Path>) -> io::Result<Self> {
        let p = p.as_ref();
        let mut f = fs::File::open(p)?;
        f.read_to_string(&mut self.source)?;
        Ok(self)
    }

    fn compile(self) {
        let (_, errs) = parse_str(&self.source);

        if errs.is_empty() {
            return;
        }

        let errs = errs.into_iter().map(|e| e.map(|tok| tok.to_string()));
        for e in errs {
            let report = Report::build(ReportKind::Error, (), e.span().start);

            let report = match e.reason() {
                chumsky::error::SimpleReason::Unexpected => report
                    .with_message(format!(
                        "{}, expected {}",
                        if e.found().is_some() {
                            "Unexpected token in input"
                        } else {
                            "Unexpected end of input"
                        },
                        if e.expected().len() == 0 {
                            "end of input".to_string()
                        } else {
                            e.expected()
                                .map(|x| x.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        }
                    ))
                    .with_label(
                        Label::new(e.span())
                            .with_message(format!(
                                "Unexpected token {}",
                                e.found()
                                    .unwrap_or(&"end of file".to_string())
                                    .fg(Color::Red)
                            ))
                            .with_color(Color::Red),
                    ),
                _ => todo!(),
            };

            report.finish().print(Source::from(&self.source)).unwrap();
        }
    }
}

fn main() -> io::Result<()> {
    let path = std::env::args().nth(1).expect("USAGE: tiger file.tig");
    Compiler::new().add_file(path)?.compile();
    Ok(())
}
