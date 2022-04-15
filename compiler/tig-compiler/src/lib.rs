use std::{io::Read, path::PathBuf};

use tig_common::SourceCode;
use tig_error::ParserError;
use tig_syntax::parser::parse_source_code;

#[derive(Debug, Default)]
pub struct Compiler {
    source_code: SourceCode,
}

type CResult<T> = Result<T, Vec<ParserError>>;

impl Compiler {
    pub fn add_file(mut self, file: impl Into<PathBuf>) -> std::io::Result<Self> {
        self.source_code.add_file(file)?;
        Ok(self)
    }

    pub fn add_reader<R: Read>(
        mut self,
        file_name: impl Into<PathBuf>,
        reader: R,
    ) -> std::io::Result<Self> {
        self.source_code.add_reader(file_name, reader)?;
        Ok(self)
    }

    pub fn display_ast(&mut self) -> CResult<()> {
        let result = parse_source_code(&mut self.source_code);

        if let Some(ast) = result.program {
            println!("{:#?}", ast);
        }

        if result.errors.is_empty() {
            Ok(())
        } else {
            Err(result.errors)
        }
    }

    pub fn display_errors(&self, errors: &[ParserError]) {
        for e in errors.iter().take(3) {
            eprintln!("{}", e.pretty_print(&self.source_code));
        }
    }
}
