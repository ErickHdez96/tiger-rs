use std::{io::Read, marker::PhantomData, path::PathBuf};

use tig_common::SourceCode;
use tig_error::SpannedError;
use tig_semant::{frame::Fragment, translate_program, Frame, TranslateResult};
use tig_syntax::{ast, parser::parse_source_code, ParseResult};

#[derive(Debug)]
pub struct Compiler<F: Frame> {
    source_code: SourceCode,
    errors: Vec<SpannedError>,
    _f: PhantomData<F>,
}

impl<F: Frame> Default for Compiler<F> {
    fn default() -> Self {
        Self {
            source_code: SourceCode::default(),
            errors: vec![],
            _f: PhantomData,
        }
    }
}

type CResult<T> = Result<T, Vec<SpannedError>>;

impl<F: Frame> Compiler<F> {
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

    fn parse(&mut self) -> CResult<ast::Program> {
        let ParseResult {
            program,
            mut errors,
        } = parse_source_code(&mut self.source_code);

        self.errors.append(&mut errors);
        match program {
            Some(p) => Ok(p),
            None => Err(std::mem::take(&mut self.errors)),
        }
    }

    fn translate(&mut self, ast: ast::Program) -> CResult<Vec<Fragment<F>>> {
        let TranslateResult {
            fragments,
            mut errors,
            ..
        } = translate_program::<F>(ast);

        if errors.is_empty() {
            Ok(fragments)
        } else {
            self.errors.append(&mut errors);
            Err(std::mem::take(&mut self.errors))
        }
    }

    pub fn compile(&mut self) -> CResult<()> {
        let ast = self.parse()?;
        self.translate(ast)?;

        Ok(())
    }

    pub fn display_ast(&mut self) -> CResult<()> {
        let ast = self.parse()?;

        println!("{:#?}", ast);

        self.ret_errors()
    }

    fn ret_errors(&mut self) -> CResult<()> {
        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(std::mem::take(&mut self.errors))
        }
    }

    pub fn display_errors(&self, errors: &[SpannedError]) {
        for e in errors {
            eprintln!("{}", e.pretty_print(&self.source_code));
        }
    }
}
