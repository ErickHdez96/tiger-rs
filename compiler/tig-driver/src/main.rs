use std::path::PathBuf;

use clap::Parser;
use tig_compiler::Compiler;

#[derive(Debug, Parser)]
struct TigerCli {
    #[clap(short = 'A', long = "ast-display")]
    display_ast: bool,

    #[clap(parse(from_os_str), value_name = "INPUT")]
    input_file: Option<PathBuf>,
}

fn main() -> std::io::Result<()> {
    let cli = TigerCli::parse();

    let mut compiler = match cli.input_file {
        Some(file_path) => Compiler::default().add_file(file_path)?,
        None => Compiler::default().add_reader("-", std::io::stdin())?,
    };

    if cli.display_ast {
        match compiler.display_ast() {
            Ok(_) => {}
            Err(errs) => {
                // At most display 3 errors
                compiler.display_errors(&errs[..std::cmp::min(3, errs.len())]);
                std::process::exit(1);
            }
        }
    }

    Ok(())
}
