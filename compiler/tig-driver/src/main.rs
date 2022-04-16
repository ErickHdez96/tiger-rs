use std::path::PathBuf;

use clap::Parser;
use tig_arch::{amd64::Amd64Frame, Frame};
use tig_compiler::Compiler;
use tig_syntax::ast;

#[derive(Debug, Parser)]
struct TigerCli {
    #[clap(short = 'A', long = "ast-display")]
    display_ast: bool,

    #[clap(
        short = 'T',
        long = "type-sizes",
        help = "Displays the sizes of diferent types"
    )]
    display_type_sizes: bool,

    #[clap(parse(from_os_str), value_name = "INPUT")]
    input_file: Option<PathBuf>,
}

fn new_compiler<F: Frame>(file: Option<PathBuf>) -> Compiler<F> {
    let (name, result) = match file {
        Some(file_path) => (
            file_path.to_string_lossy().to_string(),
            Compiler::default().add_file(file_path),
        ),
        None => (
            "-".into(),
            Compiler::default().add_reader("-", std::io::stdin()),
        ),
    };

    match result {
        Ok(c) => c,
        Err(e) => {
            eprintln!("{}: {}", name, e);
            std::process::exit(1);
        }
    }
}

fn main() -> std::io::Result<()> {
    env_logger::init();
    let cli = TigerCli::parse();

    if cli.display_type_sizes {
        display_type_sizes();
        return Ok(());
    }

    let mut compiler = new_compiler::<Amd64Frame>(cli.input_file);

    if cli.display_ast {
        return match compiler.display_ast() {
            Ok(_) => Ok(()),
            Err(errs) => {
                // At most display 3 errors
                compiler.display_errors(&errs[..std::cmp::min(3, errs.len())]);
                std::process::exit(1);
            }
        };
    }

    if let Err(errs) = compiler.compile() {
        // At most display 3 errors
        compiler.display_errors(&errs[..std::cmp::min(3, errs.len())]);
        std::process::exit(1);
    }

    Ok(())
}

fn display_type_sizes() {
    use tig_common::{Env, SourceCode, SourceFile, Span};
    use tig_error::SpannedError;
    use tig_semant::{types, ExpTy};

    println!("SourceCode:\t{} bytes", std::mem::size_of::<SourceCode>());
    println!("SourceFile:\t{} bytes", std::mem::size_of::<SourceFile>());
    println!("Env:\t\t{} bytes", std::mem::size_of::<Env<(), ()>>());
    println!("Span:\t\t{} bytes", std::mem::size_of::<Span>());
    println!(
        "SpannedError:\t{} bytes",
        std::mem::size_of::<SpannedError>()
    );
    println!("Program:\t{} bytes", std::mem::size_of::<ast::Program>());
    println!("Expr:\t\t{} bytes", std::mem::size_of::<ast::Expr>());
    println!("ExprKind:\t{} bytes", std::mem::size_of::<ast::ExprKind>());
    println!(
        "RecordField:\t{} bytes",
        std::mem::size_of::<ast::RecordField>()
    );
    println!("LValue:\t\t{} bytes", std::mem::size_of::<ast::LValue>());
    println!("BinOp:\t\t{} bytes", std::mem::size_of::<ast::BinOp>());
    println!("Dec:\t\t{} bytes", std::mem::size_of::<ast::Dec>());
    println!("DecKind:\t{} bytes", std::mem::size_of::<ast::DecKind>());
    println!("TypeDec:\t{} bytes", std::mem::size_of::<ast::TypeDec>());
    println!(
        "FunctionDec:\t{} bytes",
        std::mem::size_of::<ast::FunctionDec>()
    );
    println!("Ident:\t\t{} bytes", std::mem::size_of::<ast::Ident>());
    println!("Field:\t\t{} bytes", std::mem::size_of::<ast::Field>());
    println!("TyField:\t{} bytes", std::mem::size_of::<ast::TyField>());
    println!("Type:\t\t{} bytes", std::mem::size_of::<ast::Type>());
    println!("TypeKind:\t{} bytes", std::mem::size_of::<ast::TypeKind>());
    println!("ExpTy:\t\t{} bytes", std::mem::size_of::<ExpTy>());
    println!("RType:\t\t{} bytes", std::mem::size_of::<types::RType>());
    println!("Type:\t\t{} bytes", std::mem::size_of::<types::Type>());
}
