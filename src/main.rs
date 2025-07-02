use general::ast::Type;
use lexer::lexer::Lexer;
use parser::parser::Parser;

mod general;
mod lexer;
mod parser;
mod transpile;
mod utils;

use std::collections::HashMap;
use std::env;
use std::fs;
use std::io;
use std::io::Write;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use crate::transpile::transpile::Transpiler;
use general::ast::Expr;

use std::fs::write;

pub type SymbolTable = HashMap<String, Type>;

#[allow(dead_code)]
fn bench(input_file_name: &str, now: Instant, using_windows: bool) {
    let elapsed = now.elapsed();
    if !using_windows {
        println!(
            "{}",
            &format!(
                "\n\x1b[1;96mElapsed '{}' \x1b[1;93min: \x1b[0;96m{:.2?}\x1b[0m\n",
                input_file_name, elapsed
            )
        );
    } else {
        println!(
            "{}",
            &format!("\nElapsed '{}' in: {:.2?}\n", input_file_name, elapsed)
        );
    }
}

fn main() {
    // Fallback for not using ANSI
    let mut using_windows = false;
    let mut is_benching = false;
    let mut release = false;
    let mut preserve_output = false;
    let mut lexer = Lexer::new();
    let mut parser = Parser::new();

    if cfg!(windows) {
        using_windows = true;
    } else if cfg!(unix) {
        using_windows = false;
    }

    // Get the file path from the first command line argument
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: <file_path> --args");
        return;
    }
    let file_path = &args[1];

    let path = Path::new(file_path);

    let mut file_name = if let Some(name) = path.file_stem() {
        name.to_string_lossy().to_string()
    } else {
        panic!("Pre-transpile arg error: Could not extract file name from path");
    };
    let now = Instant::now();
    if args.len() >= 2 {
        for (i, arg) in args.clone().iter().enumerate() {
            if arg == "--bench" || arg == "--b" || arg == "--B" {
                is_benching = true;
            }
            if arg == "--preserve" || arg == "--p" || arg == "--P" {
                preserve_output = true;
            }
            if arg == "--r" || arg == "--R" {
                release = true;
            }
            if arg == "--name" || arg == "--n" || arg == "--N" {
                if i + 1 >= args.len() {
                    panic!("Pre-transpile arg error: Missing file name in --name")
                } else {
                    #[allow(clippy::collapsible_else_if)]
                    if args[i + 1].starts_with("-") {
                        panic!(
                            "Pre-transpile arg error: File name for --name cannot be prefixed with '-'"
                        )
                    } else {
                        file_name = args[i + 1].to_string();
                    }
                }
            }
        }
    }
    // Read the whole file into a string
    let file_contents = fs::read_to_string(file_path).expect("Failed to read the file");

    lexer.tokenize(&file_contents);
    parser.first_pass(&lexer);
    //parser.type_check();
    let mut found_main = false;
    for func in parser.functions.clone().into_iter() {
        if func.0 == "main" {
            if func.1.return_type != Type::Null {
                panic!("'main()' must return null")
            }
            if !func.1.params.is_empty() {
                panic!("'main()' must have 0 args")
            }
            found_main = true;
        }
    }
    if !found_main {
        panic!("'main()' not found")
    }

    let mut final_code = String::new();

    let mut transpiler = Transpiler::new();

    transpiler.load_extern_funcs(parser.extern_funcs.clone());

    final_code = format!("{}{}", final_code, transpiler.transpiled_code);

    for func in parser.functions.clone().into_iter() {
        let mut symbols = SymbolTable::new();

        let f = Expr::FunctionDef {
            name: func.0.to_string(),
            params: func.1.params,
            body: Box::new(func.1.body.clone()),
            return_type: func.1.return_type,
        };
        final_code = format!(
            "{}{}",
            final_code,
            transpiler.transpile_expr(&f, false, &mut symbols)
        );
    }

    if !using_windows {
        println!("\n\x1b[1;96mBubbleTea brewed successfully! Transpiling to Rust!\x1b[0m\n");
    } else {
        println!("\nBubbleTea brewed successfully! Transpiling to Rust!\n");
    }

    let _ = write("output.rs", final_code);

    let mut failed = false;
    if !release {
        let status = Command::new("rustc")
            .arg("output.rs")
            .arg("-o")
            .arg(file_name.clone())
            .status()
            .expect("failed to run rustc");
        if !status.success() {
            failed = true;
        };
    } else {
        let _ = Command::new("rustc")
            .arg("output.rs")
            .arg("-o")
            .arg(file_name.clone())
            .arg("-O")
            .status();
    }

    if failed {
        if !using_windows {
            println!("\n\x1b[1;91mCompilation failed.");
            println!("\x1b[0;91mrustc has failed to compile the transpile.\x1b[0m\n");
            return;
        } else {
            println!("\nCompilation failed.");
            println!("rustc has failed to compile the transpile.\n");
            return;
        }
    }

    if !using_windows {
        println!(
            "\n\x1b[1;96mBinary was output as \x1b[1;92m{}\x1b[0m\n",
            file_name
        );
    } else {
        println!("\nBinary output as {}\n", file_name);
    }

    if !preserve_output {
        let _ = std::fs::remove_file("./output.rs");
    }
    let _ = io::stdout().write_all(b"\n");
    let _ = io::stdout().flush();
    if is_benching {
        bench(&args[1], now, using_windows);
    }
}
