//! rwlog CLI - Relational Programming via Term Rewriting
//!
//! Commands:
//! - `load <file>` - Load relation definitions from a file
//! - `<query>` - Run a query
//! - `list` - List defined relations
//! - `help` - Show help
//! - `quit` or `exit` - Exit the REPL
//! - `kernel install` - Install Jupyter kernel spec
//! - `kernel --connection-file <path>` - Run Jupyter kernel

use rwlog::jupyter::{default_kernel_dir, install_kernel_spec};
use rwlog::repl::Repl;
use std::io::{self, BufRead, Write};
use std::path::PathBuf;

#[cfg(feature = "jupyter")]
use rwlog::jupyter::run_kernel;

fn main() {
    let mut args = std::env::args().skip(1);
    match args.next().as_deref() {
        None => run_repl(),
        Some("help") | Some("--help") | Some("-h") => {
            print_help();
        }
        Some("kernel") => handle_kernel(args.collect()),
        Some(other) => {
            eprintln!("Unknown subcommand: {}", other);
            print_help();
        }
    }
}

fn print_help() {
    println!("rwlog - Relational Programming via Term Rewriting\n");
    println!("Usage:");
    println!("  rwlog                  Start interactive REPL");
    println!("  rwlog kernel install   Install Jupyter kernel spec");
    println!("  rwlog kernel --connection-file <path>  Run Jupyter kernel");
}

fn run_repl() {
    let mut repl = Repl::new();

    println!("rwlog - Relational Programming via Term Rewriting");
    println!("Type 'help' for usage, 'quit' to exit.\n");

    let stdin = io::stdin();
    let mut stdout = io::stdout();

    loop {
        print!("> ");
        stdout.flush().unwrap();

        let mut line = String::new();
        match stdin.lock().read_line(&mut line) {
            Ok(0) => {
                // EOF
                println!("\nGoodbye!");
                break;
            }
            Ok(_) => match repl.process_input(&line) {
                Ok(Some(output)) => println!("{}", output),
                Ok(None) => {}
                Err(e) if e == "quit" => {
                    println!("Goodbye!");
                    break;
                }
                Err(e) => eprintln!("Error: {}", e),
            },
            Err(e) => {
                eprintln!("Error reading input: {}", e);
                break;
            }
        }
    }
}

fn handle_kernel(args: Vec<String>) {
    let mut iter = args.into_iter();
    match iter.next().as_deref() {
        Some("install") => handle_kernel_install(iter.collect()),
        other => handle_kernel_run(other, iter.collect()),
    }
}

fn handle_kernel_install(args: Vec<String>) {
    let mut name = "rwlog".to_string();
    let mut dir: Option<PathBuf> = None;
    let mut iter = args.into_iter();

    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--name" => {
                if let Some(val) = iter.next() {
                    name = val;
                }
            }
            "--dir" => {
                if let Some(val) = iter.next() {
                    dir = Some(PathBuf::from(val));
                }
            }
            "--help" | "-h" => {
                println!("rwlog kernel install [--name <name>] [--dir <dir>]");
                return;
            }
            other => {
                eprintln!("Unknown install option: {}", other);
                return;
            }
        }
    }

    let dir = match dir {
        Some(d) => d,
        None => match default_kernel_dir() {
            Ok(d) => d,
            Err(err) => {
                eprintln!("Failed to resolve kernel dir: {}", err);
                return;
            }
        },
    };
    let argv0 = match std::env::current_exe() {
        Ok(path) => path.to_string_lossy().to_string(),
        Err(err) => {
            eprintln!("Failed to resolve executable path: {}", err);
            return;
        }
    };

    match install_kernel_spec(&dir, &name, &argv0) {
        Ok(path) => println!("Installed kernel spec at {}", path.display()),
        Err(err) => eprintln!("Kernel install failed: {}", err),
    }
}

fn handle_kernel_run(first: Option<&str>, rest: Vec<String>) {
    let mut connection_file: Option<String> = None;
    let mut args = Vec::new();
    if let Some(arg) = first {
        args.push(arg.to_string());
    }
    args.extend(rest);

    let mut iter = args.into_iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--connection-file" | "-f" => {
                connection_file = iter.next();
            }
            "--help" | "-h" => {
                println!("rwlog kernel --connection-file <path>");
                return;
            }
            other => {
                eprintln!("Unknown kernel option: {}", other);
                return;
            }
        }
    }

    let connection_file = match connection_file {
        Some(path) => PathBuf::from(path),
        None => {
            eprintln!("Missing --connection-file");
            return;
        }
    };

    #[cfg(feature = "jupyter")]
    {
        if let Err(err) = run_kernel(&connection_file) {
            eprintln!("Kernel error: {}", err);
        }
    }

    #[cfg(not(feature = "jupyter"))]
    {
        eprintln!("Kernel support requires building with --features jupyter");
        let _ = connection_file;
    }
}


#[cfg(test)]
#[path = "rwlog/tests.rs"]
mod tests;
