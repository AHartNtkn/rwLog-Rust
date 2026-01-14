//! rwlog CLI - Relational Programming via Term Rewriting
//!
//! A command-line interface for the rwlog logic programming system.

use std::io::{stdin, stdout, BufReader};

use rwlog::cli::Repl;

fn main() {
    // Create REPL with unit constraint (simplest mode)
    let mut repl: Repl<()> = Repl::new();

    // Run the REPL
    let mut input = BufReader::new(stdin().lock());
    let mut output = stdout().lock();

    if let Err(e) = repl.run(&mut input, &mut output) {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    }
}
