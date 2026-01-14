//! Debug test for backward query bug
use rwlog::trace::init_subscriber;
use rwlog::cli::repl::Repl;

fn main() {
    // Initialize tracing subscriber
    init_subscriber();
    
    let mut repl: Repl<()> = Repl::new();
    
    // Load addition
    eprintln!("=== Loading addition.txt ===");
    repl.process_line("load examples/addition.txt").unwrap();
    
    // Run the backward query
    eprintln!("\n=== Running: ?- add ; z ===");
    let result = repl.process_line("?- add ; z").unwrap();
    
    eprintln!("\n=== RESULT ===");
    eprintln!("{:?}", result);
}
