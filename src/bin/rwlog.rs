//! rwlog CLI - Relational Programming via Term Rewriting
//!
//! Commands:
//! - `load <file>` - Load relation definitions from a file
//! - `?- <query>` - Run a query
//! - `list` - List defined relations
//! - `help` - Show help
//! - `quit` or `exit` - Exit the REPL

use rwlog::engine::Engine;
use rwlog::parser::Parser;
use rwlog::rel::Rel;
use rwlog::work::Env;
use std::collections::HashMap;
use std::io::{self, BufRead, Write};

/// REPL state.
struct Repl {
    parser: Parser,
    /// Named relation definitions.
    definitions: HashMap<String, Rel<()>>,
}

impl Repl {
    fn new() -> Self {
        Self {
            parser: Parser::new(),
            definitions: HashMap::new(),
        }
    }

    /// Process a single line of input.
    fn process_line(&mut self, line: &str) -> Result<Option<String>, String> {
        let line = line.trim();

        if line.is_empty() || line.starts_with('#') {
            return Ok(None);
        }

        if line == "help" {
            return Ok(Some(self.help_text()));
        }

        if line == "quit" || line == "exit" {
            return Err("quit".to_string());
        }

        if line == "list" {
            return Ok(Some(self.list_relations()));
        }

        if let Some(path) = line.strip_prefix("load ") {
            return self.load_file(path.trim());
        }

        if let Some(query) = line.strip_prefix("?- ") {
            return self.run_query(query.trim());
        }

        // Try to parse as a relation definition
        if line.starts_with("rel ") {
            return self.define_relation(line);
        }

        Err(format!("Unknown command: {}. Type 'help' for usage.", line))
    }

    fn help_text(&self) -> String {
        r#"rwlog - Relational Programming via Term Rewriting

Commands:
  load <file>    Load relation definitions from a file
  ?- <query>     Run a query (e.g., ?- add ; (cons z z))
  list           List defined relations
  help           Show this help
  quit/exit      Exit the REPL

Syntax:
  rel name { body }     Define a relation
  lhs -> rhs            Rewrite rule
  a | b                 Disjunction (or)
  a ; b                 Sequence (composition)
  a & b                 Conjunction (and/intersection)
  [...]                 Grouping
  $var                  Variable
  (f x y)               Compound term
"#.to_string()
    }

    fn list_relations(&self) -> String {
        if self.definitions.is_empty() {
            "No relations defined.".to_string()
        } else {
            let names: Vec<&str> = self.definitions.keys().map(|s| s.as_str()).collect();
            format!("Defined relations: {}", names.join(", "))
        }
    }

    fn load_file(&mut self, path: &str) -> Result<Option<String>, String> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| format!("Failed to read file '{}': {}", path, e))?;

        let mut count = 0;
        let mut pos = 0;

        // Strip comments and find relation definitions
        while pos < content.len() {
            // Skip whitespace and comments
            while pos < content.len() {
                let ch = content.chars().nth(pos).unwrap();
                if ch.is_whitespace() {
                    pos += 1;
                } else if ch == '#' {
                    // Skip to end of line
                    while pos < content.len() && content.chars().nth(pos).unwrap() != '\n' {
                        pos += 1;
                    }
                } else {
                    break;
                }
            }

            if pos >= content.len() {
                break;
            }

            // Check for 'rel' keyword
            if content[pos..].starts_with("rel ") {
                // Find the matching closing brace
                let start = pos;
                let mut brace_depth = 0;
                let mut found_open = false;

                while pos < content.len() {
                    let ch = content.chars().nth(pos).unwrap();
                    if ch == '{' {
                        found_open = true;
                        brace_depth += 1;
                    } else if ch == '}' {
                        brace_depth -= 1;
                        if brace_depth == 0 && found_open {
                            pos += 1;
                            break;
                        }
                    }
                    pos += 1;
                }

                let rel_text = &content[start..pos];
                match self.parser.parse_rel_def(rel_text) {
                    Ok((name, rel)) => {
                        self.definitions.insert(name, rel);
                        count += 1;
                    }
                    Err(e) => {
                        return Err(format!("Parse error in '{}': {}", path, e));
                    }
                }
            } else {
                pos += 1;
            }
        }

        Ok(Some(format!("Loaded {} relation(s) from '{}'", count, path)))
    }

    fn define_relation(&mut self, line: &str) -> Result<Option<String>, String> {
        match self.parser.parse_rel_def(line) {
            Ok((name, rel)) => {
                self.definitions.insert(name.clone(), rel);
                Ok(Some(format!("Defined relation '{}'", name)))
            }
            Err(e) => Err(format!("Parse error: {}", e)),
        }
    }

    fn run_query(&mut self, query: &str) -> Result<Option<String>, String> {
        // Parse the query as a relation body
        let rel = self.parser.parse_rel_body(query)
            .map_err(|e| format!("Parse error: {}", e))?;

        let env = self.build_env();

        // Share the parser's TermStore with the engine to keep TermIds valid.
        let terms = self.parser.take_terms();
        let mut engine: Engine<()> = Engine::new_with_env(rel, terms, env);

        // Collect answers (with a limit to prevent infinite loops)
        let mut answers = Vec::new();
        let max_answers = 100;

        while let Some(nf) = engine.next() {
            answers.push(nf);
            if answers.len() >= max_answers {
                break;
            }
        }

        let terms = engine.into_terms();
        self.parser.restore_terms(terms);

        if answers.is_empty() {
            Ok(Some("No answers.".to_string()))
        } else {
            let mut output = String::new();
            for (i, nf) in answers.iter().enumerate() {
                output.push_str(&format!("{}. {:?}\n", i + 1, nf));
            }
            if answers.len() >= max_answers {
                output.push_str(&format!("... (showing first {} answers)\n", max_answers));
            }
            Ok(Some(output))
        }
    }

    fn build_env(&self) -> Env<()> {
        let mut env = Env::new();
        for rel in self.definitions.values() {
            if let Rel::Fix(id, body) = rel {
                env = env.bind(*id, body.clone());
            }
        }
        env
    }
}

fn main() {
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
            Ok(_) => {
                match repl.process_line(&line) {
                    Ok(Some(output)) => println!("{}", output),
                    Ok(None) => {}
                    Err(e) if e == "quit" => {
                        println!("Goodbye!");
                        break;
                    }
                    Err(e) => eprintln!("Error: {}", e),
                }
            }
            Err(e) => {
                eprintln!("Error reading input: {}", e);
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Repl;

    #[test]
    fn repl_query_composes_named_relations() {
        let mut repl = Repl::new();
        repl.process_line("rel f { a -> b }")
            .expect("define f")
            .expect("f output");
        repl.process_line("rel g { b -> c }")
            .expect("define g")
            .expect("g output");

        let output = repl
            .process_line("?- f ; g")
            .expect("query should run")
            .expect("query output");

        assert!(
            output.starts_with("1."),
            "Expected at least one answer, got: {}",
            output
        );
    }
}
