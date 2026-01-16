//! Repl - shared CLI/notebook command processor.
//!
//! Supports:
//! - `rel name { ... }` definitions
//! - `load <file>` to load definitions
//! - `?- <query>` to run a query
//! - `list`, `help`, `quit`/`exit`

use crate::engine::Engine;
use crate::parser::Parser;
use crate::rel::Rel;
use crate::work::Env;
use std::collections::HashMap;

/// REPL state.
pub struct Repl {
    parser: Parser,
    /// Named relation definitions.
    definitions: HashMap<String, Rel<()>>,
    active_engine: Option<Engine<()>>,
    active_answer_count: usize,
}

impl Repl {
    pub fn new() -> Self {
        Self {
            parser: Parser::new(),
            definitions: HashMap::new(),
            active_engine: None,
            active_answer_count: 0,
        }
    }

    /// Process a single command line.
    pub fn process_input(&mut self, input: &str) -> Result<Option<String>, String> {
        let line = input.trim();

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

        if line == "next" {
            return self.next_answers(1);
        }

        if let Some(rest) = line.strip_prefix("more ") {
            let count: usize = rest.trim().parse().map_err(|_| {
                "Invalid count for 'more'. Usage: more <n>".to_string()
            })?;
            if count == 0 {
                return Err("Count for 'more' must be > 0".to_string());
            }
            return self.next_answers(count);
        }

        if line == "reset" {
            self.reset_active_query();
            return Ok(Some("Query reset.".to_string()));
        }

        if let Some(path) = line.strip_prefix("load ") {
            self.reset_active_query();
            return self.load_file(path.trim());
        }

        if let Some(query) = line.strip_prefix("?- ") {
            self.reset_active_query();
            return self.run_query(query.trim());
        }

        // Try to parse as a relation definition
        if line.starts_with("rel ") {
            self.reset_active_query();
            return self.define_relation(line);
        }

        self.reset_active_query();
        self.run_query(line)
    }

    /// Process a notebook cell.
    ///
    /// If the cell starts with `rel`, treat it as a single definition.
    /// Otherwise, process non-empty lines individually.
    pub fn process_cell(&mut self, input: &str) -> Result<Option<String>, String> {
        let trimmed = input.trim();
        if trimmed.is_empty() {
            return Ok(None);
        }

        // Single-line input: delegate directly
        if !trimmed.contains('\n') {
            // process_input handles comment lines
            return self.process_input(trimmed);
        }

        let mut outputs = Vec::new();
        let mut current = String::new();
        let mut brace_depth: i32 = 0;

        for raw_line in trimmed.lines() {
            let line = raw_line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            if !current.is_empty() {
                current.push('\n');
            }
            current.push_str(line);

            brace_depth += line.chars().filter(|&ch| ch == '{').count() as i32;
            brace_depth -= line.chars().filter(|&ch| ch == '}').count() as i32;

            if brace_depth == 0 {
                if let Some(output) = self.process_input(current.trim())? {
                    outputs.push(output);
                }
                current.clear();
            }
        }

        if brace_depth != 0 {
            return Err("Unterminated relation definition in cell".to_string());
        }

        if outputs.is_empty() {
            Ok(None)
        } else {
            Ok(Some(outputs.join("\n")))
        }
    }

    fn help_text(&self) -> String {
        r#"rwlog - Relational Programming via Term Rewriting

Commands:
  load <file>    Load relation definitions from a file
  ?- <query>     Run a query (e.g., ?- add ; (cons z z))
  list           List defined relations
  next           Show the next answer from the active query
  more <n>       Show the next N answers from the active query
  reset          Clear the active query
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
  <expr>                Bare query (same as ?- <expr>)
"#
        .to_string()
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

    fn define_relation(&mut self, input: &str) -> Result<Option<String>, String> {
        match self.parser.parse_rel_def(input) {
            Ok((name, rel)) => {
                self.definitions.insert(name.clone(), rel);
                Ok(Some(format!("Defined relation '{}'", name)))
            }
            Err(e) => Err(format!("Parse error: {}", e)),
        }
    }

    fn run_query(&mut self, query: &str) -> Result<Option<String>, String> {
        let rel = self
            .parser
            .parse_rel_body(query)
            .map_err(|e| format!("Parse error: {}", e))?;

        let env = self.build_env();

        // Share the parser's TermStore with the engine to keep TermIds valid.
        let terms = self.parser.take_terms();
        let engine: Engine<()> = Engine::new_with_env(rel, terms, env);
        self.active_engine = Some(engine);
        self.active_answer_count = 0;
        self.next_answers(1)
    }

    fn next_answers(&mut self, count: usize) -> Result<Option<String>, String> {
        let engine = match self.active_engine.as_mut() {
            Some(engine) => engine,
            None => return Ok(Some("No active query. Run a query first.".to_string())),
        };

        let mut output = String::new();
        let mut produced = 0;

        while produced < count {
            match engine.next() {
                Some(nf) => {
                    self.active_answer_count += 1;
                    let rendered = engine.format_nf(&nf, self.parser.symbols())?;
                    output.push_str(&format!("{}. {}\n", self.active_answer_count, rendered));
                    produced += 1;
                }
                None => {
                    self.finish_active_query();
                    break;
                }
            }
        }

        if output.is_empty() {
            Ok(Some("No more answers.".to_string()))
        } else {
            output.push_str("Type 'next' for more answers.\n");
            Ok(Some(output))
        }
    }

    fn reset_active_query(&mut self) {
        self.finish_active_query();
    }

    fn finish_active_query(&mut self) {
        if let Some(engine) = self.active_engine.take() {
            let terms = engine.into_terms();
            self.parser.restore_terms(terms);
        }
        self.active_answer_count = 0;
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

impl Default for Repl {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::Repl;

    #[test]
    fn repl_process_cell_handles_multiple_lines() {
        let mut repl = Repl::new();
        let output = repl
            .process_cell("rel f { a -> b }\n?- f")
            .expect("process cell");
        assert!(
            output.unwrap_or_default().contains("1."),
            "Expected output from query line"
        );
    }

    #[test]
    fn repl_process_cell_handles_comment_then_query() {
        let mut repl = Repl::new();
        repl.process_input("rel f { a -> b }")
            .expect("define f");
        // Simulates a notebook cell with a comment header followed by a query
        let output = repl
            .process_cell("# This is a comment\n?- f")
            .expect("process cell with leading comment");
        assert!(
            output.unwrap_or_default().contains("1."),
            "Expected output from query after comment line"
        );
    }

    #[test]
    fn repl_query_renders_rule_syntax() {
        let mut repl = Repl::new();
        repl.process_input("rel f { a -> b }")
            .expect("define f");
        let output = repl
            .process_input("?- f")
            .expect("run query")
            .unwrap_or_default();
        assert!(
            output.contains("a -> b"),
            "Expected rule syntax in output, got: {}",
            output
        );
    }

    #[test]
    fn repl_bare_query_runs_as_query() {
        let mut repl = Repl::new();
        let output = repl
            .process_input("@z")
            .expect("process bare query")
            .unwrap_or_default();
        assert!(
            output.contains("1."),
            "Expected answer numbering for bare query, got: {}",
            output
        );
    }

    #[test]
    fn repl_next_advances_through_answers() {
        let mut repl = Repl::new();
        repl.process_input("rel f { a -> b | a -> c }")
            .expect("define f")
            .expect("define output");

        let first = repl
            .process_input("?- f")
            .expect("run query")
            .unwrap_or_default();
        assert!(first.contains("1."), "Expected first answer");

        let second = repl
            .process_input("next")
            .expect("next answer")
            .unwrap_or_default();
        assert!(second.contains("2."), "Expected second answer");

        let done = repl
            .process_input("next")
            .expect("next after exhausted")
            .unwrap_or_default();
        assert!(
            done.contains("No more answers"),
            "Expected exhaustion notice"
        );
    }
}
