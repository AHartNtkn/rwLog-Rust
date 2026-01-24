//! Repl - shared CLI/notebook command processor.
//!
//! Supports:
//! - `rel name { ... }` definitions
//! - `load <file>` to load definitions
//! - `<query>` to run a query
//! - `list`, `help`, `quit`/`exit`

use crate::chr::{ChrState, NoTheory};
use crate::engine::Engine;
use crate::parser::{ChrConstraintBuilder, Parser};
use crate::rel::Rel;
use crate::work::Env;
use std::collections::HashMap;

type ReplConstraint = ChrState<NoTheory>;

/// REPL state.
pub struct Repl {
    parser: Parser<ChrConstraintBuilder>,
    /// Named relation definitions.
    definitions: HashMap<String, Rel<ReplConstraint>>,
    active_engine: Option<Engine<ReplConstraint>>,
    active_answer_count: usize,
}

impl Repl {
    pub fn new() -> Self {
        Self {
            parser: Parser::with_chr(),
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
            let count: usize = rest
                .trim()
                .parse()
                .map_err(|_| "Invalid count for 'more'. Usage: more <n>".to_string())?;
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

        // Try to parse as a relation definition
        if line.starts_with("theory ") {
            self.reset_active_query();
            return self.define_theory(line);
        }

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
        let statements = split_statements(trimmed)
            .map_err(|_| "Unterminated block definition in cell".to_string())?;

        for statement in statements {
            if let Some(output) = self.process_input(statement.trim())? {
                outputs.push(output);
            }
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
  list           List defined relations
  next           Show the next answer from the active query
  more <n>       Show the next N answers from the active query
  reset          Clear the active query
  help           Show this help
  quit/exit      Exit the REPL

Syntax:
  theory name { body }  Define a theory (CHR constraints)
  rel name { body }     Define a relation
  lhs -> rhs            Rewrite rule
  a | b                 Disjunction (or)
  a ; b                 Sequence (composition)
  a & b                 Conjunction (and/intersection)
  [...]                 Grouping
  $var                  Variable
  (f x y)               Compound term
  <expr>                Run a query (e.g., add ; @(s z))
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

    fn apply_theory(&mut self, input: &str, source: &str) -> Result<(String, bool), String> {
        let summary = self
            .parser
            .parse_theory_def(input)
            .map_err(|e| format!("Parse error in '{}': {}", source, e))?;
        let cleared = !self.definitions.is_empty();
        if cleared {
            self.definitions.clear();
        }
        Ok((summary.name, cleared))
    }

    fn define_theory(&mut self, input: &str) -> Result<Option<String>, String> {
        let (name, cleared) = self.apply_theory(input, "<input>")?;
        let mut message = format!("Defined theory '{}'", name);
        if cleared {
            message.push_str(" (cleared existing relations)");
        }
        Ok(Some(message))
    }

    fn load_file(&mut self, path: &str) -> Result<Option<String>, String> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| format!("Failed to read file '{}': {}", path, e))?;

        let mut count = 0;
        let mut theory_count = 0;
        let statements =
            split_statements(&content).map_err(|err| format!("{} in '{}'", err, path))?;

        for statement in statements {
            let line = statement.trim();
            if line.starts_with("theory ") {
                self.apply_theory(line, path)?;
                theory_count += 1;
                continue;
            }
            if line.starts_with("rel ") {
                match self.parser.parse_rel_def(line) {
                    Ok((name, rel)) => {
                        self.definitions.insert(name, rel);
                        count += 1;
                    }
                    Err(e) => {
                        return Err(format!("Parse error in '{}': {}", path, e));
                    }
                }
            }
        }

        let mut parts = Vec::new();
        if theory_count > 0 {
            parts.push(format!("Loaded {} theory block(s)", theory_count));
        }
        parts.push(format!("Loaded {} relation(s)", count));
        Ok(Some(format!("{} from '{}'", parts.join(", "), path)))
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
        let engine: Engine<ReplConstraint> = Engine::new_with_env(rel, terms, env);
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

    fn build_env(&self) -> Env<ReplConstraint> {
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

/// Split input into separate statements, handling braces for multi-line blocks.
pub fn split_statements(input: &str) -> Result<Vec<String>, String> {
    let mut outputs = Vec::new();
    let mut current = String::new();
    let mut brace_depth: i32 = 0;

    for raw_line in input.lines() {
        let line = raw_line.trim();
        if line.is_empty() {
            continue;
        }

        let line = match line.split_once('#') {
            Some((before, _)) => before.trim(),
            None => line,
        };
        if line.is_empty() {
            continue;
        }

        if !current.is_empty() {
            current.push('\n');
        }
        current.push_str(line);

        brace_depth += line.chars().filter(|&ch| ch == '{').count() as i32;
        brace_depth -= line.chars().filter(|&ch| ch == '}').count() as i32;

        if brace_depth == 0 {
            outputs.push(current.trim().to_string());
            current.clear();
        }
    }

    if brace_depth != 0 {
        return Err("Unterminated block definition".to_string());
    }

    if !current.trim().is_empty() {
        outputs.push(current.trim().to_string());
    }

    Ok(outputs)
}


#[cfg(test)]
mod tests;
