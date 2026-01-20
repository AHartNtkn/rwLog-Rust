//! Repl - shared CLI/notebook command processor.
//!
//! Supports:
//! - `rel name { ... }` definitions
//! - `load <file>` to load definitions
//! - `?- <query>` to run a query
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

        if let Some(query) = line.strip_prefix("?- ") {
            self.reset_active_query();
            return self.run_query(query.trim());
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
  ?- <query>     Run a query (e.g., ?- add ; (cons z z))
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
mod tests {
    use super::Repl;
    use serde_json::Value;
    use std::fs;
    use std::path::Path;

    fn load_notebook_code_cells(path: &Path) -> Result<Vec<String>, String> {
        let content = fs::read_to_string(path)
            .map_err(|e| format!("Failed to read notebook '{}': {}", path.display(), e))?;
        let json: Value = serde_json::from_str(&content)
            .map_err(|e| format!("Failed to parse notebook '{}': {}", path.display(), e))?;
        let cells = json
            .get("cells")
            .and_then(|v| v.as_array())
            .ok_or_else(|| format!("Notebook '{}' missing cells array", path.display()))?;
        let mut out = Vec::new();
        for cell in cells {
            let cell_type = cell
                .get("cell_type")
                .and_then(|v| v.as_str())
                .unwrap_or_default();
            if cell_type != "code" {
                continue;
            }
            let source = cell
                .get("source")
                .ok_or_else(|| format!("Notebook '{}' missing cell source", path.display()))?;
            let src = if let Some(lines) = source.as_array() {
                let mut merged = String::new();
                for line in lines {
                    if let Some(s) = line.as_str() {
                        merged.push_str(s);
                    }
                }
                merged
            } else if let Some(s) = source.as_str() {
                s.to_string()
            } else {
                return Err(format!(
                    "Notebook '{}' cell source has unexpected type",
                    path.display()
                ));
            };
            out.push(src);
        }
        Ok(out)
    }

    fn adjust_load_paths(cell: &str, base_dir: &Path) -> String {
        let mut out_lines = Vec::new();
        for line in cell.lines() {
            let trimmed = line.trim();
            if let Some(rest) = trimmed.strip_prefix("load ") {
                let path_str = rest.trim();
                let path = Path::new(path_str);
                let adjusted = if path.exists() {
                    None
                } else {
                    let candidate = base_dir.join(path_str);
                    if candidate.exists() {
                        Some(candidate)
                    } else {
                        None
                    }
                };
                if let Some(path) = adjusted {
                    let leading: String = line.chars().take_while(|c| c.is_whitespace()).collect();
                    out_lines.push(format!("{}load {}", leading, path.display()));
                    continue;
                }
            }
            out_lines.push(line.to_string());
        }
        out_lines.join("\n")
    }

    fn cell_has_query(cell: &str) -> bool {
        let mut brace_depth: i32 = 0;
        for line in cell.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            if brace_depth > 0 {
                brace_depth += trimmed.chars().filter(|&ch| ch == '{').count() as i32;
                brace_depth -= trimmed.chars().filter(|&ch| ch == '}').count() as i32;
                continue;
            }
            if trimmed.starts_with("rel ") || trimmed.starts_with("theory ") {
                brace_depth += trimmed.chars().filter(|&ch| ch == '{').count() as i32;
                brace_depth -= trimmed.chars().filter(|&ch| ch == '}').count() as i32;
                continue;
            }
            if trimmed.starts_with("load ")
                || trimmed == "next"
                || trimmed == "reset"
                || trimmed == "list"
                || trimmed == "help"
                || trimmed.starts_with("more ")
            {
                continue;
            }
            return true;
        }
        false
    }

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
        repl.process_input("rel f { a -> b }").expect("define f");
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
        repl.process_input("rel f { a -> b }").expect("define f");
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

    #[test]
    fn theory_notebook_demo_cells_run() {
        let mut repl = Repl::new();
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let notebook = root.join("examples/theory_demos.ipynb");
        let base_dir = notebook
            .parent()
            .expect("notebook should have parent directory");
        let cells = load_notebook_code_cells(&notebook).expect("load notebook cells");

        for (idx, cell) in cells.iter().enumerate() {
            let adjusted = adjust_load_paths(cell, base_dir);
            let output = repl
                .process_cell(&adjusted)
                .unwrap_or_else(|e| panic!("cell {} failed: {}", idx, e));
            if cell_has_query(&adjusted) {
                let out = output.unwrap_or_default();
                assert!(
                    out.contains("1."),
                    "Expected an answer in cell {} output: {}",
                    idx,
                    out
                );
            } else if adjusted.trim_start().starts_with("load ") {
                let out = output.unwrap_or_default();
                assert!(
                    out.contains("Loaded"),
                    "Expected load output in cell {}: {}",
                    idx,
                    out
                );
            }
        }
    }
}
