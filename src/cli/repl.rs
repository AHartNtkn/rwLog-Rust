//! REPL (Read-Eval-Print Loop) for interactive queries.

use std::collections::HashMap;
use std::io::{self, BufRead, Write};

use crate::api::Engine;
use crate::constraint::ConstraintOps;
use crate::goal::GoalId;
use crate::nf::NF;

use super::compiler::Compiler;
use super::file_parser::{FileParser, ParsedExpr, ParsedTerm};
use super::parse::{Command, ParseError, Parser};

/// The REPL state and configuration.
pub struct Repl<C: ConstraintOps + 'static> {
    /// The logic engine.
    engine: Engine<C>,
    /// Maximum steps per query.
    max_steps: usize,
    /// Whether to show verbose output.
    verbose: bool,
    /// The REPL prompt.
    prompt: String,
    /// Map from relation name to its compiled GoalId.
    rel_goals: HashMap<String, GoalId>,
}

impl<C: ConstraintOps + Default + Clone + 'static> Repl<C> {
    /// Create a new REPL with default settings.
    pub fn new() -> Self {
        Self {
            engine: Engine::new(),
            max_steps: 10000,
            verbose: false,
            prompt: "rwlog> ".to_string(),
            rel_goals: HashMap::new(),
        }
    }

    /// Set the maximum steps per query.
    pub fn with_max_steps(mut self, max_steps: usize) -> Self {
        self.max_steps = max_steps;
        self
    }

    /// Set verbose mode.
    pub fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Set the prompt.
    pub fn with_prompt(mut self, prompt: impl Into<String>) -> Self {
        self.prompt = prompt.into();
        self
    }

    /// Get a reference to the engine.
    pub fn engine(&self) -> &Engine<C> {
        &self.engine
    }

    /// Get a mutable reference to the engine.
    pub fn engine_mut(&mut self) -> &mut Engine<C> {
        &mut self.engine
    }

    /// Run the REPL with the given input and output streams.
    pub fn run<R: BufRead, W: Write>(
        &mut self,
        input: &mut R,
        output: &mut W,
    ) -> io::Result<()> {
        self.print_banner(output)?;

        loop {
            write!(output, "{}", self.prompt)?;
            output.flush()?;

            let mut line = String::new();
            let bytes_read = input.read_line(&mut line)?;

            if bytes_read == 0 {
                // EOF
                writeln!(output, "\nGoodbye!")?;
                break;
            }

            match self.process_line(&line) {
                Ok(ReplAction::Continue) => {}
                Ok(ReplAction::Quit) => {
                    writeln!(output, "Goodbye!")?;
                    break;
                }
                Ok(ReplAction::Print(msg)) => {
                    writeln!(output, "{}", msg)?;
                }
                Err(e) => {
                    writeln!(output, "Error: {}", e)?;
                }
            }
        }

        Ok(())
    }

    /// Process a single line of input.
    pub fn process_line(&mut self, line: &str) -> Result<ReplAction, ReplError> {
        let mut parser = Parser::new(line);
        let cmd = parser.parse().map_err(ReplError::Parse)?;

        match cmd {
            Command::Empty => Ok(ReplAction::Continue),
            Command::Quit => Ok(ReplAction::Quit),
            Command::Help => Ok(ReplAction::Print(Self::help_text())),
            Command::List => {
                let relations = self.list_relations();
                Ok(ReplAction::Print(relations))
            }
            Command::Query { goal } => {
                let result = self.handle_query(&goal)?;
                Ok(ReplAction::Print(result))
            }
            Command::Define { name, body } => {
                let result = self.handle_define(&name, &body)?;
                Ok(ReplAction::Print(result))
            }
            Command::Load { filename } => {
                let result = self.handle_load(&filename)?;
                Ok(ReplAction::Print(result))
            }
        }
    }

    fn print_banner<W: Write>(&self, output: &mut W) -> io::Result<()> {
        writeln!(output, "rwlog - Relational Programming via Term Rewriting")?;
        writeln!(output, "Type 'help' for available commands, 'quit' to exit.")?;
        writeln!(output)?;
        Ok(())
    }

    fn help_text() -> String {
        r#"Available commands:
  ?- <goal>          Query a goal
  def <name> = <body>  Define a relation
  load <filename>    Load definitions from a file
  list               List defined relations
  help               Show this help message
  quit               Exit the REPL

Examples:
  ?- parent(tom, X)
  def grandparent(X, Z) = parent(X, Y), parent(Y, Z)
  load "examples/family.rwl"
"#
        .to_string()
    }

    fn list_relations(&self) -> String {
        let mut result = String::from("Defined relations:\n");
        let goals = self.engine.goals();
        let mut found = false;

        // Iterate over relation IDs and get their names
        let mut rel_id = 0u32;
        while let Some(name) = goals.rel_name(rel_id) {
            result.push_str(&format!("  {}\n", name));
            found = true;
            rel_id += 1;
        }

        if !found {
            result.push_str("  (none defined yet)\n");
        }
        result
    }

    fn handle_query(&mut self, query_str: &str) -> Result<String, ReplError> {
        // Parse query as a relation expression
        let query_str = query_str.trim();
        if query_str.is_empty() {
            return Err(ReplError::Execution("Empty query".to_string()));
        }

        let mut parser = FileParser::new(query_str);
        let expr = parser
            .parse_expr()
            .map_err(|e| ReplError::Execution(format!("Parse error: {}", e)))?;

        // Compile expression to a Goal
        let goal_id = self.compile_query_expr(&expr)?;

        // Create arity-1 identity input: $x -> $x
        // This allows composition with arity-1 relations
        let v0 = self.engine.var(0);
        let identity_input = NF::factor(v0, v0, C::default(), self.engine.terms_mut());

        // Enumerate pairs in the relation
        let answers = self.engine.query(goal_id, identity_input, self.max_steps);

        if answers.is_empty() {
            Ok("No solutions.".to_string())
        } else {
            let mut result = String::new();
            for (i, answer) in answers.iter().enumerate() {
                if i > 0 {
                    result.push_str("\n");
                }
                // Format the answer as a full pair: lhs -> rhs
                let formatted = self.format_answer(&answer.nf);
                result.push_str(&formatted);
            }
            Ok(result)
        }
    }

    /// Compile a query expression to a GoalId.
    fn compile_query_expr(&mut self, expr: &ParsedExpr) -> Result<GoalId, ReplError> {
        use crate::goal::Goal;
        use smallvec::smallvec;

        match expr {
            ParsedExpr::Rule { lhs, rhs, .. } => {
                // Compile both terms
                let mut var_map = std::collections::HashMap::new();
                let lhs_id = self.parsed_term_to_id(lhs, &mut var_map);
                let rhs_id = self.parsed_term_to_id(rhs, &mut var_map);

                // Create NF via factoring
                let nf = NF::factor(lhs_id, rhs_id, C::default(), self.engine.terms_mut());
                let rule_id = self.engine.rules_mut().add(nf);
                Ok(self.engine.add_goal(Goal::Rule(rule_id)))
            }

            ParsedExpr::Call(name) => {
                // Look up as defined relation, or treat as nullary term
                if let Some(&goal_id) = self.rel_goals.get(name) {
                    Ok(goal_id)
                } else {
                    // Treat as a nullary term (atom) - identity relation on it
                    let sym = self.engine.intern(name);
                    let term_id = self.engine.app(sym, smallvec![]);
                    let nf = NF::factor(term_id, term_id, C::default(), self.engine.terms_mut());
                    let rule_id = self.engine.rules_mut().add(nf);
                    Ok(self.engine.add_goal(Goal::Rule(rule_id)))
                }
            }

            ParsedExpr::Seq(exprs) => {
                let goal_ids: Result<smallvec::SmallVec<[GoalId; 4]>, _> = exprs
                    .iter()
                    .map(|e| self.compile_query_expr(e))
                    .collect();
                Ok(self.engine.seq(goal_ids?))
            }

            ParsedExpr::Alt(exprs) => {
                let goal_ids: Result<smallvec::SmallVec<[GoalId; 2]>, _> = exprs
                    .iter()
                    .map(|e| self.compile_query_expr(e))
                    .collect();
                Ok(self.engine.alt(goal_ids?))
            }

            ParsedExpr::Both(exprs) => {
                let goal_ids: Result<smallvec::SmallVec<[GoalId; 4]>, _> = exprs
                    .iter()
                    .map(|e| self.compile_query_expr(e))
                    .collect();
                Ok(self.engine.both(goal_ids?))
            }

            ParsedExpr::Term(term) => {
                // A bare term is an identity relation: term -> term
                let mut var_map = std::collections::HashMap::new();
                let term_id = self.parsed_term_to_id(term, &mut var_map);
                let nf = NF::factor(term_id, term_id, C::default(), self.engine.terms_mut());
                let rule_id = self.engine.rules_mut().add(nf);
                Ok(self.engine.add_goal(Goal::Rule(rule_id)))
            }
        }
    }

    /// Convert a ParsedTerm to a TermId in the engine.
    fn parsed_term_to_id(
        &self,
        term: &ParsedTerm,
        var_map: &mut std::collections::HashMap<String, u32>,
    ) -> crate::term::TermId {
        match term {
            ParsedTerm::Var(name) => {
                let idx = if let Some(&idx) = var_map.get(name) {
                    idx
                } else {
                    let idx = var_map.len() as u32;
                    var_map.insert(name.clone(), idx);
                    idx
                };
                self.engine.var(idx)
            }
            ParsedTerm::Atom(name) => {
                let sym = self.engine.intern(name);
                self.engine.app(sym, smallvec::smallvec![])
            }
            ParsedTerm::App(name, args) => {
                let sym = self.engine.intern(name);
                let arg_ids: smallvec::SmallVec<[crate::term::TermId; 4]> = args
                    .iter()
                    .map(|a| self.parsed_term_to_id(a, var_map))
                    .collect();
                self.engine.app(sym, arg_ids)
            }
        }
    }

    /// Format an answer NF as a full pair: lhs -> rhs
    fn format_answer(&self, nf: &NF<C>) -> String {
        let lhs = if nf.match_pats.is_empty() {
            "()".to_string()
        } else {
            self.format_term(nf.match_pats[0])
        };

        let rhs = if nf.build_pats.is_empty() {
            "()".to_string()
        } else {
            self.format_term(nf.build_pats[0])
        };

        format!("{} -> {}", lhs, rhs)
    }

    /// Format a term as an S-expression string.
    fn format_term(&self, term_id: crate::term::TermId) -> String {
        use crate::term::Term;

        let term = self.engine.terms().resolve(term_id);
        match term {
            Some(Term::Var(idx)) => format!("${}", idx),
            Some(Term::App(func, children)) => {
                let name = self
                    .engine
                    .symbols()
                    .resolve(func)
                    .unwrap_or("<unknown>");
                if children.is_empty() {
                    name.to_string()
                } else {
                    let args: Vec<String> = children
                        .iter()
                        .map(|&c| self.format_term(c))
                        .collect();
                    format!("({} {})", name, args.join(" "))
                }
            }
            None => "<invalid>".to_string(),
        }
    }

    fn handle_define(&mut self, name: &str, body: &str) -> Result<String, ReplError> {
        // For now, just acknowledge the definition
        Ok(format!("Defined: {} = {}", name, body))
    }

    fn handle_load(&mut self, filename: &str) -> Result<String, ReplError> {
        // Read the file
        let content = std::fs::read_to_string(filename).map_err(ReplError::Io)?;

        // Parse the file
        let mut parser = FileParser::new(&content);
        let parsed = parser
            .parse_file()
            .map_err(|e| ReplError::Execution(e.to_string()))?;

        // Compile the file
        let mut compiler = Compiler::new(&mut self.engine);
        let loaded = compiler
            .compile_file(parsed)
            .map_err(|e| ReplError::Execution(e.to_string()))?;

        // Store the relation goal IDs for query execution
        for (name, goal_id) in &loaded {
            self.rel_goals.insert(name.clone(), *goal_id);
        }

        let names: Vec<&str> = loaded.keys().map(|s| s.as_str()).collect();
        Ok(format!(
            "Loaded {} relation(s): {}",
            loaded.len(),
            names.join(", ")
        ))
    }
}

impl<C: ConstraintOps + Default + Clone + 'static> Default for Repl<C> {
    fn default() -> Self {
        Self::new()
    }
}

/// Actions the REPL can take after processing a command.
#[derive(Debug, Clone, PartialEq)]
pub enum ReplAction {
    /// Continue to the next prompt.
    Continue,
    /// Quit the REPL.
    Quit,
    /// Print a message and continue.
    Print(String),
}

/// Errors that can occur in the REPL.
#[derive(Debug)]
pub enum ReplError {
    /// Parse error.
    Parse(ParseError),
    /// IO error.
    Io(io::Error),
    /// Execution error.
    Execution(String),
}

impl std::fmt::Display for ReplError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReplError::Parse(e) => write!(f, "Parse error: {}", e),
            ReplError::Io(e) => write!(f, "IO error: {}", e),
            ReplError::Execution(e) => write!(f, "Execution error: {}", e),
        }
    }
}

impl std::error::Error for ReplError {}

impl From<ParseError> for ReplError {
    fn from(e: ParseError) -> Self {
        ReplError::Parse(e)
    }
}

impl From<io::Error> for ReplError {
    fn from(e: io::Error) -> Self {
        ReplError::Io(e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    // ========== REPL CREATION TESTS ==========

    #[test]
    fn repl_new() {
        let repl: Repl<()> = Repl::new();
        assert_eq!(repl.max_steps, 10000);
        assert!(!repl.verbose);
        assert_eq!(repl.prompt, "rwlog> ");
    }

    #[test]
    fn repl_with_max_steps() {
        let repl: Repl<()> = Repl::new().with_max_steps(1000);
        assert_eq!(repl.max_steps, 1000);
    }

    #[test]
    fn repl_with_verbose() {
        let repl: Repl<()> = Repl::new().with_verbose(true);
        assert!(repl.verbose);
    }

    #[test]
    fn repl_with_prompt() {
        let repl: Repl<()> = Repl::new().with_prompt("test> ");
        assert_eq!(repl.prompt, "test> ");
    }

    #[test]
    fn repl_default() {
        let repl: Repl<()> = Repl::default();
        assert_eq!(repl.max_steps, 10000);
    }

    // ========== PROCESS LINE TESTS ==========

    #[test]
    fn process_empty_line() {
        let mut repl: Repl<()> = Repl::new();
        let result = repl.process_line("").unwrap();
        assert_eq!(result, ReplAction::Continue);
    }

    #[test]
    fn process_quit() {
        let mut repl: Repl<()> = Repl::new();
        let result = repl.process_line("quit").unwrap();
        assert_eq!(result, ReplAction::Quit);
    }

    #[test]
    fn process_help() {
        let mut repl: Repl<()> = Repl::new();
        let result = repl.process_line("help").unwrap();
        match result {
            ReplAction::Print(msg) => {
                assert!(msg.contains("Available commands"));
            }
            _ => panic!("Expected Print action"),
        }
    }

    #[test]
    fn process_list() {
        let mut repl: Repl<()> = Repl::new();
        let result = repl.process_line("list").unwrap();
        match result {
            ReplAction::Print(msg) => {
                assert!(msg.contains("Defined relations"));
            }
            _ => panic!("Expected Print action"),
        }
    }

    #[test]
    fn process_query_after_load() {
        let mut repl: Repl<()> = Repl::new();
        // Load the addition example
        repl.process_line("load examples/addition.txt").unwrap();
        // Query should work now - (cons z z) ; add means "forward query 0+0"
        let result = repl.process_line("?- (cons z z) ; add").unwrap();
        assert!(matches!(result, ReplAction::Print(_)));
    }

    #[test]
    fn process_define() {
        let mut repl: Repl<()> = Repl::new();
        let result = repl.process_line("def foo = bar").unwrap();
        match result {
            ReplAction::Print(msg) => {
                assert!(msg.contains("Defined: foo = bar"));
            }
            _ => panic!("Expected Print action"),
        }
    }

    #[test]
    fn process_load_nonexistent_file() {
        let mut repl: Repl<()> = Repl::new();
        let result = repl.process_line("load nonexistent.rwl");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.to_string().contains("IO error"));
    }

    #[test]
    fn process_load_addition_example() {
        let mut repl: Repl<()> = Repl::new();
        let result = repl.process_line("load examples/addition.txt");
        assert!(result.is_ok());
        match result.unwrap() {
            ReplAction::Print(msg) => {
                assert!(msg.contains("add"));
                assert!(msg.contains("1 relation"));
            }
            _ => panic!("Expected Print action"),
        }
    }

    #[test]
    fn process_load_treecalc_example() {
        let mut repl: Repl<()> = Repl::new();
        let result = repl.process_line("load examples/treecalc.txt");
        assert!(result.is_ok());
        match result.unwrap() {
            ReplAction::Print(msg) => {
                assert!(msg.contains("app"));
                assert!(msg.contains("eval"));
                assert!(msg.contains("2 relation"));
            }
            _ => panic!("Expected Print action"),
        }
    }

    #[test]
    fn process_invalid_command() {
        let mut repl: Repl<()> = Repl::new();
        let result = repl.process_line("invalid");
        assert!(result.is_err());
    }

    // ========== REPL RUN TESTS ==========

    #[test]
    fn run_quit_immediately() {
        let mut repl: Repl<()> = Repl::new();
        let input = "quit\n";
        let mut input_cursor = Cursor::new(input.as_bytes());
        let mut output: Vec<u8> = Vec::new();

        repl.run(&mut input_cursor, &mut output).unwrap();

        let output_str = String::from_utf8(output).unwrap();
        assert!(output_str.contains("Goodbye!"));
    }

    #[test]
    fn run_help_then_quit() {
        let mut repl: Repl<()> = Repl::new();
        let input = "help\nquit\n";
        let mut input_cursor = Cursor::new(input.as_bytes());
        let mut output: Vec<u8> = Vec::new();

        repl.run(&mut input_cursor, &mut output).unwrap();

        let output_str = String::from_utf8(output).unwrap();
        assert!(output_str.contains("Available commands"));
        assert!(output_str.contains("Goodbye!"));
    }

    #[test]
    fn run_eof_exits() {
        let mut repl: Repl<()> = Repl::new();
        let input = "";
        let mut input_cursor = Cursor::new(input.as_bytes());
        let mut output: Vec<u8> = Vec::new();

        repl.run(&mut input_cursor, &mut output).unwrap();

        let output_str = String::from_utf8(output).unwrap();
        assert!(output_str.contains("Goodbye!"));
    }

    // ========== ERROR DISPLAY TESTS ==========

    #[test]
    fn repl_error_display_parse() {
        let err = ReplError::Parse(ParseError::UnexpectedEof);
        assert!(err.to_string().contains("Parse error"));
    }

    #[test]
    fn repl_error_display_io() {
        let io_err = io::Error::new(io::ErrorKind::NotFound, "file not found");
        let err = ReplError::Io(io_err);
        assert!(err.to_string().contains("IO error"));
    }

    #[test]
    fn repl_error_display_execution() {
        let err = ReplError::Execution("test error".to_string());
        assert!(err.to_string().contains("Execution error"));
    }

    // ========== ENGINE ACCESS TESTS ==========

    #[test]
    fn engine_access() {
        let repl: Repl<()> = Repl::new();
        let _engine = repl.engine();
    }

    #[test]
    fn engine_mut_access() {
        let mut repl: Repl<()> = Repl::new();
        let engine = repl.engine_mut();
        let _sym = engine.intern("test");
    }

    // ========== ADDITION E2E TESTS ==========
    // Tests based on AddRelSpec.hs from the Haskell implementation

    /// Helper to extract the result string from a query response.
    fn extract_result(action: &ReplAction) -> Option<&str> {
        match action {
            ReplAction::Print(s) => Some(s.as_str()),
            _ => None,
        }
    }

    /// Helper to extract the first answer from a query response.
    fn first_answer(action: &ReplAction) -> Option<&str> {
        extract_result(action).and_then(|s| s.lines().next())
    }

    /// Helper to check if expected answer is in the results.
    fn contains_answer(action: &ReplAction, expected: &str) -> bool {
        extract_result(action)
            .map(|s| s.lines().any(|line| line.contains(expected)))
            .unwrap_or(false)
    }

    /// Helper to create Peano number representation: z, (s z), (s (s z)), etc.
    fn peano(n: usize) -> String {
        if n == 0 {
            "z".to_string()
        } else {
            format!("(s {})", peano(n - 1))
        }
    }

    /// Helper to build a cons cell for addition input.
    fn cons(x: usize, y: usize) -> String {
        format!("(cons {} {})", peano(x), peano(y))
    }

    /// Max duration for any recursive relation test.
    /// If a test takes longer, it indicates a bug (infinite loop).
    const TEST_TIMEOUT_MS: u128 = 1000;

    /// Assert that a test completed within the timeout.
    fn assert_test_duration(start: std::time::Instant, test_name: &str) {
        let elapsed = start.elapsed().as_millis();
        assert!(
            elapsed < TEST_TIMEOUT_MS,
            "TEST TIMEOUT: {} took {}ms (limit: {}ms) - likely infinite loop",
            test_name,
            elapsed,
            TEST_TIMEOUT_MS
        );
    }

    #[test]
    fn addition_0_plus_0() {
        let start = std::time::Instant::now();
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();
        let result = repl.process_line("?- (cons z z) ; add").unwrap();
        assert_test_duration(start, "addition_0_plus_0");
        // Answer format: lhs -> rhs, so we check for "-> z"
        assert!(
            contains_answer(&result, "-> z"),
            "0 + 0 should equal 0, got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn addition_0_plus_1() {
        let start = std::time::Instant::now();
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();
        let result = repl.process_line("?- (cons z (s z)) ; add").unwrap();
        assert_test_duration(start, "addition_0_plus_1");
        assert!(
            contains_answer(&result, "-> (s z)"),
            "0 + 1 should equal 1, got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn addition_1_plus_0() {
        let start = std::time::Instant::now();
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();
        let result = repl.process_line("?- (cons (s z) z) ; add").unwrap();
        assert_test_duration(start, "addition_1_plus_0");
        assert!(
            contains_answer(&result, "-> (s z)"),
            "1 + 0 should equal 1, got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn addition_1_plus_1() {
        let start = std::time::Instant::now();
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();
        let result = repl.process_line("?- (cons (s z) (s z)) ; add").unwrap();
        assert_test_duration(start, "addition_1_plus_1");
        assert!(
            contains_answer(&result, "-> (s (s z))"),
            "1 + 1 should equal 2, got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn addition_2_plus_1() {
        let start = std::time::Instant::now();
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();
        let query = format!("?- {} ; add", cons(2, 1));
        let result = repl.process_line(&query).unwrap();
        assert_test_duration(start, "addition_2_plus_1");
        let expected = format!("-> {}", peano(3));
        assert!(
            contains_answer(&result, &expected),
            "2 + 1 should equal 3, got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn addition_3_plus_2_equals_5() {
        let start = std::time::Instant::now();
        // Exact test from AddRelSpec.hs: "computes 3 + 2 = 5"
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();
        let query = format!("?- {} ; add", cons(3, 2));
        let result = repl.process_line(&query).unwrap();
        assert_test_duration(start, "addition_3_plus_2_equals_5");
        let expected = format!("-> {}", peano(5));
        assert!(
            contains_answer(&result, &expected),
            "3 + 2 should equal 5, got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn addition_5_plus_3() {
        let start = std::time::Instant::now();
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();
        let query = format!("?- {} ; add", cons(5, 3));
        let result = repl.process_line(&query).unwrap();
        assert_test_duration(start, "addition_5_plus_3");
        let expected = format!("-> {}", peano(8));
        assert!(
            contains_answer(&result, &expected),
            "5 + 3 should equal 8, got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn addition_backward_query_sum_5() {
        let start = std::time::Instant::now();
        // From AddRelSpec.hs: "generates all pairs summing to 5 by running addition backwards"
        // ?- add ; (s (s (s (s (s z))))) should find 6 pairs: 0+5, 1+4, 2+3, 3+2, 4+1, 5+0
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();
        let five = peano(5);
        let query = format!("?- add ; {}", five);
        let result = repl.process_line(&query).unwrap();
        assert_test_duration(start, "addition_backward_query_sum_5");

        // Should find all 6 pairs that sum to 5
        for x in 0..=5 {
            let y = 5 - x;
            let expected = format!("(cons {} {}) -> {}", peano(x), peano(y), five);
            assert!(
                contains_answer(&result, &expected),
                "{} + {} = 5 should be found, got: {:?}",
                x, y,
                extract_result(&result)
            );
        }
    }

    #[test]
    fn addition_enumerate_relation() {
        let start = std::time::Instant::now();
        // Enumeration: ?- add should enumerate pairs in the relation
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();
        let result = repl.process_line("?- add").unwrap();
        assert_test_duration(start, "addition_enumerate_relation");
        // Should find at least the base case: (cons z $x) -> $x
        assert!(
            contains_answer(&result, "(cons z"),
            "Should enumerate pairs starting with (cons z ...), got: {:?}",
            extract_result(&result)
        );
    }

    // ========== TREE CALCULUS E2E TESTS ==========
    // Tests based on TreeCalcSpec.hs from the Haskell implementation

    #[test]
    fn treecalc_1() {
        let start = std::time::Instant::now();
        // From TreeCalcSpec.hs: (f (f l (b l)) (b (b l))) ~> (b l)
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/treecalc.txt").unwrap();
        let result = repl.process_line("?- (f (f l (b l)) (b (b l))) ; app").unwrap();
        assert_test_duration(start, "treecalc_1");
        assert!(
            contains_answer(&result, "-> (b l)"),
            "(f (f l (b l)) (b (b l))) should give (b l), got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn treecalc_2() {
        let start = std::time::Instant::now();
        // From TreeCalcSpec.hs: (f (f l (f l l)) (b (b (b l)))) ~> (f l l)
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/treecalc.txt").unwrap();
        let result = repl.process_line("?- (f (f l (f l l)) (b (b (b l)))) ; app").unwrap();
        assert_test_duration(start, "treecalc_2");
        assert!(
            contains_answer(&result, "-> (f l l)"),
            "(f (f l (f l l)) (b (b (b l)))) should give (f l l), got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn treecalc_3() {
        let start = std::time::Instant::now();
        // From TreeCalcSpec.hs: (f (f (f l l) l) (b (b l))) ~> (b (b l))
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/treecalc.txt").unwrap();
        let result = repl.process_line("?- (f (f (f l l) l) (b (b l))) ; app").unwrap();
        assert_test_duration(start, "treecalc_3");
        assert!(
            contains_answer(&result, "-> (b (b l))"),
            "(f (f (f l l) l) (b (b l))) should give (b (b l)), got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn treecalc_4() {
        let start = std::time::Instant::now();
        // From TreeCalcSpec.hs: (f (b (f l l)) (f l l)) ~> (f (f l l) (f l l))
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/treecalc.txt").unwrap();
        let result = repl.process_line("?- (f (b (f l l)) (f l l)) ; app").unwrap();
        assert_test_duration(start, "treecalc_4");
        assert!(
            contains_answer(&result, "-> (f (f l l) (f l l))"),
            "(f (b (f l l)) (f l l)) should give (f (f l l) (f l l)), got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn treecalc_5() {
        let start = std::time::Instant::now();
        // From TreeCalcSpec.hs: (f (f l l) (f (b l) (b l))) ~> l
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/treecalc.txt").unwrap();
        let result = repl.process_line("?- (f (f l l) (f (b l) (b l))) ; app").unwrap();
        assert_test_duration(start, "treecalc_5");
        assert!(
            contains_answer(&result, "-> l"),
            "(f (f l l) (f (b l) (b l))) should give l, got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn treecalc_6() {
        let start = std::time::Instant::now();
        // From TreeCalcSpec.hs: (f (f l (b l)) (f (b l) (b l))) ~> (b l)
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/treecalc.txt").unwrap();
        let result = repl.process_line("?- (f (f l (b l)) (f (b l) (b l))) ; app").unwrap();
        assert_test_duration(start, "treecalc_6");
        assert!(
            contains_answer(&result, "-> (b l)"),
            "(f (f l (b l)) (f (b l) (b l))) should give (b l), got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn treecalc_7() {
        let start = std::time::Instant::now();
        // From TreeCalcSpec.hs: (f (b l) (b (b (b l)))) ~> (f l (b (b (b l))))
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/treecalc.txt").unwrap();
        let result = repl.process_line("?- (f (b l) (b (b (b l)))) ; app").unwrap();
        assert_test_duration(start, "treecalc_7");
        assert!(
            contains_answer(&result, "-> (f l (b (b (b l))))"),
            "(f (b l) (b (b (b l)))) should give (f l (b (b (b l)))), got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn treecalc_8() {
        let start = std::time::Instant::now();
        // From TreeCalcSpec.hs: (f (f (f l (f l l)) (f l (b l))) (f (f l l) (b (f l l)))) ~> (f l (b (f l l)))
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/treecalc.txt").unwrap();
        let result = repl.process_line("?- (f (f (f l (f l l)) (f l (b l))) (f (f l l) (b (f l l)))) ; app").unwrap();
        assert_test_duration(start, "treecalc_8");
        assert!(
            contains_answer(&result, "-> (f l (b (f l l)))"),
            "complex treecalc should give (f l (b (f l l))), got: {:?}",
            extract_result(&result)
        );
    }

    #[test]
    fn treecalc_9() {
        let start = std::time::Instant::now();
        // From TreeCalcSpec.hs: (f (f (f l (b l)) (f (b l) (b l))) (f l (f (b l) (b l)))) ~> (f l l)
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/treecalc.txt").unwrap();
        let result = repl.process_line("?- (f (f (f l (b l)) (f (b l) (b l))) (f l (f (b l) (b l)))) ; app").unwrap();
        assert_test_duration(start, "treecalc_9");
        assert!(
            contains_answer(&result, "-> (f l l)"),
            "complex treecalc should give (f l l), got: {:?}",
            extract_result(&result)
        );
    }

    // ========== SYMMETRY BUG INVESTIGATION ==========
    // These tests investigate the backward query composition bug.
    // Evaluation should be perfectly symmetric: forward and backward queries
    // should both constrain properly when composed with ground terms.
    //
    // BUG: `?- add ; 5` returns generic patterns instead of specific pairs summing to 5

    #[test]
    fn symmetry_forward_query_constrains_input() {
        let start = std::time::Instant::now();
        // Forward query: (cons z z) ; add
        // The ground term (cons z z) should constrain the input
        // Expected: (cons z z) -> z (0 + 0 = 0)
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();
        let result = repl.process_line("?- (cons z z) ; add").unwrap();
        assert_test_duration(start, "symmetry_forward_query_constrains_input");
        let output = extract_result(&result).unwrap();

        // Should get exactly one answer with the specific input
        assert!(
            output.contains("(cons z z) -> z"),
            "Forward query should return specific pair, got: {}",
            output
        );
        // Should NOT contain variables in the answer (fully ground)
        assert!(
            !output.contains("$"),
            "Forward query result should be ground (no variables), got: {}",
            output
        );
    }

    #[test]
    fn symmetry_backward_query_constrains_output() {
        let start = std::time::Instant::now();
        // Backward query: add ; z
        // The ground term z should constrain the output
        // Expected: (cons z z) -> z (only 0 + 0 = 0)
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();
        let result = repl.process_line("?- add ; z").unwrap();
        assert_test_duration(start, "symmetry_backward_query_constrains_output");
        let output = extract_result(&result).unwrap();

        // Should get exactly one answer with the specific output
        assert!(
            output.contains("(cons z z) -> z"),
            "Backward query should return specific pair, got: {}",
            output
        );
        // Should NOT contain variables in the answer (fully ground)
        assert!(
            !output.contains("$"),
            "Backward query result should be ground (no variables), got: {}",
            output
        );
    }

    #[test]
    fn symmetry_backward_query_sum_1() {
        let start = std::time::Instant::now();
        // Backward query: add ; (s z)
        // Should find exactly 2 pairs: 0+1=1 and 1+0=1
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();
        let result = repl.process_line("?- add ; (s z)").unwrap();
        assert_test_duration(start, "symmetry_backward_query_sum_1");
        let output = extract_result(&result).unwrap();

        // Should find (cons z (s z)) -> (s z) [0 + 1 = 1]
        assert!(
            output.contains("(cons z (s z)) -> (s z)"),
            "0 + 1 = 1 should be found in backward query, got: {}",
            output
        );
        // Should find (cons (s z) z) -> (s z) [1 + 0 = 1]
        assert!(
            output.contains("(cons (s z) z) -> (s z)"),
            "1 + 0 = 1 should be found in backward query, got: {}",
            output
        );
        // Should NOT contain uninstantiated variables
        assert!(
            !output.contains("$"),
            "Backward query results should be ground (no variables), got: {}",
            output
        );
    }

    #[test]
    fn symmetry_identity_composition_left() {
        let start = std::time::Instant::now();
        // Composing identity on left: (cons z z) ; identity ; add
        // Should be equivalent to: (cons z z) ; add
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();

        // Direct forward query
        let direct = repl.process_line("?- (cons z z) ; add").unwrap();
        let direct_output = extract_result(&direct).unwrap();

        // With explicit identity (term composed with itself is identity)
        let with_identity = repl.process_line("?- (cons z z) ; [(cons z z) -> (cons z z)] ; add").unwrap();
        assert_test_duration(start, "symmetry_identity_composition_left");
        let identity_output = extract_result(&with_identity).unwrap();

        assert!(
            direct_output.contains("-> z"),
            "Direct query should work, got: {}",
            direct_output
        );
        assert!(
            identity_output.contains("-> z"),
            "Identity composition should work, got: {}",
            identity_output
        );
    }

    #[test]
    fn symmetry_identity_composition_right() {
        let start = std::time::Instant::now();
        // Composing identity on right: add ; z ; identity
        // The z is an identity relation on z, should constrain output
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();

        let result = repl.process_line("?- add ; z").unwrap();
        assert_test_duration(start, "symmetry_identity_composition_right");
        let output = extract_result(&result).unwrap();

        // z as identity relation should constrain add's output to z
        // Only (cons z z) -> z should match
        assert!(
            output.contains("(cons z z) -> z"),
            "add ; z should find 0+0=0, got: {}",
            output
        );
    }

    #[test]
    fn symmetry_enumerate_then_filter_vs_direct() {
        let start = std::time::Instant::now();
        // Two ways to get pairs summing to 1:
        // 1. Backward query: add ; (s z)
        // 2. Enumerate add and filter (conceptually)
        // Both should give the same results
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();

        // Backward query
        let backward = repl.process_line("?- add ; (s z)").unwrap();
        assert_test_duration(start, "symmetry_enumerate_then_filter_vs_direct");
        let backward_output = extract_result(&backward).unwrap();

        // The backward query should produce ground answers
        let has_0_plus_1 = backward_output.contains("(cons z (s z)) -> (s z)");
        let has_1_plus_0 = backward_output.contains("(cons (s z) z) -> (s z)");

        assert!(
            has_0_plus_1 && has_1_plus_0,
            "Backward query should find both pairs summing to 1, got: {}",
            backward_output
        );
    }

    #[test]
    fn symmetry_ground_term_filters_relation() {
        // When composing a relation with a ground term, the term should act as a filter
        // add ; (s z) should only return pairs where add's output unifies with (s z)
        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();

        let result = repl.process_line("?- add ; (s z)").unwrap();
        let output = extract_result(&result).unwrap();

        // All results should have (s z) as the RHS
        for line in output.lines() {
            if line.contains("->") {
                assert!(
                    line.ends_with("-> (s z)"),
                    "All backward query results should have (s z) as output, got line: {}",
                    line
                );
            }
        }
    }

    // ========== CLI SESSION TESTS ==========

    #[test]
    fn cli_session_load_query_list() {
        let mut repl: Repl<()> = Repl::new();

        // Load addition
        let load_result = repl.process_line("load examples/addition.txt");
        assert!(load_result.is_ok(), "Should load addition.txt");

        // List should show add
        let list_result = repl.process_line("list").unwrap();
        let list_output = extract_result(&list_result).unwrap();
        assert!(list_output.contains("add"), "List should contain 'add'");

        // Forward query should work
        let query_result = repl.process_line("?- (cons (s z) (s z)) ; add").unwrap();
        assert!(
            contains_answer(&query_result, "-> (s (s z))"),
            "1 + 1 should equal 2, got: {:?}",
            extract_result(&query_result)
        );
    }

    #[test]
    fn cli_session_multiple_files() {
        let mut repl: Repl<()> = Repl::new();

        // Load addition
        repl.process_line("load examples/addition.txt").unwrap();

        // Load tree calculus
        repl.process_line("load examples/treecalc.txt").unwrap();

        // List should show all relations
        let list_result = repl.process_line("list").unwrap();
        let list_output = extract_result(&list_result).unwrap();
        assert!(list_output.contains("add"), "Should contain 'add'");
        assert!(list_output.contains("app"), "Should contain 'app'");
        assert!(list_output.contains("eval"), "Should contain 'eval'");

        // Both queries should work
        let add_result = repl.process_line("?- (cons z z) ; add").unwrap();
        assert!(
            contains_answer(&add_result, "-> z"),
            "0 + 0 should equal 0"
        );

        let app_result = repl.process_line("?- (f l l) ; app").unwrap();
        assert!(
            contains_answer(&app_result, "-> (b l)"),
            "app(L, L) should give B(L)"
        );
    }

    #[test]
    fn cli_session_error_recovery() {
        let mut repl: Repl<()> = Repl::new();

        // Bad load shouldn't crash
        assert!(repl.process_line("load nonexistent.txt").is_err());

        // Should still work after error
        assert!(repl.process_line("load examples/addition.txt").is_ok());
        let result = repl.process_line("?- (cons z z) ; add").unwrap();
        assert!(
            contains_answer(&result, "-> z"),
            "0 + 0 should equal 0"
        );
    }

    // ========== DEBUG TEST FOR BACKWARD QUERY BUG ==========

    #[test]
    fn debug_backward_query_trace() {
        // Trace what happens step by step in a backward query
        use crate::cli::file_parser::FileParser;

        let mut repl: Repl<()> = Repl::new();
        repl.process_line("load examples/addition.txt").unwrap();

        // Parse the query manually
        let query_str = "add ; z";
        let mut parser = FileParser::new(query_str);
        let expr = parser.parse_expr().unwrap();
        eprintln!("Parsed expression: {:?}", expr);

        // Check what rel_goals contains
        eprintln!("rel_goals: {:?}", repl.rel_goals.keys().collect::<Vec<_>>());

        // Now execute the query
        let result = repl.process_line("?- add ; z").unwrap();
        let output = extract_result(&result).unwrap();
        eprintln!("Query result: {}", output);

        // Also try the forward query for comparison
        let fwd_result = repl.process_line("?- (cons z z) ; add").unwrap();
        let fwd_output = extract_result(&fwd_result).unwrap();
        eprintln!("Forward query result: {}", fwd_output);

        // Try composing in a different order
        let manual_result = repl.process_line("?- z -> z").unwrap();
        let manual_output = extract_result(&manual_result).unwrap();
        eprintln!("Identity z -> z: {}", manual_output);

        // Create a seq of the identity THEN the add (reverse order)
        let reverse_result = repl.process_line("?- [z -> z] ; add").unwrap();
        let reverse_output = extract_result(&reverse_result).unwrap();
        eprintln!("Reverse [z -> z] ; add: {}", reverse_output);

        // The real test - what happens when we try add ; [z -> z]
        let bracket_result = repl.process_line("?- add ; [z -> z]").unwrap();
        let bracket_output = extract_result(&bracket_result).unwrap();
        eprintln!("Bracketed add ; [z -> z]: {}", bracket_output);
    }
}
