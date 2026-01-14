//! File parser for rwlog definition files.
//!
//! Parses `.txt` or `.rwl` files containing relation definitions.
//!
//! # Syntax
//!
//! ```text
//! # Comments start with #
//!
//! # Terms use S-expression syntax: (ctor arg1 arg2 ...)
//! # Nullary constructors are just identifiers: z, l
//! # Variables have $ prefix: $x, $y
//!
//! # Rewrite rule: lhs -> rhs
//! (cons z $y) -> $y
//!
//! # Combinators:
//! #   ; = Seq (sequential composition)
//! #   | = Alt (disjunction)
//! #   & = Both (conjunction)
//!
//! # Relation definition
//! rel add {
//!     ((cons z $y) -> $y)
//!     | [((cons (s $x) $y) -> (cons $x $y)) ; add ; ($z -> (s $z))]
//! }
//! ```

use std::fmt;

/// A parsed definition file containing zero or more relation definitions.
#[derive(Debug, Clone, PartialEq)]
pub struct ParsedFile {
    pub relations: Vec<RelationDef>,
}

/// A relation definition: `rel name { body }`
#[derive(Debug, Clone, PartialEq)]
pub struct RelationDef {
    pub name: String,
    pub body: ParsedExpr,
    pub line: usize,
}

/// An expression in the file format (maps to Goal IR).
#[derive(Debug, Clone, PartialEq)]
pub enum ParsedExpr {
    /// Simple rewrite rule: `lhs -> rhs`
    Rule {
        lhs: ParsedTerm,
        rhs: ParsedTerm,
        line: usize,
    },
    /// Sequential composition: `expr ; expr` -> Goal::Seq
    Seq(Vec<ParsedExpr>),
    /// Disjunction: `expr | expr` -> Goal::Alt
    Alt(Vec<ParsedExpr>),
    /// Conjunction: `expr & expr` -> Goal::Both
    Both(Vec<ParsedExpr>),
    /// Call to a relation: `name` -> Goal::Call
    Call(String),
    /// Bare term (used in queries): becomes identity relation `term -> term`
    Term(ParsedTerm),
}

/// A term in the file format.
#[derive(Debug, Clone, PartialEq)]
pub enum ParsedTerm {
    /// Variable: `$x`
    Var(String),
    /// Nullary constructor: `z`, `l`
    Atom(String),
    /// N-ary application: `(ctor arg1 arg2 ...)`
    App(String, Vec<ParsedTerm>),
}

/// File parsing error with location information.
#[derive(Debug, Clone, PartialEq)]
pub struct FileParseError {
    pub line: usize,
    pub col: usize,
    pub message: String,
}

impl fmt::Display for FileParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.col, self.message)
    }
}

impl std::error::Error for FileParseError {}

/// Parser for relation definition files.
pub struct FileParser {
    input: Vec<char>,
    pos: usize,
    line: usize,
    col: usize,
}

impl FileParser {
    /// Create a new parser for the given input.
    pub fn new(input: &str) -> Self {
        Self {
            input: input.chars().collect(),
            pos: 0,
            line: 1,
            col: 1,
        }
    }

    /// Parse the entire file.
    pub fn parse_file(&mut self) -> Result<ParsedFile, FileParseError> {
        let mut relations = Vec::new();

        loop {
            self.skip_whitespace_and_comments();
            if self.is_at_end() {
                break;
            }

            let rel = self.parse_relation()?;
            relations.push(rel);
        }

        Ok(ParsedFile { relations })
    }

    /// Parse a relation definition: `rel name { body }`
    fn parse_relation(&mut self) -> Result<RelationDef, FileParseError> {
        let line = self.line;

        // Expect 'rel' keyword
        let keyword = self.parse_identifier()?;
        if keyword != "rel" {
            return Err(self.error(format!("Expected 'rel', found '{}'", keyword)));
        }

        self.skip_whitespace_and_comments();

        // Parse relation name
        let name = self.parse_identifier()?;
        if name.is_empty() {
            return Err(self.error("Expected relation name after 'rel'".to_string()));
        }

        self.skip_whitespace_and_comments();

        // Expect '{'
        if self.peek() != Some('{') {
            return Err(self.error(format!(
                "Expected '{{' after relation name, found {:?}",
                self.peek()
            )));
        }
        self.advance();

        self.skip_whitespace_and_comments();

        // Parse body expression
        let body = self.parse_expr()?;

        self.skip_whitespace_and_comments();

        // Expect '}'
        if self.peek() != Some('}') {
            return Err(self.error(format!(
                "Expected '}}' after relation body, found {:?}",
                self.peek()
            )));
        }
        self.advance();

        Ok(RelationDef { name, body, line })
    }

    /// Parse an expression (handles operator precedence).
    /// Precedence (low to high): | < & < ; < -> < [ ]
    pub fn parse_expr(&mut self) -> Result<ParsedExpr, FileParseError> {
        self.parse_alt()
    }

    /// Parse alternation: `expr | expr | ...`
    fn parse_alt(&mut self) -> Result<ParsedExpr, FileParseError> {
        let mut exprs = vec![self.parse_both()?];

        loop {
            self.skip_whitespace_and_comments();
            if self.peek() == Some('|') {
                self.advance();
                self.skip_whitespace_and_comments();
                exprs.push(self.parse_both()?);
            } else {
                break;
            }
        }

        if exprs.len() == 1 {
            Ok(exprs.pop().unwrap())
        } else {
            Ok(ParsedExpr::Alt(exprs))
        }
    }

    /// Parse conjunction: `expr & expr & ...`
    fn parse_both(&mut self) -> Result<ParsedExpr, FileParseError> {
        let mut exprs = vec![self.parse_seq()?];

        loop {
            self.skip_whitespace_and_comments();
            if self.peek() == Some('&') {
                self.advance();
                self.skip_whitespace_and_comments();
                exprs.push(self.parse_seq()?);
            } else {
                break;
            }
        }

        if exprs.len() == 1 {
            Ok(exprs.pop().unwrap())
        } else {
            Ok(ParsedExpr::Both(exprs))
        }
    }

    /// Parse sequential composition: `expr ; expr ; ...`
    fn parse_seq(&mut self) -> Result<ParsedExpr, FileParseError> {
        let mut exprs = vec![self.parse_primary()?];

        loop {
            self.skip_whitespace_and_comments();
            if self.peek() == Some(';') {
                self.advance();
                self.skip_whitespace_and_comments();
                exprs.push(self.parse_primary()?);
            } else {
                break;
            }
        }

        if exprs.len() == 1 {
            Ok(exprs.pop().unwrap())
        } else {
            Ok(ParsedExpr::Seq(exprs))
        }
    }

    /// Parse primary expression: rule, call, or grouped expression.
    fn parse_primary(&mut self) -> Result<ParsedExpr, FileParseError> {
        self.skip_whitespace_and_comments();

        match self.peek() {
            Some('[') => {
                // Grouped expression
                self.advance();
                self.skip_whitespace_and_comments();
                let expr = self.parse_expr()?;
                self.skip_whitespace_and_comments();
                if self.peek() != Some(']') {
                    return Err(self.error("Expected ']' after grouped expression".to_string()));
                }
                self.advance();
                Ok(expr)
            }
            Some('(') => {
                // Rule: (lhs) -> (rhs) or just (lhs -> rhs)
                self.parse_rule_or_grouped_rule()
            }
            Some('$') => {
                // Rule starting with variable: $x -> ...
                self.parse_rule_starting_with_term()
            }
            Some(c) if c.is_alphabetic() || c == '_' => {
                // Could be a call or a rule starting with an atom
                self.parse_call_or_rule()
            }
            Some(c) => Err(self.error(format!("Unexpected character: '{}'", c))),
            None => Err(self.error("Unexpected end of input".to_string())),
        }
    }

    /// Parse a rule or grouped rule starting with '('.
    fn parse_rule_or_grouped_rule(&mut self) -> Result<ParsedExpr, FileParseError> {
        let line = self.line;
        let lhs = self.parse_term()?;

        self.skip_whitespace_and_comments();

        // Check for '->'
        if self.peek() == Some('-') {
            self.advance();
            if self.peek() != Some('>') {
                return Err(self.error("Expected '>' after '-'".to_string()));
            }
            self.advance();
            self.skip_whitespace_and_comments();
            let rhs = self.parse_term()?;
            Ok(ParsedExpr::Rule { lhs, rhs, line })
        } else {
            // No '->' follows - this is a bare term (identity relation)
            Ok(ParsedExpr::Term(lhs))
        }
    }

    /// Parse a rule starting with a term (variable or atom).
    fn parse_rule_starting_with_term(&mut self) -> Result<ParsedExpr, FileParseError> {
        let line = self.line;
        let lhs = self.parse_term()?;

        self.skip_whitespace_and_comments();

        if self.peek() == Some('-') {
            self.advance();
            if self.peek() != Some('>') {
                return Err(self.error("Expected '>' after '-'".to_string()));
            }
            self.advance();
            self.skip_whitespace_and_comments();
            let rhs = self.parse_term()?;
            Ok(ParsedExpr::Rule { lhs, rhs, line })
        } else {
            // No '->' follows - this is a bare term (identity relation)
            Ok(ParsedExpr::Term(lhs))
        }
    }

    /// Parse a call or rule starting with an identifier.
    fn parse_call_or_rule(&mut self) -> Result<ParsedExpr, FileParseError> {
        let start_pos = self.pos;
        let start_line = self.line;
        let start_col = self.col;

        let ident = self.parse_identifier()?;

        self.skip_whitespace_and_comments();

        // Check what follows the identifier
        match self.peek() {
            Some('-') => {
                // It's a rule: atom -> rhs
                self.advance();
                if self.peek() != Some('>') {
                    return Err(self.error("Expected '>' after '-'".to_string()));
                }
                self.advance();
                self.skip_whitespace_and_comments();
                let rhs = self.parse_term()?;
                Ok(ParsedExpr::Rule {
                    lhs: ParsedTerm::Atom(ident),
                    rhs,
                    line: start_line,
                })
            }
            Some(';') | Some('|') | Some('&') | Some(']') | Some('}') | None => {
                // It's a call
                Ok(ParsedExpr::Call(ident))
            }
            Some(_) => {
                // Backtrack and try parsing as a term for a rule
                self.pos = start_pos;
                self.line = start_line;
                self.col = start_col;
                self.parse_rule_starting_with_term()
            }
        }
    }

    /// Parse a term: variable, atom, or application.
    pub fn parse_term(&mut self) -> Result<ParsedTerm, FileParseError> {
        self.skip_whitespace_and_comments();

        match self.peek() {
            Some('$') => {
                // Variable
                self.advance();
                let name = self.parse_identifier()?;
                if name.is_empty() {
                    return Err(self.error("Expected variable name after '$'".to_string()));
                }
                Ok(ParsedTerm::Var(name))
            }
            Some('(') => {
                // Application: (ctor arg1 arg2 ...)
                self.advance();
                self.skip_whitespace_and_comments();

                let ctor = self.parse_identifier()?;
                if ctor.is_empty() {
                    return Err(self.error("Expected constructor name in application".to_string()));
                }

                let mut args = Vec::new();
                loop {
                    self.skip_whitespace_and_comments();
                    if self.peek() == Some(')') {
                        self.advance();
                        break;
                    }
                    args.push(self.parse_term()?);
                }

                Ok(ParsedTerm::App(ctor, args))
            }
            Some(c) if c.is_alphabetic() || c == '_' => {
                // Atom (nullary constructor)
                let name = self.parse_identifier()?;
                Ok(ParsedTerm::Atom(name))
            }
            Some(c) => Err(self.error(format!("Unexpected character in term: '{}'", c))),
            None => Err(self.error("Unexpected end of input in term".to_string())),
        }
    }

    /// Parse an identifier (alphanumeric + underscore).
    fn parse_identifier(&mut self) -> Result<String, FileParseError> {
        let mut result = String::new();
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                result.push(c);
                self.advance();
            } else {
                break;
            }
        }
        Ok(result)
    }

    /// Skip whitespace and comments.
    fn skip_whitespace_and_comments(&mut self) {
        loop {
            // Skip whitespace
            while let Some(c) = self.peek() {
                if c.is_whitespace() {
                    self.advance();
                } else {
                    break;
                }
            }

            // Skip comment
            if self.peek() == Some('#') {
                while let Some(c) = self.peek() {
                    if c == '\n' {
                        self.advance();
                        break;
                    }
                    self.advance();
                }
            } else {
                break;
            }
        }
    }

    fn is_at_end(&self) -> bool {
        self.pos >= self.input.len()
    }

    fn peek(&self) -> Option<char> {
        self.input.get(self.pos).copied()
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.peek();
        if let Some(ch) = c {
            self.pos += 1;
            if ch == '\n' {
                self.line += 1;
                self.col = 1;
            } else {
                self.col += 1;
            }
        }
        c
    }

    fn error(&self, message: String) -> FileParseError {
        FileParseError {
            line: self.line,
            col: self.col,
            message,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========== EMPTY FILE TESTS ==========

    #[test]
    fn parse_empty_file() {
        let mut parser = FileParser::new("");
        let file = parser.parse_file().unwrap();
        assert!(file.relations.is_empty());
    }

    #[test]
    fn parse_whitespace_only_file() {
        let mut parser = FileParser::new("   \n\t\n   ");
        let file = parser.parse_file().unwrap();
        assert!(file.relations.is_empty());
    }

    #[test]
    fn parse_comments_only_file() {
        let mut parser = FileParser::new("# comment 1\n# comment 2\n");
        let file = parser.parse_file().unwrap();
        assert!(file.relations.is_empty());
    }

    // ========== TERM PARSING TESTS ==========

    #[test]
    fn parse_term_variable() {
        let mut parser = FileParser::new("$x");
        let term = parser.parse_term().unwrap();
        assert_eq!(term, ParsedTerm::Var("x".to_string()));
    }

    #[test]
    fn parse_term_variable_long_name() {
        let mut parser = FileParser::new("$foo_bar123");
        let term = parser.parse_term().unwrap();
        assert_eq!(term, ParsedTerm::Var("foo_bar123".to_string()));
    }

    #[test]
    fn parse_term_atom() {
        let mut parser = FileParser::new("z");
        let term = parser.parse_term().unwrap();
        assert_eq!(term, ParsedTerm::Atom("z".to_string()));
    }

    #[test]
    fn parse_term_atom_long_name() {
        let mut parser = FileParser::new("leaf");
        let term = parser.parse_term().unwrap();
        assert_eq!(term, ParsedTerm::Atom("leaf".to_string()));
    }

    #[test]
    fn parse_term_nullary_application() {
        let mut parser = FileParser::new("(s)");
        let term = parser.parse_term().unwrap();
        assert_eq!(term, ParsedTerm::App("s".to_string(), vec![]));
    }

    #[test]
    fn parse_term_unary_application() {
        let mut parser = FileParser::new("(s z)");
        let term = parser.parse_term().unwrap();
        assert_eq!(
            term,
            ParsedTerm::App("s".to_string(), vec![ParsedTerm::Atom("z".to_string())])
        );
    }

    #[test]
    fn parse_term_binary_application() {
        let mut parser = FileParser::new("(cons $x $y)");
        let term = parser.parse_term().unwrap();
        assert_eq!(
            term,
            ParsedTerm::App(
                "cons".to_string(),
                vec![
                    ParsedTerm::Var("x".to_string()),
                    ParsedTerm::Var("y".to_string())
                ]
            )
        );
    }

    #[test]
    fn parse_term_nested_application() {
        let mut parser = FileParser::new("(s (s z))");
        let term = parser.parse_term().unwrap();
        assert_eq!(
            term,
            ParsedTerm::App(
                "s".to_string(),
                vec![ParsedTerm::App(
                    "s".to_string(),
                    vec![ParsedTerm::Atom("z".to_string())]
                )]
            )
        );
    }

    #[test]
    fn parse_term_deeply_nested() {
        let mut parser = FileParser::new("(f (g $x) (h (k $y) $z))");
        let term = parser.parse_term().unwrap();
        assert_eq!(
            term,
            ParsedTerm::App(
                "f".to_string(),
                vec![
                    ParsedTerm::App("g".to_string(), vec![ParsedTerm::Var("x".to_string())]),
                    ParsedTerm::App(
                        "h".to_string(),
                        vec![
                            ParsedTerm::App("k".to_string(), vec![ParsedTerm::Var("y".to_string())]),
                            ParsedTerm::Var("z".to_string())
                        ]
                    )
                ]
            )
        );
    }

    // ========== RULE PARSING TESTS ==========

    #[test]
    fn parse_simple_rule() {
        let mut parser = FileParser::new("rel test { $x -> $y }");
        let file = parser.parse_file().unwrap();
        assert_eq!(file.relations.len(), 1);
        assert_eq!(file.relations[0].name, "test");
        assert!(matches!(
            &file.relations[0].body,
            ParsedExpr::Rule { lhs: ParsedTerm::Var(x), rhs: ParsedTerm::Var(y), .. }
            if x == "x" && y == "y"
        ));
    }

    #[test]
    fn parse_rule_atom_to_atom() {
        let mut parser = FileParser::new("rel test { z -> l }");
        let file = parser.parse_file().unwrap();
        assert!(matches!(
            &file.relations[0].body,
            ParsedExpr::Rule { lhs: ParsedTerm::Atom(x), rhs: ParsedTerm::Atom(y), .. }
            if x == "z" && y == "l"
        ));
    }

    #[test]
    fn parse_rule_app_to_var() {
        let mut parser = FileParser::new("rel test { (cons z $y) -> $y }");
        let file = parser.parse_file().unwrap();
        assert!(matches!(&file.relations[0].body, ParsedExpr::Rule { .. }));
    }

    #[test]
    fn parse_rule_complex_lhs_rhs() {
        let mut parser = FileParser::new("rel test { (f (g $x) $y) -> (h $x (k $y)) }");
        let file = parser.parse_file().unwrap();
        assert!(matches!(&file.relations[0].body, ParsedExpr::Rule { .. }));
    }

    // ========== COMBINATOR PARSING TESTS ==========

    #[test]
    fn parse_alt_two_branches() {
        // Rules don't need grouping - use [] if you need to group expressions
        let mut parser = FileParser::new("rel test { $x -> $y | $a -> $b }");
        let file = parser.parse_file().unwrap();
        assert!(matches!(&file.relations[0].body, ParsedExpr::Alt(branches) if branches.len() == 2));
    }

    #[test]
    fn parse_alt_three_branches() {
        let mut parser = FileParser::new("rel test { $x -> $x | $y -> $y | $z -> $z }");
        let file = parser.parse_file().unwrap();
        assert!(matches!(&file.relations[0].body, ParsedExpr::Alt(branches) if branches.len() == 3));
    }

    #[test]
    fn parse_seq_two_steps() {
        // Use [] for grouping expressions, not ()
        let mut parser = FileParser::new("rel test { [$x -> $y] ; [$y -> $z] }");
        let file = parser.parse_file().unwrap();
        assert!(matches!(&file.relations[0].body, ParsedExpr::Seq(steps) if steps.len() == 2));
    }

    #[test]
    fn parse_seq_three_steps() {
        let mut parser = FileParser::new("rel test { [$x -> $y] ; [$y -> $z] ; [$z -> $w] }");
        let file = parser.parse_file().unwrap();
        assert!(matches!(&file.relations[0].body, ParsedExpr::Seq(steps) if steps.len() == 3));
    }

    #[test]
    fn parse_both_two_constraints() {
        let mut parser = FileParser::new("rel test { [$x -> $y] & [$a -> $b] }");
        let file = parser.parse_file().unwrap();
        assert!(matches!(&file.relations[0].body, ParsedExpr::Both(constraints) if constraints.len() == 2));
    }

    #[test]
    fn parse_call() {
        let mut parser = FileParser::new("rel test { [$x -> $y] ; other }");
        let file = parser.parse_file().unwrap();
        match &file.relations[0].body {
            ParsedExpr::Seq(steps) => {
                assert_eq!(steps.len(), 2);
                assert!(matches!(&steps[1], ParsedExpr::Call(name) if name == "other"));
            }
            _ => panic!("Expected Seq"),
        }
    }

    // ========== OPERATOR PRECEDENCE TESTS ==========

    #[test]
    fn precedence_alt_lower_than_seq() {
        // a | b ; c should parse as a | (b ; c)
        // Using [] for grouping and S-expr terms
        let mut parser = FileParser::new("rel test { $x -> $x | [$y -> $y] ; [$z -> $z] }");
        let file = parser.parse_file().unwrap();
        match &file.relations[0].body {
            ParsedExpr::Alt(branches) => {
                assert_eq!(branches.len(), 2);
                assert!(matches!(&branches[0], ParsedExpr::Rule { .. }));
                assert!(matches!(&branches[1], ParsedExpr::Seq(steps) if steps.len() == 2));
            }
            _ => panic!("Expected Alt at top level"),
        }
    }

    #[test]
    fn precedence_both_lower_than_seq() {
        // a & b ; c should parse as a & (b ; c)
        let mut parser = FileParser::new("rel test { $x -> $x & [$y -> $y] ; [$z -> $z] }");
        let file = parser.parse_file().unwrap();
        match &file.relations[0].body {
            ParsedExpr::Both(constraints) => {
                assert_eq!(constraints.len(), 2);
                assert!(matches!(&constraints[0], ParsedExpr::Rule { .. }));
                assert!(matches!(&constraints[1], ParsedExpr::Seq(steps) if steps.len() == 2));
            }
            _ => panic!("Expected Both at top level"),
        }
    }

    #[test]
    fn precedence_alt_lower_than_both() {
        // a | b & c should parse as a | (b & c)
        let mut parser = FileParser::new("rel test { $x -> $x | [$y -> $y] & [$z -> $z] }");
        let file = parser.parse_file().unwrap();
        match &file.relations[0].body {
            ParsedExpr::Alt(branches) => {
                assert_eq!(branches.len(), 2);
                assert!(matches!(&branches[0], ParsedExpr::Rule { .. }));
                assert!(matches!(&branches[1], ParsedExpr::Both(constraints) if constraints.len() == 2));
            }
            _ => panic!("Expected Alt at top level"),
        }
    }

    // ========== GROUPING TESTS ==========

    #[test]
    fn grouping_overrides_precedence() {
        // [a | b] ; c should parse as (a | b) ; c
        let mut parser = FileParser::new("rel test { [$x -> $x | $y -> $y] ; [$z -> $z] }");
        let file = parser.parse_file().unwrap();
        match &file.relations[0].body {
            ParsedExpr::Seq(steps) => {
                assert_eq!(steps.len(), 2);
                assert!(matches!(&steps[0], ParsedExpr::Alt(branches) if branches.len() == 2));
                assert!(matches!(&steps[1], ParsedExpr::Rule { .. }));
            }
            _ => panic!("Expected Seq at top level"),
        }
    }

    #[test]
    fn nested_grouping() {
        let mut parser =
            FileParser::new("rel test { [[$x -> $x | $y -> $y] ; [$z -> $z]] | $w -> $w }");
        let file = parser.parse_file().unwrap();
        assert!(matches!(&file.relations[0].body, ParsedExpr::Alt(branches) if branches.len() == 2));
    }

    // ========== MULTIPLE RELATIONS TESTS ==========

    #[test]
    fn parse_multiple_relations() {
        let input = r#"
            rel first { $x -> $x }
            rel second { $y -> $y }
            rel third { $z -> $z }
        "#;
        let mut parser = FileParser::new(input);
        let file = parser.parse_file().unwrap();
        assert_eq!(file.relations.len(), 3);
        assert_eq!(file.relations[0].name, "first");
        assert_eq!(file.relations[1].name, "second");
        assert_eq!(file.relations[2].name, "third");
    }

    // ========== ADDITION EXAMPLE TEST ==========

    #[test]
    fn parse_addition_relation() {
        let input = r#"
            # Peano addition
            rel add {
                (cons z $y) -> $y
                | [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
            }
        "#;
        let mut parser = FileParser::new(input);
        let file = parser.parse_file().unwrap();
        assert_eq!(file.relations.len(), 1);
        assert_eq!(file.relations[0].name, "add");

        // Should be Alt with 2 branches
        match &file.relations[0].body {
            ParsedExpr::Alt(branches) => {
                assert_eq!(branches.len(), 2);
                // First branch: base case rule
                assert!(matches!(&branches[0], ParsedExpr::Rule { .. }));
                // Second branch: grouped Seq
                match &branches[1] {
                    ParsedExpr::Seq(steps) => {
                        assert_eq!(steps.len(), 3);
                        assert!(matches!(&steps[0], ParsedExpr::Rule { .. }));
                        assert!(matches!(&steps[1], ParsedExpr::Call(name) if name == "add"));
                        assert!(matches!(&steps[2], ParsedExpr::Rule { .. }));
                    }
                    _ => panic!("Expected Seq for recursive branch"),
                }
            }
            _ => panic!("Expected Alt at top level"),
        }
    }

    // ========== TREE CALCULUS EXAMPLE TEST ==========

    #[test]
    fn parse_treecalc_relations() {
        let input = r#"
            # Tree calculus
            rel app {
                (f l $z) -> (b $z)
                | (f (b $y) $z) -> (f $y $z)
                | (f (f l $y) $z) -> $y
                | (f (f (f $w $x) $y) l) -> $w
            }

            rel eval {
                $x -> $x
                | [app ; eval]
            }
        "#;
        let mut parser = FileParser::new(input);
        let file = parser.parse_file().unwrap();
        assert_eq!(file.relations.len(), 2);
        assert_eq!(file.relations[0].name, "app");
        assert_eq!(file.relations[1].name, "eval");

        // app should have 4 branches
        match &file.relations[0].body {
            ParsedExpr::Alt(branches) => assert_eq!(branches.len(), 4),
            _ => panic!("Expected Alt for app"),
        }

        // eval should have 2 branches
        match &file.relations[1].body {
            ParsedExpr::Alt(branches) => {
                assert_eq!(branches.len(), 2);
                assert!(matches!(&branches[0], ParsedExpr::Rule { .. }));
                match &branches[1] {
                    ParsedExpr::Seq(steps) => {
                        assert_eq!(steps.len(), 2);
                        assert!(matches!(&steps[0], ParsedExpr::Call(name) if name == "app"));
                        assert!(matches!(&steps[1], ParsedExpr::Call(name) if name == "eval"));
                    }
                    _ => panic!("Expected Seq"),
                }
            }
            _ => panic!("Expected Alt for eval"),
        }
    }

    // ========== ERROR TESTS ==========

    #[test]
    fn error_missing_arrow() {
        let mut parser = FileParser::new("rel test { $x $y }");
        let result = parser.parse_file();
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.message.contains("->") || err.message.contains("Expected"));
    }

    #[test]
    fn error_unclosed_paren() {
        let mut parser = FileParser::new("rel test { (cons $x -> $y }");
        let result = parser.parse_file();
        assert!(result.is_err());
    }

    #[test]
    fn error_unclosed_bracket() {
        let mut parser = FileParser::new("rel test { [$x -> $y }");
        let result = parser.parse_file();
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.message.contains("]"));
    }

    #[test]
    fn error_missing_brace() {
        let mut parser = FileParser::new("rel test { $x -> $y");
        let result = parser.parse_file();
        assert!(result.is_err());
    }

    #[test]
    fn error_missing_relation_name() {
        let mut parser = FileParser::new("rel { $x -> $y }");
        let result = parser.parse_file();
        assert!(result.is_err());
    }

    #[test]
    fn error_invalid_keyword() {
        let mut parser = FileParser::new("define foo { $x -> $y }");
        let result = parser.parse_file();
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.message.contains("rel"));
    }

    #[test]
    fn error_empty_variable_name() {
        let mut parser = FileParser::new("rel test { $ -> $y }");
        let result = parser.parse_file();
        assert!(result.is_err());
    }

    #[test]
    fn error_line_numbers_preserved() {
        let input = "# comment\n\nrel test {\n  (unclosed\n}";
        let mut parser = FileParser::new(input);
        let result = parser.parse_file();
        assert!(result.is_err());
        let err = result.unwrap_err();
        // Error should be on line 4 or later (where the unclosed paren is)
        assert!(err.line >= 4);
    }

    // ========== PARSE ERROR DISPLAY TESTS ==========

    #[test]
    fn parse_error_display() {
        let err = FileParseError {
            line: 5,
            col: 12,
            message: "Expected '->'".to_string(),
        };
        assert_eq!(err.to_string(), "5:12: Expected '->'");
    }
}
