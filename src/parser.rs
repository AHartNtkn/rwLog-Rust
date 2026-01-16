//! Parser for rwlog relation definitions.
//!
//! Syntax:
//! - `rel name { body }` - relation definition
//! - `pattern -> pattern` - rewrite rule (atomic relation)
//! - `|` - Or (disjunction) - lowest precedence
//! - `;` - Seq (sequential composition)
//! - `&` - And (intersection/conjunction) - highest precedence
//! - `[...]` - grouping for sequences
//! - `$var` - variable
//! - `atom` - lowercase identifier (nullary constructor)
//! - `@term` - term literal (identity relation at term)
//! - `(f x y ...)` - compound term

use crate::nf::NF;
use crate::rel::{Rel, RelId};
use crate::symbol::SymbolStore;
use crate::term::TermStore;
use smallvec::SmallVec;
use std::collections::HashMap;
use std::sync::Arc;

/// Result of parsing a term - TermId plus variable info.
#[derive(Clone, Debug)]
pub struct ParsedTerm {
    pub term_id: crate::term::TermId,
    /// Variables in order of first occurrence.
    pub var_order: Vec<u32>,
}

/// Parser state.
pub struct Parser {
    symbols: SymbolStore,
    terms: TermStore,
    /// Named relations (for recursive calls).
    relations: HashMap<String, RelId>,
    /// Next available RelId.
    next_rel_id: RelId,
}

/// Parse error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub position: usize,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Parse error at position {}: {}", self.position, self.message)
    }
}

impl std::error::Error for ParseError {}

impl Parser {
    /// Create a new parser.
    pub fn new() -> Self {
        Self {
            symbols: SymbolStore::new(),
            terms: TermStore::new(),
            relations: HashMap::new(),
            next_rel_id: 0,
        }
    }

    /// Create a parser with existing symbol and term stores.
    pub fn with_stores(symbols: SymbolStore, terms: TermStore) -> Self {
        Self {
            symbols,
            terms,
            relations: HashMap::new(),
            next_rel_id: 0,
        }
    }

    /// Get the symbol store.
    pub fn symbols(&self) -> &SymbolStore {
        &self.symbols
    }

    /// Get the term store.
    pub fn terms(&self) -> &TermStore {
        &self.terms
    }

    /// Take ownership of the term store, leaving a fresh one behind.
    pub fn take_terms(&mut self) -> TermStore {
        std::mem::take(&mut self.terms)
    }

    /// Restore the term store after temporary extraction.
    pub fn restore_terms(&mut self, terms: TermStore) {
        self.terms = terms;
    }

    /// Consume the parser and return the stores.
    pub fn into_stores(self) -> (SymbolStore, TermStore) {
        (self.symbols, self.terms)
    }

    /// Parse a term from a string.
    /// Returns the TermId and the variable order.
    pub fn parse_term(&self, input: &str) -> Result<ParsedTerm, ParseError> {
        let mut pos = 0;
        let mut var_map: HashMap<String, u32> = HashMap::new();
        let mut var_order: Vec<u32> = Vec::new();
        let term = self.parse_term_inner(input, &mut pos, &mut var_map, &mut var_order)?;
        skip_whitespace(input, &mut pos);
        if pos < input.len() {
            return Err(ParseError {
                message: "Unexpected characters after term".to_string(),
                position: pos,
            });
        }
        Ok(ParsedTerm {
            term_id: term,
            var_order,
        })
    }

    /// Parse a term, tracking variables.
    fn parse_term_inner(
        &self,
        input: &str,
        pos: &mut usize,
        var_map: &mut HashMap<String, u32>,
        var_order: &mut Vec<u32>,
    ) -> Result<crate::term::TermId, ParseError> {
        skip_whitespace(input, pos);

        if *pos >= input.len() {
            return Err(ParseError {
                message: "Unexpected end of input".to_string(),
                position: *pos,
            });
        }

        let ch = input.chars().nth(*pos).unwrap();

        if ch == '$' {
            // Variable
            *pos += 1;
            let name = parse_identifier(input, pos)?;
            let var_id = if let Some(&id) = var_map.get(&name) {
                id
            } else {
                let id = var_map.len() as u32;
                var_map.insert(name, id);
                var_order.push(id);
                id
            };
            Ok(self.terms.var(var_id))
        } else if ch == '(' {
            // Compound term: (f args...)
            *pos += 1;
            skip_whitespace(input, pos);
            let functor = parse_identifier(input, pos)?;
            let sym = self.symbols.intern(&functor);

            let mut args: SmallVec<[crate::term::TermId; 4]> = SmallVec::new();
            loop {
                skip_whitespace(input, pos);
                if *pos >= input.len() {
                    return Err(ParseError {
                        message: "Unclosed parenthesis".to_string(),
                        position: *pos,
                    });
                }
                if input.chars().nth(*pos).unwrap() == ')' {
                    *pos += 1;
                    break;
                }
                args.push(self.parse_term_inner(input, pos, var_map, var_order)?);
            }

            Ok(self.terms.app(sym, args))
        } else if ch.is_ascii_lowercase() || ch.is_ascii_digit() {
            // Atom (nullary constructor)
            let name = parse_identifier(input, pos)?;
            let sym = self.symbols.intern(&name);
            Ok(self.terms.app0(sym))
        } else {
            Err(ParseError {
                message: format!("Unexpected character: '{}'", ch),
                position: *pos,
            })
        }
    }

    /// Parse a rule: `lhs -> rhs`
    pub fn parse_rule(&mut self, input: &str) -> Result<NF<()>, ParseError> {
        let mut pos = 0;
        let rule = self.parse_rule_inner(input, &mut pos)?;
        skip_whitespace(input, &mut pos);
        if pos < input.len() {
            return Err(ParseError {
                message: "Unexpected characters after rule".to_string(),
                position: pos,
            });
        }
        Ok(rule)
    }

    /// Parse a rule, returning an NF.
    fn parse_rule_inner(&mut self, input: &str, pos: &mut usize) -> Result<NF<()>, ParseError> {
        let mut var_map: HashMap<String, u32> = HashMap::new();
        let mut var_order: Vec<u32> = Vec::new();

        // Parse LHS
        let lhs = self.parse_term_inner(input, pos, &mut var_map, &mut var_order)?;

        // Expect ->
        skip_whitespace(input, pos);
        if !input[*pos..].starts_with("->") {
            return Err(ParseError {
                message: "Expected '->'".to_string(),
                position: *pos,
            });
        }
        *pos += 2;

        // Parse RHS with the same var_map (to share variables)
        let rhs = self.parse_term_inner(input, pos, &mut var_map, &mut var_order)?;

        Ok(NF::factor(lhs, rhs, (), &mut self.terms))
    }

    /// Parse a relation body (the part inside `rel name { ... }`).
    pub fn parse_rel_body(&mut self, input: &str) -> Result<Rel<()>, ParseError> {
        let mut pos = 0;
        let rel = self.parse_or_expr(input, &mut pos)?;
        skip_whitespace(input, &mut pos);
        if pos < input.len() {
            return Err(ParseError {
                message: format!("Unexpected characters after relation body: '{}'", &input[pos..]),
                position: pos,
            });
        }
        Ok(rel)
    }

    /// Parse an Or expression (lowest precedence).
    fn parse_or_expr(&mut self, input: &str, pos: &mut usize) -> Result<Rel<()>, ParseError> {
        let mut left = self.parse_seq_expr(input, pos)?;

        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() || input.chars().nth(*pos).unwrap() != '|' {
                break;
            }
            *pos += 1;
            let right = self.parse_seq_expr(input, pos)?;
            left = Rel::Or(Arc::new(left), Arc::new(right));
        }

        Ok(left)
    }

    /// Parse a Seq expression (semicolon-separated).
    fn parse_seq_expr(&mut self, input: &str, pos: &mut usize) -> Result<Rel<()>, ParseError> {
        let mut factors: Vec<Arc<Rel<()>>> = Vec::new();
        factors.push(Arc::new(self.parse_and_expr(input, pos)?));

        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                break;
            }
            let ch = input.chars().nth(*pos).unwrap();
            if ch != ';' {
                break;
            }
            *pos += 1;
            factors.push(Arc::new(self.parse_and_expr(input, pos)?));
        }

        if factors.len() == 1 {
            Ok(Arc::try_unwrap(factors.pop().unwrap()).unwrap_or_else(|arc| (*arc).clone()))
        } else {
            Ok(Rel::Seq(Arc::from(factors)))
        }
    }

    /// Parse an And expression (ampersand-separated, highest precedence).
    fn parse_and_expr(&mut self, input: &str, pos: &mut usize) -> Result<Rel<()>, ParseError> {
        let mut left = self.parse_primary(input, pos)?;

        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() || input.chars().nth(*pos).unwrap() != '&' {
                break;
            }
            *pos += 1;
            let right = self.parse_primary(input, pos)?;
            left = Rel::And(Arc::new(left), Arc::new(right));
        }

        Ok(left)
    }

    /// Parse a primary expression (rule, call, or bracketed expr).
    fn parse_primary(&mut self, input: &str, pos: &mut usize) -> Result<Rel<()>, ParseError> {
        skip_whitespace(input, pos);

        if *pos >= input.len() {
            return Err(ParseError {
                message: "Unexpected end of input".to_string(),
                position: *pos,
            });
        }

        let ch = input.chars().nth(*pos).unwrap();

        if ch == '[' {
            // Bracketed sequence
            *pos += 1;
            let inner = self.parse_or_expr(input, pos)?;
            skip_whitespace(input, pos);
            if *pos >= input.len() || input.chars().nth(*pos).unwrap() != ']' {
                return Err(ParseError {
                    message: "Expected ']'".to_string(),
                    position: *pos,
                });
            }
            *pos += 1;
            Ok(inner)
        } else if ch == '@' {
            *pos += 1;
            let mut var_map: HashMap<String, u32> = HashMap::new();
            let mut var_order: Vec<u32> = Vec::new();
            let term = self.parse_term_inner(input, pos, &mut var_map, &mut var_order)?;
            let nf = NF::factor(term, term, (), &mut self.terms);
            Ok(Rel::Atom(Arc::new(nf)))
        } else if ch == '$' || ch == '(' {
            // Rule starting with term
            let rule = self.parse_rule_inner(input, pos)?;
            Ok(Rel::Atom(Arc::new(rule)))
        } else if ch.is_alphabetic() && ch.is_lowercase() {
            // Could be atom (start of rule) or relation call
            let start_pos = *pos;
            let name = parse_identifier(input, pos)?;
            skip_whitespace(input, pos);

            // Check if this is followed by -> (making it a rule starting with an atom)
            if *pos < input.len() && input[*pos..].starts_with("->") {
                // It's a rule: restore position and parse as rule
                *pos = start_pos;
                let rule = self.parse_rule_inner(input, pos)?;
                Ok(Rel::Atom(Arc::new(rule)))
            } else {
                // It's a relation call
                if let Some(&rel_id) = self.relations.get(&name) {
                    Ok(Rel::Call(rel_id))
                } else {
                    // Unknown relation - allocate a new RelId
                    // This will be resolved when we parse the relation definition
                    let rel_id = self.next_rel_id;
                    self.next_rel_id += 1;
                    self.relations.insert(name, rel_id);
                    Ok(Rel::Call(rel_id))
                }
            }
        } else {
            Err(ParseError {
                message: format!("Unexpected character in primary: '{}'", ch),
                position: *pos,
            })
        }
    }

    /// Parse a complete relation definition.
    pub fn parse_rel_def(&mut self, input: &str) -> Result<(String, Rel<()>), ParseError> {
        let mut pos = 0;
        skip_whitespace(input, &mut pos);

        // Expect 'rel'
        if !input[pos..].starts_with("rel") {
            return Err(ParseError {
                message: "Expected 'rel' keyword".to_string(),
                position: pos,
            });
        }
        pos += 3;

        // Parse name
        skip_whitespace(input, &mut pos);
        let name = parse_identifier(input, &mut pos)?;

        // Register the relation name if not already registered
        let rel_id = if let Some(&id) = self.relations.get(&name) {
            id
        } else {
            let id = self.next_rel_id;
            self.next_rel_id += 1;
            self.relations.insert(name.clone(), id);
            id
        };

        // Expect '{'
        skip_whitespace(input, &mut pos);
        if pos >= input.len() || input.chars().nth(pos).unwrap() != '{' {
            return Err(ParseError {
                message: "Expected '{'".to_string(),
                position: pos,
            });
        }
        pos += 1;

        // Parse body
        let body = self.parse_rel_body_until_brace(input, &mut pos)?;

        // Expect '}'
        skip_whitespace(input, &mut pos);
        if pos >= input.len() || input.chars().nth(pos).unwrap() != '}' {
            return Err(ParseError {
                message: "Expected '}'".to_string(),
                position: pos,
            });
        }
        // Wrap in Fix to enable recursion
        let rel = Rel::Fix(rel_id, Arc::new(body));

        Ok((name, rel))
    }

    /// Parse relation body until we hit a closing brace.
    fn parse_rel_body_until_brace(&mut self, input: &str, pos: &mut usize) -> Result<Rel<()>, ParseError> {
        self.parse_or_expr_until(input, pos, '}')
    }

    /// Parse an Or expression, stopping at a given character.
    fn parse_or_expr_until(&mut self, input: &str, pos: &mut usize, stop_char: char) -> Result<Rel<()>, ParseError> {
        let mut left = self.parse_seq_expr_until(input, pos, stop_char)?;

        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                break;
            }
            let ch = input.chars().nth(*pos).unwrap();
            if ch == stop_char || ch != '|' {
                break;
            }
            *pos += 1;
            let right = self.parse_seq_expr_until(input, pos, stop_char)?;
            left = Rel::Or(Arc::new(left), Arc::new(right));
        }

        Ok(left)
    }

    /// Parse a Seq expression, stopping at a given character.
    fn parse_seq_expr_until(&mut self, input: &str, pos: &mut usize, stop_char: char) -> Result<Rel<()>, ParseError> {
        let mut factors: Vec<Arc<Rel<()>>> = Vec::new();
        factors.push(Arc::new(self.parse_and_expr_until(input, pos, stop_char)?));

        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                break;
            }
            let ch = input.chars().nth(*pos).unwrap();
            if ch == stop_char || ch == '|' {
                break;
            }
            if ch != ';' {
                break;
            }
            *pos += 1;
            factors.push(Arc::new(self.parse_and_expr_until(input, pos, stop_char)?));
        }

        if factors.len() == 1 {
            Ok(Arc::try_unwrap(factors.pop().unwrap()).unwrap_or_else(|arc| (*arc).clone()))
        } else {
            Ok(Rel::Seq(Arc::from(factors)))
        }
    }

    /// Parse an And expression, stopping at a given character.
    fn parse_and_expr_until(&mut self, input: &str, pos: &mut usize, stop_char: char) -> Result<Rel<()>, ParseError> {
        let mut left = self.parse_primary_until(input, pos, stop_char)?;

        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                break;
            }
            let ch = input.chars().nth(*pos).unwrap();
            if ch == stop_char || ch == '|' || ch == ';' {
                break;
            }
            if ch != '&' {
                break;
            }
            *pos += 1;
            let right = self.parse_primary_until(input, pos, stop_char)?;
            left = Rel::And(Arc::new(left), Arc::new(right));
        }

        Ok(left)
    }

    /// Parse a primary expression, stopping at a given character.
    fn parse_primary_until(&mut self, input: &str, pos: &mut usize, stop_char: char) -> Result<Rel<()>, ParseError> {
        skip_whitespace(input, pos);

        if *pos >= input.len() {
            return Err(ParseError {
                message: "Unexpected end of input".to_string(),
                position: *pos,
            });
        }

        let ch = input.chars().nth(*pos).unwrap();

        if ch == stop_char {
            return Err(ParseError {
                message: format!("Unexpected '{}'", stop_char),
                position: *pos,
            });
        }

        if ch == '[' {
            // Bracketed sequence
            *pos += 1;
            let inner = self.parse_or_expr_until(input, pos, ']')?;
            skip_whitespace(input, pos);
            if *pos >= input.len() || input.chars().nth(*pos).unwrap() != ']' {
                return Err(ParseError {
                    message: "Expected ']'".to_string(),
                    position: *pos,
                });
            }
            *pos += 1;
            Ok(inner)
        } else if ch == '$' || ch == '(' {
            // Rule starting with term
            let rule = self.parse_rule_inner(input, pos)?;
            Ok(Rel::Atom(Arc::new(rule)))
        } else if ch.is_alphabetic() && ch.is_lowercase() {
            // Could be atom (start of rule) or relation call
            let start_pos = *pos;
            let name = parse_identifier(input, pos)?;
            skip_whitespace(input, pos);

            // Check if this is followed by -> (making it a rule starting with an atom)
            if *pos < input.len() && input[*pos..].starts_with("->") {
                // It's a rule: restore position and parse as rule
                *pos = start_pos;
                let rule = self.parse_rule_inner(input, pos)?;
                Ok(Rel::Atom(Arc::new(rule)))
            } else {
                // It's a relation call
                if let Some(&rel_id) = self.relations.get(&name) {
                    Ok(Rel::Call(rel_id))
                } else {
                    // Unknown relation - allocate a new RelId
                    let rel_id = self.next_rel_id;
                    self.next_rel_id += 1;
                    self.relations.insert(name, rel_id);
                    Ok(Rel::Call(rel_id))
                }
            }
        } else {
            Err(ParseError {
                message: format!("Unexpected character in primary: '{}'", ch),
                position: *pos,
            })
        }
    }
}

impl Default for Parser {
    fn default() -> Self {
        Self::new()
    }
}

/// Skip whitespace and comments.
fn skip_whitespace(input: &str, pos: &mut usize) {
    while *pos < input.len() {
        let ch = input.chars().nth(*pos).unwrap();
        if ch.is_whitespace() {
            *pos += 1;
        } else if ch == '#' {
            // Comment - skip to end of line
            while *pos < input.len() && input.chars().nth(*pos).unwrap() != '\n' {
                *pos += 1;
            }
        } else {
            break;
        }
    }
}

/// Parse an identifier (lowercase letters, digits, underscores).
fn parse_identifier(input: &str, pos: &mut usize) -> Result<String, ParseError> {
    let start = *pos;
    while *pos < input.len() {
        let ch = input.chars().nth(*pos).unwrap();
        if ch.is_alphanumeric() || ch == '_' {
            *pos += 1;
        } else {
            break;
        }
    }

    if *pos == start {
        return Err(ParseError {
            message: "Expected identifier".to_string(),
            position: *pos,
        });
    }

    Ok(input[start..*pos].to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // TERM PARSING TESTS
    // ========================================================================

    #[test]
    fn parse_atom() {
        let parser = Parser::new();
        let result = parser.parse_term("z");
        assert!(result.is_ok(), "Should parse atom");
        let parsed = result.unwrap();
        assert!(parsed.var_order.is_empty(), "Atom has no variables");
    }

    #[test]
    fn parse_numeric_atom() {
        let parser = Parser::new();
        let result = parser.parse_term("0");
        assert!(result.is_ok(), "Should parse numeric atom");
        let parsed = result.unwrap();
        assert!(parsed.var_order.is_empty(), "Numeric atom has no variables");
    }

    #[test]
    fn parse_variable() {
        let parser = Parser::new();
        let result = parser.parse_term("$x");
        assert!(result.is_ok(), "Should parse variable");
        let parsed = result.unwrap();
        assert_eq!(parsed.var_order.len(), 1, "Should have one variable");
    }

    #[test]
    fn parse_compound_term_nullary() {
        let parser = Parser::new();
        let result = parser.parse_term("(f)");
        assert!(result.is_ok(), "Should parse nullary compound");
    }

    #[test]
    fn parse_compound_term_unary() {
        let parser = Parser::new();
        let result = parser.parse_term("(s z)");
        assert!(result.is_ok(), "Should parse unary compound");
    }

    #[test]
    fn parse_compound_with_numeric_atom() {
        let parser = Parser::new();
        let result = parser.parse_term("(c 0)");
        assert!(
            result.is_ok(),
            "Should parse compound with numeric atom argument"
        );
    }

    #[test]
    fn parse_compound_term_binary() {
        let parser = Parser::new();
        let result = parser.parse_term("(cons z z)");
        assert!(result.is_ok(), "Should parse binary compound");
    }

    #[test]
    fn parse_nested_compound() {
        let parser = Parser::new();
        let result = parser.parse_term("(cons (s z) (s (s z)))");
        assert!(result.is_ok(), "Should parse nested compound");
    }

    #[test]
    fn parse_term_with_variable() {
        let parser = Parser::new();
        let result = parser.parse_term("(s $x)");
        assert!(result.is_ok());
        let parsed = result.unwrap();
        assert_eq!(parsed.var_order.len(), 1);
    }

    #[test]
    fn parse_term_multiple_variables() {
        let parser = Parser::new();
        let result = parser.parse_term("(cons $x $y)");
        assert!(result.is_ok());
        let parsed = result.unwrap();
        assert_eq!(parsed.var_order.len(), 2);
    }

    #[test]
    fn parse_term_repeated_variable() {
        let parser = Parser::new();
        let result = parser.parse_term("(cons $x $x)");
        assert!(result.is_ok());
        let parsed = result.unwrap();
        // Same variable used twice, but only counted once
        assert_eq!(parsed.var_order.len(), 1);
    }

    #[test]
    fn parse_term_whitespace_handling() {
        let parser = Parser::new();
        let result = parser.parse_term("  (  cons   $x   $y  )  ");
        assert!(result.is_ok());
    }

    #[test]
    fn parse_term_unclosed_paren_fails() {
        let parser = Parser::new();
        let result = parser.parse_term("(cons $x");
        assert!(result.is_err());
    }

    #[test]
    fn parse_term_extra_chars_fails() {
        let parser = Parser::new();
        let result = parser.parse_term("z extra");
        assert!(result.is_err());
    }

    // ========================================================================
    // RULE PARSING TESTS
    // ========================================================================

    #[test]
    fn parse_simple_rule() {
        let mut parser = Parser::new();
        let result = parser.parse_rule("z -> z");
        assert!(result.is_ok(), "Should parse simple rule");
    }

    #[test]
    fn parse_rule_with_compound() {
        let mut parser = Parser::new();
        let result = parser.parse_rule("(s $x) -> $x");
        assert!(result.is_ok());
    }

    #[test]
    fn parse_rule_with_variables() {
        let mut parser = Parser::new();
        let result = parser.parse_rule("(cons $x $y) -> $y");
        assert!(result.is_ok());
    }

    #[test]
    fn parse_rule_rhs_only_variable_creates_fresh_output() {
        let mut parser = Parser::new();
        let nf = parser
            .parse_rule("$x -> (f $x $y)")
            .expect("parse rule with rhs-only variable");
        assert_eq!(nf.wire.in_arity, 1);
        assert_eq!(nf.wire.out_arity, 2);
        assert_eq!(nf.wire.map.as_slice(), &[(0, 0)]);
    }

    #[test]
    fn parse_rule_lhs_only_variable_is_dropped() {
        let mut parser = Parser::new();
        let nf = parser
            .parse_rule("(f $x $y) -> $x")
            .expect("parse rule with lhs-only variable");
        assert_eq!(nf.wire.in_arity, 2);
        assert_eq!(nf.wire.out_arity, 1);
        assert_eq!(nf.wire.map.as_slice(), &[(0, 0)]);
    }

    #[test]
    fn parse_complex_rule() {
        let mut parser = Parser::new();
        let result = parser.parse_rule("(cons (s $x) $y) -> (cons $x $y)");
        assert!(result.is_ok());
    }

    #[test]
    fn parse_rule_missing_arrow_fails() {
        let mut parser = Parser::new();
        let result = parser.parse_rule("z z");
        assert!(result.is_err());
    }

    #[test]
    fn parse_rule_missing_rhs_fails() {
        let mut parser = Parser::new();
        let result = parser.parse_rule("z ->");
        assert!(result.is_err());
    }

    // ========================================================================
    // RELATION BODY PARSING TESTS
    // ========================================================================

    #[test]
    fn parse_single_rule_body() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_body("z -> z");
        assert!(result.is_ok());
        assert!(matches!(result.unwrap(), Rel::Atom(_)));
    }

    #[test]
    fn parse_term_literal_identity_body() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_body("@z").unwrap();
        match result {
            Rel::Atom(nf) => {
                assert_eq!(nf.match_pats.len(), 1);
                assert_eq!(nf.build_pats.len(), 1);
                assert_eq!(nf.match_pats[0], nf.build_pats[0]);
            }
            _ => panic!("Expected term literal to parse as Atom identity"),
        }
    }

    #[test]
    fn parse_or_body() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_body("z -> z | (s z) -> (s z)");
        assert!(result.is_ok());
        assert!(matches!(result.unwrap(), Rel::Or(_, _)));
    }

    #[test]
    fn parse_seq_body() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_body("z -> (s z) ; (s $x) -> $x");
        assert!(result.is_ok());
        assert!(matches!(result.unwrap(), Rel::Seq(_)));
    }

    #[test]
    fn parse_bracketed_seq() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_body("[z -> (s z) ; (s $x) -> $x]");
        assert!(result.is_ok());
    }

    #[test]
    fn parse_or_with_seq() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_body("z -> z | [a -> b ; b -> c]");
        assert!(result.is_ok());
        match result.unwrap() {
            Rel::Or(left, right) => {
                assert!(matches!(left.as_ref(), Rel::Atom(_)));
                assert!(matches!(right.as_ref(), Rel::Seq(_)));
            }
            _ => panic!("Expected Or"),
        }
    }

    #[test]
    fn parse_call_in_seq() {
        let mut parser = Parser::new();
        // First register a relation
        parser.relations.insert("foo".to_string(), 0);
        let result = parser.parse_rel_body("a -> b ; foo ; c -> d");
        assert!(result.is_ok());
        match result.unwrap() {
            Rel::Seq(factors) => {
                assert_eq!(factors.len(), 3);
                assert!(matches!(factors[1].as_ref(), Rel::Call(0)));
            }
            _ => panic!("Expected Seq"),
        }
    }

    #[test]
    fn parse_nested_brackets() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_body("[[a -> b]]");
        assert!(result.is_ok());
    }

    #[test]
    fn parse_and_body() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_body("a -> a & b -> b");
        assert!(result.is_ok());
        assert!(matches!(result.unwrap(), Rel::And(_, _)));
    }

    #[test]
    fn parse_and_with_or() {
        let mut parser = Parser::new();
        // `|` binds looser than `&`
        // So `a & b | c & d` should parse as `(a & b) | (c & d)`
        // Use [...] for grouping rules
        let result = parser.parse_rel_body("[a -> a] & [b -> b] | [c -> c] & [d -> d]");
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());
        match result.unwrap() {
            Rel::Or(left, right) => {
                assert!(matches!(left.as_ref(), Rel::And(_, _)));
                assert!(matches!(right.as_ref(), Rel::And(_, _)));
            }
            _ => panic!("Expected Or at top level"),
        }
    }

    #[test]
    fn parse_and_with_seq() {
        let mut parser = Parser::new();
        // `&` binds tighter than `;`
        // So `a ; b & c ; d` should parse as `a ; (b & c) ; d`
        let result = parser.parse_rel_body("[a -> a] ; [b -> b] & [c -> c] ; [d -> d]");
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());
        match result.unwrap() {
            Rel::Seq(factors) => {
                assert_eq!(factors.len(), 3);
                assert!(matches!(factors[0].as_ref(), Rel::Atom(_)));
                assert!(matches!(factors[1].as_ref(), Rel::And(_, _)));
                assert!(matches!(factors[2].as_ref(), Rel::Atom(_)));
            }
            _ => panic!("Expected Seq at top level"),
        }
    }

    #[test]
    fn parse_chained_and() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_body("[a -> a] & [b -> b] & [c -> c]");
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());
        // Should be left-associative: ((a & b) & c)
        match result.unwrap() {
            Rel::And(left, right) => {
                assert!(matches!(left.as_ref(), Rel::And(_, _)));
                assert!(matches!(right.as_ref(), Rel::Atom(_)));
            }
            _ => panic!("Expected And"),
        }
    }

    // ========================================================================
    // RELATION DEFINITION PARSING TESTS
    // ========================================================================

    #[test]
    fn parse_simple_rel_def() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_def("rel id { $x -> $x }");
        assert!(result.is_ok());
        let (name, rel) = result.unwrap();
        assert_eq!(name, "id");
        assert!(matches!(rel, Rel::Fix(_, _)));
    }

    #[test]
    fn parse_rel_def_with_or() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_def("rel test { a -> b | c -> d }");
        assert!(result.is_ok());
        let (name, rel) = result.unwrap();
        assert_eq!(name, "test");
        match rel {
            Rel::Fix(_, body) => {
                assert!(matches!(body.as_ref(), Rel::Or(_, _)));
            }
            _ => panic!("Expected Fix"),
        }
    }

    #[test]
    fn parse_recursive_rel_def() {
        let mut parser = Parser::new();
        let input = r#"
            rel add {
                (cons z $y) -> $y
                |
                [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
            }
        "#;
        let result = parser.parse_rel_def(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
        let (name, _rel) = result.unwrap();
        assert_eq!(name, "add");
    }

    #[test]
    fn parse_rel_def_missing_brace_fails() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_def("rel test { $x -> $x");
        assert!(result.is_err());
    }

    #[test]
    fn parse_rel_def_missing_name_fails() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_def("rel { $x -> $x }");
        assert!(result.is_err());
    }

    // ========================================================================
    // COMMENT HANDLING TESTS
    // ========================================================================

    #[test]
    fn parse_with_comments() {
        let parser = Parser::new();
        let result = parser.parse_term("# this is a comment\nz");
        assert!(result.is_ok());
    }

    #[test]
    fn parse_rule_with_comment() {
        let mut parser = Parser::new();
        let result = parser.parse_rule("z -> z # identity");
        assert!(result.is_ok());
    }

    #[test]
    fn parse_rel_body_with_comments() {
        let mut parser = Parser::new();
        let input = r#"
            # Base case
            z -> z
            |
            # Recursive case
            (s $x) -> (s $x)
        "#;
        let result = parser.parse_rel_body(input);
        assert!(result.is_ok());
    }

    // ========================================================================
    // EDGE CASE TESTS
    // ========================================================================

    #[test]
    fn parse_empty_input_fails() {
        let parser = Parser::new();
        let result = parser.parse_term("");
        assert!(result.is_err());
    }

    #[test]
    fn parse_whitespace_only_fails() {
        let parser = Parser::new();
        let result = parser.parse_term("   ");
        assert!(result.is_err());
    }

    #[test]
    fn parse_identifier_with_underscores() {
        let parser = Parser::new();
        let result = parser.parse_term("my_atom");
        assert!(result.is_ok());
    }

    #[test]
    fn parse_identifier_with_numbers() {
        let parser = Parser::new();
        let result = parser.parse_term("x1");
        assert!(result.is_ok());
    }

    #[test]
    fn parse_variable_with_underscore() {
        let parser = Parser::new();
        let result = parser.parse_term("$my_var");
        assert!(result.is_ok());
    }

    // ========================================================================
    // SIZE AND MEMORY TESTS
    // ========================================================================

    #[test]
    fn parser_size_reasonable() {
        use std::mem::size_of;
        let size = size_of::<Parser>();
        // Parser contains SymbolStore, TermStore, and HashMap<String, RelId>
        assert!(size < 1000, "Parser should not be excessively large, got {}", size);
    }

    #[test]
    fn parse_error_size_reasonable() {
        use std::mem::size_of;
        let size = size_of::<ParseError>();
        assert!(size < 100, "ParseError should not be excessively large, got {}", size);
    }
}
