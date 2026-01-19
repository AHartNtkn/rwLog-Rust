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

use crate::chr::{
    ArgExpr, BodyInstr, BodyProg, ChrProgram, ChrProgramBuilder, ChrState, GuardInstr, GuardProg,
    GVal, HeadPat, NoTheory, PatId, PredId, RVar,
};
use crate::constraint::ConstraintOps;
use crate::nf::NF;
use crate::rel::{Rel, RelId};
use crate::symbol::SymbolStore;
use crate::term::{TermId, TermStore};
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

#[derive(Clone, Debug)]
pub struct ConstraintCall {
    name: String,
    args: Vec<TermId>,
    position: usize,
}

#[derive(Clone, Debug)]
pub struct TheorySummary {
    pub name: String,
    pub predicates: usize,
    pub rules: usize,
}

pub trait ConstraintBuilder: Clone {
    type Constraint: ConstraintOps + Clone + Eq + Default + Send + Sync;

    fn empty_constraint(&self) -> Self::Constraint {
        Self::Constraint::default()
    }

    fn build_constraint(
        &mut self,
        calls: Vec<ConstraintCall>,
        terms: &mut TermStore,
    ) -> Result<Self::Constraint, ParseError>;

    fn parse_theory_def(
        &mut self,
        input: &str,
        symbols: &mut SymbolStore,
        terms: &mut TermStore,
    ) -> Result<TheorySummary, ParseError>;
}

#[derive(Clone, Debug, Default)]
pub struct NoConstraintBuilder;

impl ConstraintBuilder for NoConstraintBuilder {
    type Constraint = ();

    fn build_constraint(
        &mut self,
        calls: Vec<ConstraintCall>,
        _terms: &mut TermStore,
    ) -> Result<Self::Constraint, ParseError> {
        let pos = calls.first().map(|c| c.position).unwrap_or(0);
        Err(ParseError {
            message: "Constraints are not supported in this parser".to_string(),
            position: pos,
        })
    }

    fn parse_theory_def(
        &mut self,
        _input: &str,
        _symbols: &mut SymbolStore,
        _terms: &mut TermStore,
    ) -> Result<TheorySummary, ParseError> {
        Err(ParseError {
            message: "Theory blocks are not supported in this parser".to_string(),
            position: 0,
        })
    }
}

#[derive(Clone, Debug)]
pub struct ChrConstraintBuilder {
    builder: ChrProgramBuilder<NoTheory>,
    program: Arc<ChrProgram<NoTheory>>,
}

impl ChrConstraintBuilder {
    pub fn new() -> Self {
        let builder = ChrProgramBuilder::new(crate::chr::BuiltinRegistry::default());
        let program = builder.clone().build();
        Self { builder, program }
    }

    pub fn program(&self) -> Arc<ChrProgram<NoTheory>> {
        self.program.clone()
    }
}

impl Default for ChrConstraintBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl ConstraintBuilder for ChrConstraintBuilder {
    type Constraint = ChrState<NoTheory>;

    fn empty_constraint(&self) -> Self::Constraint {
        ChrState::new(self.program.clone(), ())
    }

    fn build_constraint(
        &mut self,
        calls: Vec<ConstraintCall>,
        terms: &mut TermStore,
    ) -> Result<Self::Constraint, ParseError> {
        let mut st = ChrState::new(self.program.clone(), ());
        for call in calls {
            let pred = self
                .program
                .pred_id(&call.name)
                .ok_or_else(|| ParseError {
                    message: format!("unknown constraint predicate '{}'", call.name),
                    position: call.position,
                })?;
            let expected = self.program.preds[pred.0 as usize].arity as usize;
            if call.args.len() != expected {
                return Err(ParseError {
                    message: format!(
                        "constraint '{}' arity {} expects {} args, got {}",
                        call.name,
                        expected,
                        expected,
                        call.args.len()
                    ),
                    position: call.position,
                });
            }
            st.introduce(pred, &call.args, terms);
        }
        Ok(st)
    }

    fn parse_theory_def(
        &mut self,
        input: &str,
        symbols: &mut SymbolStore,
        terms: &mut TermStore,
    ) -> Result<TheorySummary, ParseError> {
        let summary = parse_chr_theory(input, &mut self.builder, symbols, terms)?;
        self.program = self.builder.clone().build();
        Ok(summary)
    }
}

/// Parser state.
pub struct Parser<B: ConstraintBuilder = NoConstraintBuilder> {
    symbols: SymbolStore,
    terms: TermStore,
    /// Named relations (for recursive calls).
    relations: HashMap<String, RelId>,
    /// Next available RelId.
    next_rel_id: RelId,
    constraints: B,
}

/// Parse error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub position: usize,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Parse error at position {}: {}",
            self.position, self.message
        )
    }
}

impl std::error::Error for ParseError {}

impl Parser<NoConstraintBuilder> {
    /// Create a new parser.
    pub fn new() -> Self {
        Self {
            symbols: SymbolStore::new(),
            terms: TermStore::new(),
            relations: HashMap::new(),
            next_rel_id: 0,
            constraints: NoConstraintBuilder,
        }
    }

    /// Create a parser with existing symbol and term stores.
    pub fn with_stores(symbols: SymbolStore, terms: TermStore) -> Self {
        Self {
            symbols,
            terms,
            relations: HashMap::new(),
            next_rel_id: 0,
            constraints: NoConstraintBuilder,
        }
    }
}

impl<B: ConstraintBuilder> Parser<B> {
    pub fn with_builder(builder: B) -> Self {
        Self {
            symbols: SymbolStore::new(),
            terms: TermStore::new(),
            relations: HashMap::new(),
            next_rel_id: 0,
            constraints: builder,
        }
    }

    pub fn with_stores_and_builder(symbols: SymbolStore, terms: TermStore, builder: B) -> Self {
        Self {
            symbols,
            terms,
            relations: HashMap::new(),
            next_rel_id: 0,
            constraints: builder,
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

        let ch = peek_char(input, *pos).unwrap();

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
                if peek_char(input, *pos).unwrap() == ')' {
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
    pub fn parse_rule(&mut self, input: &str) -> Result<NF<B::Constraint>, ParseError> {
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
    fn parse_rule_inner(
        &mut self,
        input: &str,
        pos: &mut usize,
    ) -> Result<NF<B::Constraint>, ParseError> {
        let mut var_map: HashMap<String, u32> = HashMap::new();
        let mut var_order: Vec<u32> = Vec::new();

        // Parse LHS
        let lhs = self.parse_term_inner(input, pos, &mut var_map, &mut var_order)?;

        // Optional constraint block between lhs and arrow.
        skip_whitespace(input, pos);
        let constraint = if *pos < input.len() && peek_char(input, *pos) == Some('{') {
            self.parse_constraint_block(input, pos, &mut var_map, &mut var_order)?
        } else {
            self.constraints.empty_constraint()
        };

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

        Ok(NF::factor(lhs, rhs, constraint, &mut self.terms))
    }

    pub fn parse_theory_def(&mut self, input: &str) -> Result<TheorySummary, ParseError> {
        self.constraints
            .parse_theory_def(input, &mut self.symbols, &mut self.terms)
    }

    fn parse_constraint_block(
        &mut self,
        input: &str,
        pos: &mut usize,
        var_map: &mut HashMap<String, u32>,
        var_order: &mut Vec<u32>,
    ) -> Result<B::Constraint, ParseError> {
        if peek_char(input, *pos) != Some('{') {
            return Err(ParseError {
                message: "Expected '{' to start constraint block".to_string(),
                position: *pos,
            });
        }
        *pos += 1;

        let mut calls = Vec::new();
        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                return Err(ParseError {
                    message: "Unterminated constraint block".to_string(),
                    position: *pos,
                });
            }
            if peek_char(input, *pos) == Some('}') {
                *pos += 1;
                break;
            }

            let call_pos = *pos;
            let (name, args) = self.parse_constraint_call(input, pos, var_map, var_order)?;
            calls.push(ConstraintCall {
                name,
                args,
                position: call_pos,
            });

            skip_whitespace(input, pos);
            if *pos >= input.len() {
                return Err(ParseError {
                    message: "Unterminated constraint block".to_string(),
                    position: *pos,
                });
            }
            match peek_char(input, *pos).unwrap() {
                ',' => {
                    *pos += 1;
                }
                '}' => {
                    *pos += 1;
                    break;
                }
                other => {
                    return Err(ParseError {
                        message: format!("Expected ',' or '}}', found '{}'", other),
                        position: *pos,
                    });
                }
            }
        }

        self.constraints.build_constraint(calls, &mut self.terms)
    }

    fn parse_constraint_call(
        &self,
        input: &str,
        pos: &mut usize,
        var_map: &mut HashMap<String, u32>,
        var_order: &mut Vec<u32>,
    ) -> Result<(String, Vec<TermId>), ParseError> {
        skip_whitespace(input, pos);
        if *pos >= input.len() {
            return Err(ParseError {
                message: "Unexpected end of input".to_string(),
                position: *pos,
            });
        }

        if peek_char(input, *pos) == Some('(') {
            *pos += 1;
            skip_whitespace(input, pos);
            let name = parse_identifier(input, pos)?;
            let mut args = Vec::new();
            loop {
                skip_whitespace(input, pos);
                if *pos >= input.len() {
                    return Err(ParseError {
                        message: "Unclosed constraint term".to_string(),
                        position: *pos,
                    });
                }
                if peek_char(input, *pos).unwrap() == ')' {
                    *pos += 1;
                    break;
                }
                let arg = self.parse_term_inner(input, pos, var_map, var_order)?;
                args.push(arg);
            }
            Ok((name, args))
        } else {
            let name = parse_identifier(input, pos)?;
            Ok((name, Vec::new()))
        }
    }

    /// Parse a relation body (the part inside `rel name { ... }`).
    pub fn parse_rel_body(&mut self, input: &str) -> Result<Rel<B::Constraint>, ParseError> {
        let mut pos = 0;
        let rel = self.parse_or_expr(input, &mut pos)?;
        skip_whitespace(input, &mut pos);
        if pos < input.len() {
            return Err(ParseError {
                message: format!(
                    "Unexpected characters after relation body: '{}'",
                    &input[pos..]
                ),
                position: pos,
            });
        }
        Ok(rel)
    }

    /// Parse an Or expression (lowest precedence).
    fn parse_or_expr(
        &mut self,
        input: &str,
        pos: &mut usize,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        self.parse_or_expr_impl(input, pos, None)
    }

    /// Parse an Or expression, optionally stopping at a given character.
    fn parse_or_expr_impl(
        &mut self,
        input: &str,
        pos: &mut usize,
        stop_char: Option<char>,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        let mut left = self.parse_seq_expr_impl(input, pos, stop_char)?;

        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                break;
            }
            let ch = peek_char(input, *pos).unwrap();
            if stop_char == Some(ch) || ch != '|' {
                break;
            }
            *pos += 1;
            let right = self.parse_seq_expr_impl(input, pos, stop_char)?;
            left = Rel::Or(Arc::new(left), Arc::new(right));
        }

        Ok(left)
    }

    /// Parse a Seq expression, optionally stopping at a given character.
    fn parse_seq_expr_impl(
        &mut self,
        input: &str,
        pos: &mut usize,
        stop_char: Option<char>,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        let mut factors: Vec<Arc<Rel<B::Constraint>>> = Vec::new();
        factors.push(Arc::new(self.parse_and_expr_impl(input, pos, stop_char)?));

        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                break;
            }
            let ch = peek_char(input, *pos).unwrap();
            if stop_char == Some(ch) || ch == '|' || ch != ';' {
                break;
            }
            *pos += 1;
            factors.push(Arc::new(self.parse_and_expr_impl(input, pos, stop_char)?));
        }

        if factors.len() == 1 {
            Ok(unwrap_or_clone(factors.pop().unwrap()))
        } else {
            Ok(Rel::Seq(Arc::from(factors)))
        }
    }

    /// Parse an And expression, optionally stopping at a given character.
    fn parse_and_expr_impl(
        &mut self,
        input: &str,
        pos: &mut usize,
        stop_char: Option<char>,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        let mut left = self.parse_primary_impl(input, pos, stop_char)?;

        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                break;
            }
            let ch = peek_char(input, *pos).unwrap();
            if stop_char == Some(ch) || ch == '|' || ch == ';' || ch != '&' {
                break;
            }
            *pos += 1;
            let right = self.parse_primary_impl(input, pos, stop_char)?;
            left = Rel::And(Arc::new(left), Arc::new(right));
        }

        Ok(left)
    }

    /// Parse a primary expression (rule, call, or bracketed expr).
    fn parse_primary_impl(
        &mut self,
        input: &str,
        pos: &mut usize,
        stop_char: Option<char>,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        skip_whitespace(input, pos);

        if *pos >= input.len() {
            return Err(ParseError {
                message: "Unexpected end of input".to_string(),
                position: *pos,
            });
        }

        let ch = peek_char(input, *pos).unwrap();

        if stop_char == Some(ch) {
            return Err(ParseError {
                message: format!("Unexpected '{}'", ch),
                position: *pos,
            });
        }

        if ch == '[' {
            // Bracketed sequence
            *pos += 1;
            let inner = self.parse_or_expr_impl(input, pos, Some(']'))?;
            skip_whitespace(input, pos);
            if *pos >= input.len() || peek_char(input, *pos).unwrap() != ']' {
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
            let nf = NF::factor(term, term, self.constraints.empty_constraint(), &mut self.terms);
            Ok(Rel::Atom(Arc::new(nf)))
        } else if ch == '$' || ch == '(' {
            // Rule starting with term
            let rule = self.parse_rule_inner(input, pos)?;
            Ok(Rel::Atom(Arc::new(rule)))
        } else if ch.is_ascii_lowercase() {
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
    pub fn parse_rel_def(
        &mut self,
        input: &str,
    ) -> Result<(String, Rel<B::Constraint>), ParseError> {
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
        if pos >= input.len() || peek_char(input, pos).unwrap() != '{' {
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
        if pos >= input.len() || peek_char(input, pos).unwrap() != '}' {
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
    fn parse_rel_body_until_brace(
        &mut self,
        input: &str,
        pos: &mut usize,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        self.parse_or_expr_impl(input, pos, Some('}'))
    }
}

impl Parser<ChrConstraintBuilder> {
    pub fn with_chr() -> Self {
        Parser::with_builder(ChrConstraintBuilder::new())
    }
}

impl Default for Parser<NoConstraintBuilder> {
    fn default() -> Self {
        Self::new()
    }
}

fn peek_char(input: &str, pos: usize) -> Option<char> {
    input.as_bytes().get(pos).copied().map(|byte| byte as char)
}

fn unwrap_or_clone<T: Clone>(arc: Arc<T>) -> T {
    Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone())
}

/// Skip whitespace and comments.
fn skip_whitespace(input: &str, pos: &mut usize) {
    while *pos < input.len() {
        let ch = peek_char(input, *pos).unwrap();
        if ch.is_ascii_whitespace() {
            *pos += 1;
        } else if ch == '#' {
            // Comment - skip to end of line
            while *pos < input.len() && peek_char(input, *pos).unwrap() != '\n' {
                *pos += 1;
            }
        } else {
            break;
        }
    }
}

fn parse_chr_theory(
    input: &str,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    terms: &mut TermStore,
) -> Result<TheorySummary, ParseError> {
    let mut pos = 0;
    skip_whitespace(input, &mut pos);
    if !input[pos..].starts_with("theory") {
        return Err(ParseError {
            message: "Expected 'theory' keyword".to_string(),
            position: pos,
        });
    }
    pos += "theory".len();
    skip_whitespace(input, &mut pos);
    let name = parse_identifier(input, &mut pos)?;

    skip_whitespace(input, &mut pos);
    if peek_char(input, pos) != Some('{') {
        return Err(ParseError {
            message: "Expected '{'".to_string(),
            position: pos,
        });
    }
    pos += 1;

    let body_start = pos;
    let mut depth = 1;
    while pos < input.len() {
        match peek_char(input, pos).unwrap() {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            _ => {}
        }
        pos += 1;
    }
    if depth != 0 {
        return Err(ParseError {
            message: "Unterminated theory block".to_string(),
            position: pos,
        });
    }
    let body_end = pos;
    let body = &input[body_start..body_end];

    let mut predicates = 0usize;
    let mut rules = 0usize;

    for raw_line in body.lines() {
        let line = match raw_line.split_once('#') {
            Some((before, _)) => before.trim(),
            None => raw_line.trim(),
        };
        if line.is_empty() {
            continue;
        }
        let line = line.strip_suffix('.').unwrap_or(line).trim();
        if line.starts_with("constraint ") {
            let decl = line["constraint".len()..].trim();
            let (pred, arity) = decl
                .split_once('/')
                .ok_or_else(|| ParseError {
                    message: "Expected constraint declaration like name/arity".to_string(),
                    position: 0,
                })?;
            let pred = pred.trim();
            let arity: u8 = arity
                .trim()
                .parse()
                .map_err(|_| ParseError {
                    message: "Invalid constraint arity".to_string(),
                    position: 0,
                })?;
            if builder.pred_id(pred).is_some() {
                return Err(ParseError {
                    message: format!("Duplicate constraint predicate '{}'", pred),
                    position: 0,
                });
            }
            builder.pred(pred, arity, Vec::new());
            predicates += 1;
            continue;
        }

        parse_chr_rule_line(line, builder, symbols, terms)?;
        rules += 1;
    }

    Ok(TheorySummary {
        name,
        predicates,
        rules,
    })
}

fn parse_chr_rule_line(
    line: &str,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    terms: &mut TermStore,
) -> Result<(), ParseError> {
    let op = if let Some(idx) = find_top_level_token(line, "<=>") {
        (idx, "<=>")
    } else if let Some(idx) = find_top_level_token(line, "==>") {
        (idx, "==>")
    } else {
        return Err(ParseError {
            message: "Expected '<=>' or '==>' in CHR rule".to_string(),
            position: 0,
        });
    };

    let (lhs, rhs) = line.split_at(op.0);
    let rhs = rhs[op.1.len()..].trim();
    let lhs = lhs.trim();

    let (kept, removed) = match op.1 {
        "==>" => (lhs, ""),
        "<=>" => {
            if let Some(idx) = find_top_level_token(lhs, "\\") {
                let (k, r) = lhs.split_at(idx);
                (k.trim(), r[1..].trim())
            } else {
                ("", lhs)
            }
        }
        _ => ("", ""),
    };

    if op.1 == "==>" && find_top_level_token(lhs, "\\").is_some() {
        return Err(ParseError {
            message: "Propagation rules cannot use \\".to_string(),
            position: 0,
        });
    }

    let mut rvars = HashMap::new();
    let kept_heads = parse_chr_head_list(kept, builder, symbols, &mut rvars)?;
    let removed_heads = parse_chr_head_list(removed, builder, symbols, &mut rvars)?;
    let (guard_src, body_src) = if let Some(idx) = find_top_level_token(rhs, "|") {
        let (g, b) = rhs.split_at(idx);
        (g.trim(), b[1..].trim())
    } else {
        ("", rhs)
    };
    if !guard_src.is_empty() && body_src.is_empty() {
        return Err(ParseError {
            message: "CHR guard must be followed by a body".to_string(),
            position: 0,
        });
    }

    let guard = parse_chr_guard(guard_src, builder, symbols, terms, &rvars)?;
    let body = parse_chr_body(body_src, builder, symbols, &mut rvars)?;

    builder.rule(kept_heads, removed_heads, guard, body, 0);
    Ok(())
}

fn parse_chr_head_list(
    input: &str,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    rvars: &mut HashMap<String, RVar>,
) -> Result<Vec<HeadPat>, ParseError> {
    let input = input.trim();
    if input.is_empty() {
        return Ok(Vec::new());
    }
    let parts = split_top_level_commas(input);
    let mut heads = Vec::new();
    for part in parts {
        let (pred, args) = parse_chr_constraint(part, builder, symbols, rvars)?;
        heads.push(HeadPat::new(pred, args));
    }
    Ok(heads)
}

fn parse_chr_body(
    input: &str,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    rvars: &mut HashMap<String, RVar>,
) -> Result<BodyProg, ParseError> {
    let input = input.trim();
    if input.is_empty() || input == "." || input == "true" {
        return Ok(BodyProg::new(Vec::new()));
    }
    if input == "fail" {
        return Ok(BodyProg::new(vec![BodyInstr::Fail]));
    }

    let parts = split_top_level_commas(input);
    let mut instrs = Vec::new();
    for part in parts {
        let (pred, args) = parse_chr_constraint(part, builder, symbols, rvars)?;
        let arg_exprs: Vec<ArgExpr> = args.into_iter().map(ArgExpr::Pat).collect();
        instrs.push(BodyInstr::AddChr {
            pred,
            args: arg_exprs.into_boxed_slice(),
        });
    }
    Ok(BodyProg::new(instrs))
}

fn parse_chr_guard(
    input: &str,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    terms: &mut TermStore,
    rvars: &HashMap<String, RVar>,
) -> Result<GuardProg, ParseError> {
    let input = input.trim();
    if input.is_empty() || input == "." || input == "true" {
        return Ok(GuardProg::empty());
    }

    let parts = split_top_level_commas(input);
    let mut instrs = Vec::new();
    for part in parts {
        instrs.push(parse_chr_guard_call(part, builder, symbols, terms, rvars)?);
    }
    Ok(GuardProg::new(instrs))
}

fn parse_chr_guard_call(
    input: &str,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    terms: &mut TermStore,
    rvars: &HashMap<String, RVar>,
) -> Result<GuardInstr, ParseError> {
    let mut pos = 0;
    skip_whitespace(input, &mut pos);
    if peek_char(input, pos) != Some('(') {
        return Err(ParseError {
            message: "Expected guard call like (eq $x z)".to_string(),
            position: pos,
        });
    }
    pos += 1;
    skip_whitespace(input, &mut pos);
    let name = parse_identifier(input, &mut pos)?;

    let instr = match name.as_str() {
        "eq" | "neq" => {
            let left = parse_chr_guard_val(input, &mut pos, symbols, terms, rvars)?;
            let right = parse_chr_guard_val(input, &mut pos, symbols, terms, rvars)?;
            skip_whitespace(input, &mut pos);
            if peek_char(input, pos) != Some(')') {
                return Err(ParseError {
                    message: "Expected ')' after guard arguments".to_string(),
                    position: pos,
                });
            }
            pos += 1;
            if name == "eq" {
                GuardInstr::Eq(left, right)
            } else {
                GuardInstr::Neq(left, right)
            }
        }
        "top" => {
            let target = parse_chr_guard_val(input, &mut pos, symbols, terms, rvars)?;
            skip_whitespace(input, &mut pos);
            let functor = parse_identifier(input, &mut pos)?;
            skip_whitespace(input, &mut pos);
            let arity_str = parse_identifier(input, &mut pos)?;
            let arity: u8 = arity_str.parse().map_err(|_| ParseError {
                message: "Invalid arity in top guard".to_string(),
                position: pos,
            })?;
            skip_whitespace(input, &mut pos);
            if peek_char(input, pos) != Some(')') {
                return Err(ParseError {
                    message: "Expected ')' after guard arguments".to_string(),
                    position: pos,
                });
            }
            pos += 1;
            GuardInstr::TopFunctor {
                t: target,
                f: symbols.intern(&functor),
                arity,
            }
        }
        "match" => {
            let pat = parse_chr_pat_term_bound(input, &mut pos, builder, symbols, rvars)?;
            let target = parse_chr_guard_val(input, &mut pos, symbols, terms, rvars)?;
            skip_whitespace(input, &mut pos);
            if peek_char(input, pos) != Some(')') {
                return Err(ParseError {
                    message: "Expected ')' after guard arguments".to_string(),
                    position: pos,
                });
            }
            pos += 1;
            GuardInstr::MatchPat { pat, t: target }
        }
        _ => {
            return Err(ParseError {
                message: format!("Unknown guard predicate '{}'", name),
                position: pos,
            });
        }
    };

    skip_whitespace(input, &mut pos);
    if pos < input.len() {
        return Err(ParseError {
            message: "Unexpected trailing characters in guard".to_string(),
            position: pos,
        });
    }
    Ok(instr)
}

fn parse_chr_guard_val(
    input: &str,
    pos: &mut usize,
    symbols: &mut SymbolStore,
    terms: &mut TermStore,
    rvars: &HashMap<String, RVar>,
) -> Result<GVal, ParseError> {
    skip_whitespace(input, pos);
    if *pos >= input.len() {
        return Err(ParseError {
            message: "Unexpected end of input".to_string(),
            position: *pos,
        });
    }
    let ch = peek_char(input, *pos).unwrap();
    if ch == '$' {
        *pos += 1;
        let name = parse_identifier(input, pos)?;
        let rv = rvars.get(&name).ok_or_else(|| ParseError {
            message: format!("Guard variable '${}' must be bound by a head", name),
            position: *pos,
        })?;
        Ok(GVal::RVar(*rv))
    } else {
        let term = parse_chr_const_term(input, pos, symbols, terms)?;
        Ok(GVal::Const(term))
    }
}

fn parse_chr_const_term(
    input: &str,
    pos: &mut usize,
    symbols: &mut SymbolStore,
    terms: &mut TermStore,
) -> Result<TermId, ParseError> {
    skip_whitespace(input, pos);
    if *pos >= input.len() {
        return Err(ParseError {
            message: "Unexpected end of input".to_string(),
            position: *pos,
        });
    }
    let ch = peek_char(input, *pos).unwrap();
    if ch == '$' {
        return Err(ParseError {
            message: "Guard constants cannot include rule variables".to_string(),
            position: *pos,
        });
    }
    if ch == '(' {
        *pos += 1;
        skip_whitespace(input, pos);
        let functor = parse_identifier(input, pos)?;
        let func = symbols.intern(&functor);
        let mut kids: SmallVec<[TermId; 4]> = SmallVec::new();
        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                return Err(ParseError {
                    message: "Unclosed parenthesis".to_string(),
                    position: *pos,
                });
            }
            if peek_char(input, *pos).unwrap() == ')' {
                *pos += 1;
                break;
            }
            kids.push(parse_chr_const_term(input, pos, symbols, terms)?);
        }
        Ok(terms.app(func, kids))
    } else if ch.is_ascii_lowercase() || ch.is_ascii_digit() {
        let name = parse_identifier(input, pos)?;
        let func = symbols.intern(&name);
        Ok(terms.app0(func))
    } else {
        Err(ParseError {
            message: format!("Unexpected character: '{}'", ch),
            position: *pos,
        })
    }
}

fn parse_chr_constraint(
    input: &str,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    rvars: &mut HashMap<String, RVar>,
) -> Result<(PredId, Vec<PatId>), ParseError> {
    let mut pos = 0;
    skip_whitespace(input, &mut pos);
    let (name, args) = if peek_char(input, pos) == Some('(') {
        pos += 1;
        skip_whitespace(input, &mut pos);
        let name = parse_identifier(input, &mut pos)?;
        let mut args = Vec::new();
        loop {
            skip_whitespace(input, &mut pos);
            if pos >= input.len() {
                return Err(ParseError {
                    message: "Unclosed constraint term".to_string(),
                    position: pos,
                });
            }
            if peek_char(input, pos) == Some(')') {
                pos += 1;
                break;
            }
            args.push(parse_chr_pat_term(input, &mut pos, builder, symbols, rvars)?);
        }
        (name, args)
    } else {
        (parse_identifier(input, &mut pos)?, Vec::new())
    };

    skip_whitespace(input, &mut pos);
    if pos < input.len() {
        return Err(ParseError {
            message: "Unexpected trailing characters in constraint".to_string(),
            position: pos,
        });
    }

    let pred = builder.pred_id(&name).ok_or_else(|| ParseError {
        message: format!("Unknown constraint predicate '{}'", name),
        position: 0,
    })?;
    let expected = builder
        .pred_arity(pred)
        .map(|a| a as usize)
        .unwrap_or(0);
    if args.len() != expected {
        return Err(ParseError {
            message: format!(
                "Constraint '{}' arity {} expects {} args, got {}",
                name,
                expected,
                expected,
                args.len()
            ),
            position: 0,
        });
    }
    Ok((pred, args))
}

/// Mode for parsing CHR pattern terms.
enum PatVarMode<'a> {
    /// Create new variables if not found in the map.
    Create(&'a mut HashMap<String, RVar>),
    /// Only allow existing bound variables (for guards).
    BoundOnly(&'a HashMap<String, RVar>),
}

fn parse_chr_pat_term_impl(
    input: &str,
    pos: &mut usize,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    mode: &mut PatVarMode<'_>,
) -> Result<PatId, ParseError> {
    skip_whitespace(input, pos);
    if *pos >= input.len() {
        return Err(ParseError {
            message: "Unexpected end of input".to_string(),
            position: *pos,
        });
    }
    let ch = peek_char(input, *pos).unwrap();
    if ch == '$' {
        *pos += 1;
        let name = parse_identifier(input, pos)?;
        let rv = match mode {
            PatVarMode::Create(rvars) => {
                let next_id = rvars.len() as u32;
                *rvars.entry(name).or_insert(RVar(next_id))
            }
            PatVarMode::BoundOnly(rvars) => {
                *rvars.get(&name).ok_or_else(|| ParseError {
                    message: format!("Guard variable '${}' must be bound by a head", name),
                    position: *pos,
                })?
            }
        };
        Ok(builder.pat_var(rv))
    } else if ch == '(' {
        *pos += 1;
        skip_whitespace(input, pos);
        let functor = parse_identifier(input, pos)?;
        let sym = symbols.intern(&functor);
        let mut kids = Vec::new();
        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                return Err(ParseError {
                    message: "Unclosed parenthesis".to_string(),
                    position: *pos,
                });
            }
            if peek_char(input, *pos).unwrap() == ')' {
                *pos += 1;
                break;
            }
            kids.push(parse_chr_pat_term_impl(input, pos, builder, symbols, mode)?);
        }
        Ok(builder.pat_app(sym, kids))
    } else if ch.is_ascii_lowercase() || ch.is_ascii_digit() {
        let name = parse_identifier(input, pos)?;
        let sym = symbols.intern(&name);
        Ok(builder.pat_app(sym, Vec::new()))
    } else {
        Err(ParseError {
            message: format!("Unexpected character: '{}'", ch),
            position: *pos,
        })
    }
}

fn parse_chr_pat_term(
    input: &str,
    pos: &mut usize,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    rvars: &mut HashMap<String, RVar>,
) -> Result<PatId, ParseError> {
    parse_chr_pat_term_impl(input, pos, builder, symbols, &mut PatVarMode::Create(rvars))
}

fn parse_chr_pat_term_bound(
    input: &str,
    pos: &mut usize,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    rvars: &HashMap<String, RVar>,
) -> Result<PatId, ParseError> {
    parse_chr_pat_term_impl(input, pos, builder, symbols, &mut PatVarMode::BoundOnly(rvars))
}

fn split_top_level_commas(input: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    for (idx, ch) in input.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => {
                parts.push(input[start..idx].trim());
                start = idx + 1;
            }
            _ => {}
        }
    }
    if start < input.len() {
        parts.push(input[start..].trim());
    }
    parts.into_iter().filter(|p| !p.is_empty()).collect()
}

fn find_top_level_token(input: &str, token: &str) -> Option<usize> {
    let mut depth = 0i32;
    let mut idx = 0usize;
    while idx + token.len() <= input.len() {
        let ch = peek_char(input, idx).unwrap();
        if ch == '(' {
            depth += 1;
        } else if ch == ')' {
            depth -= 1;
        }
        if depth == 0 && input[idx..].starts_with(token) {
            return Some(idx);
        }
        idx += 1;
    }
    None
}

/// Parse an identifier (lowercase letters, digits, underscores).
fn parse_identifier(input: &str, pos: &mut usize) -> Result<String, ParseError> {
    let start = *pos;
    while *pos < input.len() {
        let ch = peek_char(input, *pos).unwrap();
        if ch.is_ascii_alphanumeric() || ch == '_' {
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
        assert_eq!(nf.drop_fresh.in_arity, 1);
        assert_eq!(nf.drop_fresh.out_arity, 2);
        assert_eq!(nf.drop_fresh.map.as_slice(), &[(0, 0)]);
    }

    #[test]
    fn parse_rule_lhs_only_variable_is_dropped() {
        let mut parser = Parser::new();
        let nf = parser
            .parse_rule("(f $x $y) -> $x")
            .expect("parse rule with lhs-only variable");
        assert_eq!(nf.drop_fresh.in_arity, 2);
        assert_eq!(nf.drop_fresh.out_arity, 1);
        assert_eq!(nf.drop_fresh.map.as_slice(), &[(0, 0)]);
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

    #[test]
    fn theory_parsing_allows_constraints_in_rules() {
        let mut parser = Parser::with_chr();
        let theory = r#"
theory eq {
  constraint eq/2
  (eq $x $x) <=> .
}
"#;
        parser.parse_theory_def(theory).expect("parse theory");
        let nf = parser
            .parse_rule("(pair $x $y) { (eq $x $y) } -> $x")
            .expect("parse rule with constraint");

        assert_eq!(nf.drop_fresh.constraint.store.alive_count, 1);
        let pred = nf
            .drop_fresh
            .constraint
            .program
            .pred_id("eq")
            .expect("eq predicate id");
        let inst = nf
            .drop_fresh
            .constraint
            .store
            .inst
            .iter()
            .find(|c| c.alive)
            .expect("alive constraint");
        assert_eq!(inst.pred, pred);
    }

    #[test]
    fn constraint_with_unknown_predicate_fails() {
        let mut parser = Parser::with_chr();
        let theory = r#"
theory eq {
  constraint eq/2
  (eq $x $x) <=> .
}
"#;
        parser.parse_theory_def(theory).expect("parse theory");
        let err = match parser.parse_rule("$x { (neq $x $x) } -> $x") {
            Ok(_) => panic!("expected unknown predicate error"),
            Err(err) => err,
        };
        assert!(
            err.message.contains("unknown constraint"),
            "unexpected error: {}",
            err
        );
    }

    #[test]
    fn theory_fail_body_makes_constraint_unsat() {
        let mut parser = Parser::with_chr();
        let theory = r#"
theory bad {
  constraint bad/0
  bad <=> fail.
}
"#;
        parser.parse_theory_def(theory).expect("parse theory");
        let nf = parser
            .parse_rule("$x { bad } -> $x")
            .expect("parse rule with fail constraint");
        let mut terms = parser.take_terms();
        let result = nf.drop_fresh.constraint.normalize(&mut terms);
        assert!(result.is_none(), "expected failure from bad constraint");
    }

    #[test]
    fn theory_parses_propagation_and_simpagation_rules() {
        let mut parser = Parser::with_chr();
        let theory = r#"
theory t {
  constraint p/1
  constraint q/1
  constraint r/1
  (p $x) ==> (q $x).
  (p $x) \ (q $x) <=> (r $x).
}
"#;
        parser
            .parse_theory_def(theory)
            .expect("parse propagation and simpagation");
    }

    #[test]
    fn theory_parses_guard_and_applies_it() {
        let mut parser = Parser::with_chr();
        let theory = r#"
theory guards {
  constraint p/1
  constraint q/1
  (p $x) <=> (eq $x z) | (q $x).
}
"#;
        parser.parse_theory_def(theory).expect("parse theory");
        let nf = parser
            .parse_rule("z { (p z) } -> z")
            .expect("parse rule with guard");

        let mut terms = parser.take_terms();
        let (normalized, _) = nf
            .drop_fresh
            .constraint
            .normalize(&mut terms)
            .expect("normalize constraints");

        let q = normalized.program.pred_id("q").expect("q predicate id");
        let count = normalized
            .store
            .inst
            .iter()
            .filter(|c| c.alive && c.pred == q)
            .count();
        assert_eq!(count, 1, "Expected guard to add q(z)");
    }

    #[test]
    fn constraint_arity_mismatch_fails() {
        let mut parser = Parser::with_chr();
        let theory = r#"
theory eq {
  constraint eq/2
  (eq $x $x) <=> .
}
"#;
        parser.parse_theory_def(theory).expect("parse theory");
        let err = match parser.parse_rule("$x { (eq $x) } -> $x") {
            Ok(_) => panic!("expected arity mismatch error"),
            Err(err) => err,
        };
        assert!(
            err.message.contains("arity"),
            "unexpected error: {}",
            err
        );
    }

    #[test]
    fn format_nf_includes_constraints() {
        let mut parser = Parser::with_chr();
        let theory = r#"
theory eq {
  constraint eq/2
  (eq $x $x) <=> .
}
"#;
        parser.parse_theory_def(theory).expect("parse theory");
        let nf = parser
            .parse_rule("(pair $x $y) { (eq $x $y) } -> $x")
            .expect("parse rule with constraint");
        let mut terms = parser.take_terms();
        let rendered = crate::nf::format_nf(&nf, &mut terms, parser.symbols())
            .expect("format nf");
        assert!(
            rendered.contains("{ (eq $0 $1) }"),
            "expected constraints in output, got: {}",
            rendered
        );
    }

    // ========================================================================
    // SIZE AND MEMORY TESTS
    // ========================================================================

    #[test]
    fn parser_size_reasonable() {
        use std::mem::size_of;
        let size = size_of::<Parser>();
        // Parser contains SymbolStore, TermStore, and HashMap<String, RelId>
        assert!(
            size < 1000,
            "Parser should not be excessively large, got {}",
            size
        );
    }

    #[test]
    fn parse_error_size_reasonable() {
        use std::mem::size_of;
        let size = size_of::<ParseError>();
        assert!(
            size < 100,
            "ParseError should not be excessively large, got {}",
            size
        );
    }
}
