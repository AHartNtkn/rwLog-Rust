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
    ArgExpr, BodyInstr, BodyProg, BuiltinId, ChrProgram, ChrProgramBuilder, ChrState, GVal,
    GuardInstr, GuardProg, HeadPat, PatId, PredId, RVar,
};
use crate::constraint::ConstraintOps;
use crate::nf::NF;
use crate::rel::{Rel, RelId};
use crate::symbol::SymbolStore;
use crate::term::{TermId, TermStore};
use smallvec::SmallVec;
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

/// Outcome of parsing a `rel` definition.
#[derive(Debug)]
pub enum RelDef<C> {
    /// A named relation was defined.
    Relation(String, Rel<C>),
    /// A macro was defined (name, arity).
    Macro(String, usize),
}

impl<C> RelDef<C> {
    /// Unwrap as a `(name, rel)` pair, panicking if this is a macro.
    pub fn into_relation(self) -> (String, Rel<C>) {
        match self {
            RelDef::Relation(name, rel) => (name, rel),
            RelDef::Macro(name, arity) => {
                panic!("expected Relation, got Macro({name}/{arity})")
            }
        }
    }
}

type RelDefResult<C> = Result<RelDef<C>, ParseError>;

/// Result of matching a macro equation: (rel_subst, term_subst).
type EquationMatch<C> = (HashMap<RelId, Rel<C>>, crate::subst::Subst);

/// Whether a macro parameter is a relation (substituted) or a term (pattern-matched).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ParamKind {
    Relation,
    Term,
}

/// A single equation in a multi-equation macro definition.
///
/// For `rel fmap(@(sum $a $b), f) { ... }`:
/// - `term_patterns[0]` = Some(TermId for `(sum $a $b)`), `term_patterns[1]` = None
/// - `rel_params` = [("f", <RelId>)]
/// - `body` = the parsed Rel tree
#[derive(Clone)]
struct MacroEquation<C> {
    /// For each param position: Some(pattern) for Term params, None for Relation params.
    term_patterns: Vec<Option<TermId>>,
    /// Relation-kind parameters: (name, placeholder RelId).
    rel_params: Vec<(String, RelId)>,
    /// The macro body as a Rel tree.
    body: Rel<C>,
    /// RelId used for recursive self-references in this equation's body.
    self_id: RelId,
}

/// A stored macro definition, potentially with multiple equations for pattern dispatch.
///
/// The first definition establishes `param_kinds`; subsequent definitions must match.
struct MacroDef<C> {
    param_kinds: Vec<ParamKind>,
    equations: Vec<MacroEquation<C>>,
}

/// Tracks the macro currently being parsed, so the body parser can recognize
/// parameter names, recursive self-calls, and meta-variable references.
struct CurrentMacro {
    name: String,
    arity: usize,
    param_kinds: Vec<ParamKind>,
    self_id: RelId,
    rel_params: Vec<(String, RelId)>,
    /// Meta-variable names from term patterns, for use by parse_macro_term_arg.
    meta_vars: HashMap<String, u32>,
    /// Term patterns for each Term-kind param (used for identity self-call check).
    term_patterns: Vec<Option<TermId>>,
}

/// A macro argument: either a relation expression or a term.
#[derive(Clone, Debug)]
enum MacroArg<C> {
    Rel(Rel<C>),
    Term(TermId),
}

/// A macro call whose definition wasn't available at parse time.
/// Stored in the Rel tree as `Call(pending_id)` and resolved after all
/// definitions in a batch are parsed.
#[derive(Clone)]
struct PendingMacroCall<C> {
    name: String,
    arity: usize,
    args: Vec<MacroArg<C>>,
}

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
    builder: ChrProgramBuilder,
    program: Arc<ChrProgram>,
}

impl ChrConstraintBuilder {
    pub fn new() -> Self {
        let builder = ChrProgramBuilder::new();
        let program = builder.clone().build();
        Self { builder, program }
    }

    pub fn program(&self) -> Arc<ChrProgram> {
        self.program.clone()
    }
}

impl Default for ChrConstraintBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl ConstraintBuilder for ChrConstraintBuilder {
    type Constraint = ChrState;

    fn empty_constraint(&self) -> Self::Constraint {
        ChrState::new(self.program.clone())
    }

    fn build_constraint(
        &mut self,
        calls: Vec<ConstraintCall>,
        terms: &mut TermStore,
    ) -> Result<Self::Constraint, ParseError> {
        let mut st = ChrState::new(self.program.clone());
        for call in calls {
            let pred = self.program.pred_id(&call.name).ok_or_else(|| ParseError {
                message: format!("unknown constraint predicate '{}'", call.name),
                position: call.position,
            })?;
            let expected = self.program.preds[pred.0 as usize].arity as usize;
            if call.args.len() != expected {
                return Err(ParseError {
                    message: format!(
                        "constraint '{}' expects {} args, got {}",
                        call.name,
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
    /// Macro definitions keyed by (name, arity).
    macro_defs: HashMap<(String, usize), MacroDef<B::Constraint>>,
    /// The macro currently being parsed (if any).
    current_macro: Option<CurrentMacro>,
    /// Known macro signatures (name, arity) -> param_kinds, registered before bodies are parsed.
    /// Used to recognize `name(...)` as macro call syntax during forward references.
    macro_signatures: HashMap<(String, usize), Vec<ParamKind>>,
    /// Current macro expansion depth (for detecting non-structural recursion).
    expansion_depth: usize,
    /// Macro calls whose definitions weren't available at parse time.
    /// Keyed by a placeholder RelId used in the Rel tree as `Call(id)`.
    pending_macro_calls: HashMap<RelId, PendingMacroCall<B::Constraint>>,
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
        Self::from_parts(SymbolStore::new(), TermStore::new(), NoConstraintBuilder)
    }

    /// Create a parser with existing symbol and term stores.
    pub fn with_stores(symbols: SymbolStore, terms: TermStore) -> Self {
        Self::from_parts(symbols, terms, NoConstraintBuilder)
    }
}

impl<B: ConstraintBuilder> Parser<B> {
    fn from_parts(symbols: SymbolStore, terms: TermStore, constraints: B) -> Self {
        Self {
            symbols,
            terms,
            relations: HashMap::new(),
            next_rel_id: 0,
            constraints,
            macro_defs: HashMap::new(),
            current_macro: None,
            macro_signatures: HashMap::new(),
            expansion_depth: 0,
            pending_macro_calls: HashMap::new(),
        }
    }

    pub fn with_builder(builder: B) -> Self {
        Self::from_parts(SymbolStore::new(), TermStore::new(), builder)
    }

    pub fn with_stores_and_builder(symbols: SymbolStore, terms: TermStore, builder: B) -> Self {
        Self::from_parts(symbols, terms, builder)
    }

    fn alloc_rel_id(&mut self) -> RelId {
        let id = self.next_rel_id;
        self.next_rel_id += 1;
        id
    }

    /// Names and arities of all defined macros.
    pub fn macro_names(&self) -> Vec<(String, usize)> {
        self.macro_defs
            .keys()
            .map(|(name, arity)| (name.clone(), *arity))
            .collect()
    }

    /// Pre-scan a batch of statements and register all macro signatures
    /// (name + arity + param_kinds) so that forward references parse correctly.
    /// Call this before parsing any bodies in the batch.
    /// The first definition for a given (name, arity) establishes param_kinds.
    pub fn scan_macro_signatures(&mut self, statements: &[String]) {
        for stmt in statements {
            let trimmed = stmt.trim();
            if let Some(after_rel) = trimmed.strip_prefix("rel ") {
                if let Some((name, arity, kinds)) = extract_macro_signature(after_rel) {
                    let key = (name, arity);
                    self.macro_signatures.entry(key).or_insert(kinds);
                }
            }
        }
    }

    /// Resolve all pending macro calls in a Rel tree. Returns an error if
    /// any referenced macro is still undefined after all definitions.
    pub fn resolve_pending(
        &mut self,
        rel: Rel<B::Constraint>,
    ) -> Result<Rel<B::Constraint>, String> {
        self.resolve_pending_inner(rel, &HashMap::new(), None)
    }

    /// Inner resolution: walks a Rel tree replacing `Call(pending_id)` nodes
    /// with expanded macros. `outer_subst` is the Rel-level substitution applied
    /// to the pending call's Rel args, and `term_subst` is applied to Term args
    /// to resolve meta-variables from an enclosing pattern-matching macro.
    fn resolve_pending_inner(
        &mut self,
        rel: Rel<B::Constraint>,
        outer_subst: &HashMap<RelId, Rel<B::Constraint>>,
        term_subst: Option<&crate::subst::Subst>,
    ) -> Result<Rel<B::Constraint>, String> {
        match rel {
            Rel::Call(id) => {
                if let Some(pending) = self.pending_macro_calls.get(&id).cloned() {
                    // Resolve the pending call's args: apply outer_subst to Rel args,
                    // apply term_subst to Term args.
                    let mut resolved_args: Vec<MacroArg<B::Constraint>> = Vec::new();
                    for arg in &pending.args {
                        match arg {
                            MacroArg::Rel(r) => {
                                let resolved = if outer_subst.is_empty() {
                                    r.clone()
                                } else {
                                    substitute_in_rel(r, outer_subst, RelId::MAX, RelId::MAX)
                                };
                                // Also resolve pending calls within the Rel arg.
                                let resolved =
                                    self.resolve_pending_inner(resolved, outer_subst, term_subst)?;
                                resolved_args.push(MacroArg::Rel(resolved));
                            }
                            MacroArg::Term(tid) => {
                                let resolved_tid = if let Some(ts) = term_subst {
                                    crate::subst::apply_subst(*tid, ts, &mut self.terms)
                                } else {
                                    *tid
                                };
                                resolved_args.push(MacroArg::Term(resolved_tid));
                            }
                        }
                    }

                    let key = (pending.name.clone(), pending.arity);
                    if self.macro_defs.contains_key(&key) {
                        // Expand and recursively resolve the result.
                        let expanded = self
                            .expand_macro_call(&pending.name, pending.arity, resolved_args, 0)
                            .map_err(|e| e.message)?;
                        self.resolve_pending_inner(expanded, outer_subst, term_subst)
                    } else {
                        Err(format!(
                            "undefined macro '{}/{}'",
                            pending.name, pending.arity
                        ))
                    }
                } else {
                    Ok(Rel::Call(id))
                }
            }
            Rel::Zero | Rel::Atom(_) => Ok(rel),
            Rel::Or(a, b) => {
                let a = self.resolve_pending_inner((*a).clone(), outer_subst, term_subst)?;
                let b = self.resolve_pending_inner((*b).clone(), outer_subst, term_subst)?;
                Ok(Rel::Or(Arc::new(a), Arc::new(b)))
            }
            Rel::And(a, b) => {
                let a = self.resolve_pending_inner((*a).clone(), outer_subst, term_subst)?;
                let b = self.resolve_pending_inner((*b).clone(), outer_subst, term_subst)?;
                Ok(Rel::And(Arc::new(a), Arc::new(b)))
            }
            Rel::Seq(xs) => {
                let new_xs: Result<Vec<_>, _> = xs
                    .iter()
                    .map(|x| self.resolve_pending_inner((**x).clone(), outer_subst, term_subst))
                    .collect();
                let new_xs: Vec<Arc<Rel<B::Constraint>>> =
                    new_xs?.into_iter().map(Arc::new).collect();
                Ok(Rel::Seq(Arc::from(new_xs)))
            }
            Rel::Fix(id, body) => {
                let body = self.resolve_pending_inner((*body).clone(), outer_subst, term_subst)?;
                Ok(Rel::Fix(id, Arc::new(body)))
            }
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
        let first = self.parse_and_expr_impl(input, pos, stop_char)?;

        skip_whitespace(input, pos);
        if *pos >= input.len() {
            return Ok(first);
        }
        let ch = peek_char(input, *pos).unwrap();
        if stop_char == Some(ch) || ch == '|' || ch != ';' {
            return Ok(first);
        }

        let mut factors: Vec<Arc<Rel<B::Constraint>>> = vec![Arc::new(first)];
        loop {
            *pos += 1;
            factors.push(Arc::new(self.parse_and_expr_impl(input, pos, stop_char)?));
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                break;
            }
            let ch = peek_char(input, *pos).unwrap();
            if stop_char == Some(ch) || ch == '|' || ch != ';' {
                break;
            }
        }

        Ok(Rel::Seq(Arc::from(factors)))
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
            let nf = NF::factor(
                term,
                term,
                self.constraints.empty_constraint(),
                &mut self.terms,
            );
            Ok(Rel::Atom(Arc::new(nf)))
        } else if ch == '$' || ch == '(' {
            // Rule starting with term
            let rule = self.parse_rule_inner(input, pos)?;
            Ok(Rel::Atom(Arc::new(rule)))
        } else if ch.is_ascii_lowercase() {
            // Could be atom (start of rule), relation call, or macro call.
            let start_pos = *pos;
            let name = parse_identifier(input, pos)?;
            skip_whitespace(input, pos);

            // Check if this is followed by -> or { (making it a rule starting with an atom).
            // A constraint block { ... } between the LHS and -> is valid rule syntax.
            let is_rule = *pos < input.len()
                && (input[*pos..].starts_with("->") || peek_char(input, *pos) == Some('{'));
            if is_rule {
                // It's a rule: restore position and parse as rule
                *pos = start_pos;
                let rule = self.parse_rule_inner(input, pos)?;
                Ok(Rel::Atom(Arc::new(rule)))
            } else if *pos < input.len() && peek_char(input, *pos) == Some('(') {
                // Macro call: name(arg1, arg2, ...)
                self.parse_macro_call(input, pos, &name, start_pos)
            } else {
                // Plain relation call
                if let Some(&rel_id) = self.relations.get(&name) {
                    Ok(Rel::Call(rel_id))
                } else {
                    let rel_id = self.alloc_rel_id();
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
    ///
    /// Returns `Ok(RelDef::Relation(name, rel))` for a plain `rel name { body }`,
    /// or `Ok(RelDef::Macro(name, arity))` for a macro `rel name(p1, ..., pn) { body }`.
    pub fn parse_rel_def(&mut self, input: &str) -> RelDefResult<B::Constraint> {
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

        // Check for parameter list: `(`
        skip_whitespace(input, &mut pos);
        let has_params = pos < input.len() && peek_char(input, pos) == Some('(');

        if has_params {
            return self.parse_macro_def(input, &mut pos, name);
        }

        // Plain relation: register name and parse body.
        let rel_id = if let Some(&id) = self.relations.get(&name) {
            id
        } else {
            let id = self.alloc_rel_id();
            self.relations.insert(name.clone(), id);
            id
        };

        // Expect '{'
        if pos >= input.len() || peek_char(input, pos).unwrap() != '{' {
            return Err(ParseError {
                message: "Expected '{'".to_string(),
                position: pos,
            });
        }
        pos += 1;

        let body = self.parse_rel_body_until_brace(input, &mut pos)?;

        skip_whitespace(input, &mut pos);
        if pos >= input.len() || peek_char(input, pos).unwrap() != '}' {
            return Err(ParseError {
                message: "Expected '}'".to_string(),
                position: pos,
            });
        }

        let rel = Rel::Fix(rel_id, Arc::new(body));
        Ok(RelDef::Relation(name, rel))
    }

    /// Parse a macro definition: the part after `rel name` when `(` was seen.
    ///
    /// Supports `@` prefix on parameters for term-valued (pattern-matched) params.
    /// Multiple definitions with the same name/arity add equations; the first
    /// definition establishes param_kinds.
    fn parse_macro_def(
        &mut self,
        input: &str,
        pos: &mut usize,
        name: String,
    ) -> RelDefResult<B::Constraint> {
        // Consume '('
        *pos += 1;

        // Parse comma-separated parameters, detecting `@` prefix for term params.
        let mut param_kinds: Vec<ParamKind> = Vec::new();
        let mut rel_params: Vec<(String, RelId)> = Vec::new();
        let mut term_patterns: Vec<Option<TermId>> = Vec::new();

        // Shared var_map/var_order for all term patterns in this equation,
        // so meta-vars across patterns share a namespace.
        let mut term_var_map: HashMap<String, u32> = HashMap::new();
        let mut term_var_order: Vec<u32> = Vec::new();

        let mut param_count = 0;
        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                return Err(ParseError {
                    message: "Unterminated macro parameter list".to_string(),
                    position: *pos,
                });
            }
            if peek_char(input, *pos) == Some(')') {
                *pos += 1;
                break;
            }
            if param_count > 0 {
                if peek_char(input, *pos) != Some(',') {
                    return Err(ParseError {
                        message: "Expected ',' between macro parameters".to_string(),
                        position: *pos,
                    });
                }
                *pos += 1;
                skip_whitespace(input, pos);
            }

            // Detect `@` prefix for term-valued parameters.
            if peek_char(input, *pos) == Some('@') {
                *pos += 1;
                param_kinds.push(ParamKind::Term);
                // Parse the term pattern (may contain meta-vars like `$a`).
                let pattern =
                    self.parse_term_inner(input, pos, &mut term_var_map, &mut term_var_order)?;
                term_patterns.push(Some(pattern));
                // No relation param for term positions.
            } else {
                param_kinds.push(ParamKind::Relation);
                let param_name = parse_identifier(input, pos)?;
                let param_id = self.alloc_rel_id();
                rel_params.push((param_name, param_id));
                term_patterns.push(None);
            }
            param_count += 1;
        }

        if param_count == 0 {
            return Err(ParseError {
                message: "Macro parameter list cannot be empty (use `rel name { ... }` instead)"
                    .to_string(),
                position: *pos,
            });
        }

        // Build meta_vars from term_var_map.
        let meta_vars = term_var_map;

        let arity = param_kinds.len();
        let self_id = self.alloc_rel_id();
        let key = (name.clone(), arity);

        // Validate param_kinds match any existing definition.
        if let Some(existing) = self.macro_defs.get(&key) {
            if existing.param_kinds != param_kinds {
                return Err(ParseError {
                    message: format!(
                        "macro '{}/{}': parameter kinds (@-positions) must match \
                         across all equations",
                        name, arity,
                    ),
                    position: *pos,
                });
            }
        }

        // Register relation param names in `relations` so the body parser
        // resolves them as Call(param_id). Meta-vars are NOT registered here.
        for (pname, pid) in &rel_params {
            self.relations.insert(pname.clone(), *pid);
        }

        // Set current_macro so parse_primary_impl can detect recursive self-calls.
        // Move locals in (no clone) — we recover them via Option::take after parsing.
        self.current_macro = Some(CurrentMacro {
            name,
            arity,
            param_kinds,
            self_id,
            rel_params,
            meta_vars,
            term_patterns,
        });

        // Expect '{'
        skip_whitespace(input, pos);
        if *pos >= input.len() || peek_char(input, *pos) != Some('{') {
            return Err(ParseError {
                message: "Expected '{' after macro parameter list".to_string(),
                position: *pos,
            });
        }
        *pos += 1;

        let body = self.parse_rel_body_until_brace(input, pos)?;

        skip_whitespace(input, pos);
        if *pos >= input.len() || peek_char(input, *pos) != Some('}') {
            return Err(ParseError {
                message: "Expected '}'".to_string(),
                position: *pos,
            });
        }

        // Recover data from current_macro (moved in above, no clones needed).
        let cm = self.current_macro.take().unwrap();

        // Unregister relation param names from `relations` — they are local to the macro body.
        for (pname, _) in &cm.rel_params {
            self.relations.remove(pname);
        }

        let equation = MacroEquation {
            term_patterns: cm.term_patterns,
            rel_params: cm.rel_params,
            body,
            self_id: cm.self_id,
        };

        // Multi-equation accumulation: if the macro already exists, push a new equation.
        self.macro_signatures
            .entry(key.clone())
            .or_insert_with(|| cm.param_kinds.clone());
        let (macro_name, macro_arity) = key.clone();
        if let Some(def) = self.macro_defs.get_mut(&key) {
            def.equations.push(equation);
        } else {
            self.macro_defs.insert(
                key,
                MacroDef {
                    param_kinds: cm.param_kinds,
                    equations: vec![equation],
                },
            );
        }

        Ok(RelDef::Macro(macro_name, macro_arity))
    }

    /// Parse relation body until we hit a closing brace.
    fn parse_rel_body_until_brace(
        &mut self,
        input: &str,
        pos: &mut usize,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        self.parse_or_expr_impl(input, pos, Some('}'))
    }

    /// Count the number of comma-separated arguments between `(` and `)` at depth 0
    /// without consuming input. Used to determine arity before parsing args.
    fn peek_arg_count(input: &str, pos: usize) -> Result<usize, ParseError> {
        if pos >= input.len() || peek_char(input, pos) != Some('(') {
            return Err(ParseError {
                message: "Expected '('".to_string(),
                position: pos,
            });
        }
        let mut depth = 1usize;
        let mut count = 0usize;
        let mut saw_content = false;
        let mut i = pos + 1;
        while i < input.len() && depth > 0 {
            let ch = peek_char(input, i).unwrap();
            match ch {
                '(' | '[' => depth += 1,
                ')' | ']' => {
                    depth -= 1;
                    if depth == 0 {
                        if saw_content {
                            count += 1;
                        }
                        break;
                    }
                }
                ',' if depth == 1 => {
                    count += 1;
                    saw_content = false;
                    i += 1;
                    continue;
                }
                _ => {}
            }
            if !ch.is_ascii_whitespace() {
                saw_content = true;
            }
            i += 1;
        }
        Ok(count)
    }

    /// Look up param_kinds for a macro call given name and arity.
    /// Returns None if the macro is unknown.
    fn lookup_param_kinds(&self, name: &str, arity: usize) -> Option<Vec<ParamKind>> {
        // Check current macro first (avoids key allocation for recursive calls).
        if let Some(ref cm) = self.current_macro {
            if cm.name == name && cm.arity == arity {
                return Some(cm.param_kinds.clone());
            }
        }
        let key = (name.to_string(), arity);
        if let Some(def) = self.macro_defs.get(&key) {
            return Some(def.param_kinds.clone());
        }
        if let Some(kinds) = self.macro_signatures.get(&key) {
            return Some(kinds.clone());
        }
        None
    }

    /// Parse a macro call: the `(arg1, arg2, ...)` part after the name has been parsed.
    fn parse_macro_call(
        &mut self,
        input: &str,
        pos: &mut usize,
        name: &str,
        name_pos: usize,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        // Peek arity to look up param_kinds before parsing args.
        let arity = Self::peek_arg_count(input, *pos)?;
        let kinds = match self.lookup_param_kinds(name, arity) {
            Some(kinds) => kinds,
            None => {
                return Err(ParseError {
                    message: format!("undefined macro '{}/{}'", name, arity),
                    position: name_pos,
                });
            }
        };

        let args = self.parse_macro_args(input, pos, &kinds)?;
        let actual_arity = args.len();

        // Check for recursive self-call when inside a macro definition.
        if let Some(ref cm) = self.current_macro {
            if cm.name == name && cm.arity == actual_arity {
                return self.handle_self_call(args, name_pos);
            }
        }

        // Look up defined macro.
        let key = (name.to_string(), actual_arity);
        if self.macro_defs.contains_key(&key) {
            return self.expand_macro_call(name, actual_arity, args, name_pos);
        }

        // Signature is known (from pre-scan) but body not yet parsed — pending call.
        if self.macro_signatures.contains_key(&key) {
            let pending_id = self.alloc_rel_id();
            self.pending_macro_calls.insert(
                pending_id,
                PendingMacroCall {
                    name: name.to_string(),
                    arity: actual_arity,
                    args,
                },
            );
            return Ok(Rel::Call(pending_id));
        }

        Err(ParseError {
            message: format!("undefined macro '{}/{}'", name, actual_arity),
            position: name_pos,
        })
    }

    /// Parse comma-separated macro arguments inside `(...)`.
    /// Each argument is parsed according to its `ParamKind`:
    /// - `Relation` → parse as a full relation expression
    /// - `Term` → parse as a term (ground at call sites, may contain meta-vars in macro bodies)
    fn parse_macro_args(
        &mut self,
        input: &str,
        pos: &mut usize,
        param_kinds: &[ParamKind],
    ) -> Result<Vec<MacroArg<B::Constraint>>, ParseError> {
        // Consume '('
        if *pos >= input.len() || peek_char(input, *pos) != Some('(') {
            return Err(ParseError {
                message: "Expected '('".to_string(),
                position: *pos,
            });
        }
        *pos += 1;

        let mut args = Vec::new();
        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                return Err(ParseError {
                    message: "Unterminated macro argument list".to_string(),
                    position: *pos,
                });
            }
            if peek_char(input, *pos) == Some(')') {
                *pos += 1;
                break;
            }
            if !args.is_empty() {
                if peek_char(input, *pos) != Some(',') {
                    return Err(ParseError {
                        message: "Expected ',' between macro arguments".to_string(),
                        position: *pos,
                    });
                }
                *pos += 1;
            }

            let idx = args.len();
            let kind = param_kinds.get(idx).copied().unwrap_or(ParamKind::Relation);

            match kind {
                ParamKind::Relation => {
                    let arg = self.parse_macro_arg_expr(input, pos)?;
                    args.push(MacroArg::Rel(arg));
                }
                ParamKind::Term => {
                    let tid = self.parse_macro_term_arg(input, pos)?;
                    args.push(MacroArg::Term(tid));
                }
            }
        }
        Ok(args)
    }

    /// Parse a term argument for a macro call.
    ///
    /// - Inside a macro body: meta-vars from the current macro's term patterns
    ///   are available as `$name` variables.
    /// - At top level: term must be ground (no variables).
    fn parse_macro_term_arg(&self, input: &str, pos: &mut usize) -> Result<TermId, ParseError> {
        skip_whitespace(input, pos);
        let start_pos = *pos;

        // If inside a macro body, pre-populate var_map with meta-vars.
        let mut var_map: HashMap<String, u32> = if let Some(ref cm) = self.current_macro {
            cm.meta_vars.clone()
        } else {
            HashMap::new()
        };
        let mut var_order: Vec<u32> = Vec::new();

        let tid = self.parse_term_inner(input, pos, &mut var_map, &mut var_order)?;

        // At top level (no current_macro), term args must be ground.
        if self.current_macro.is_none() && !var_order.is_empty() {
            return Err(ParseError {
                message: "term arguments at call sites must be ground (no $-variables)".to_string(),
                position: start_pos,
            });
        }

        Ok(tid)
    }

    /// Parse a single macro argument: a relation expression delimited by `,` or `)`.
    ///
    /// The standard or/seq/and/primary parsers with `stop_char = None` already
    /// break on any non-operator character (including `,` and `)`), so they
    /// handle macro argument boundaries correctly without special logic.
    fn parse_macro_arg_expr(
        &mut self,
        input: &str,
        pos: &mut usize,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        self.parse_or_expr_impl(input, pos, None)
    }

    /// Handle a recursive self-call inside a macro body.
    ///
    /// For Relation args: each must be a bare parameter reference or parameter-free.
    /// For Term args: compared structurally with the equation's term pattern.
    ///
    /// Identity self-call (all args match) → `Call(self_id)` (runtime recursion via Fix).
    /// Non-identity with structurally smaller term args → deferred pending call
    /// (expanded at expansion time when meta-vars are concrete).
    fn handle_self_call(
        &mut self,
        args: Vec<MacroArg<B::Constraint>>,
        call_pos: usize,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        // Clone needed data from current_macro to avoid borrow conflict
        // when we later need to mutate self (alloc_rel_id, pending_macro_calls).
        let cm = self.current_macro.as_ref().unwrap();
        let cm_name = cm.name.clone();
        let cm_arity = cm.arity;
        let cm_self_id = cm.self_id;
        let cm_param_kinds = cm.param_kinds.clone();
        let cm_rel_params = cm.rel_params.clone();
        let cm_term_patterns = cm.term_patterns.clone();
        let param_ids: HashSet<RelId> = cm_rel_params.iter().map(|(_, id)| *id).collect();

        // Check identity per position.
        let mut is_identity = true;
        for (i, (arg, kind)) in args.iter().zip(cm_param_kinds.iter()).enumerate() {
            match (kind, arg) {
                (ParamKind::Relation, MacroArg::Rel(rel)) => {
                    match rel {
                        Rel::Call(id) if param_ids.contains(id) => {
                            // Check that this bare param ref matches the correct position.
                            let rel_pos = cm_param_kinds[..i]
                                .iter()
                                .filter(|k| **k == ParamKind::Relation)
                                .count();
                            let expected_id = cm_rel_params.get(rel_pos).map(|(_, id)| *id);
                            if expected_id != Some(*id) {
                                is_identity = false;
                            }
                        }
                        _ => {
                            if contains_any_call(rel, &param_ids) {
                                return Err(ParseError {
                                    message: format!(
                                        "recursive call to '{}/{}': argument {} contains a transformed \
                                         parameter reference, which may cause infinite expansion",
                                        cm_name, cm_arity, i + 1,
                                    ),
                                    position: call_pos,
                                });
                            }
                            is_identity = false;
                        }
                    }
                }
                (ParamKind::Term, MacroArg::Term(tid)) => {
                    // Compare structurally with the equation's term pattern.
                    if let Some(Some(pattern)) = cm_term_patterns.get(i) {
                        if *tid != *pattern {
                            is_identity = false;
                        }
                    } else {
                        is_identity = false;
                    }
                }
                _ => {
                    is_identity = false;
                }
            }
        }

        if is_identity {
            return Ok(Rel::Call(cm_self_id));
        }

        // Non-identity self-call: store as a pending call to be expanded at
        // expansion time when the macro is invoked with concrete args.
        // This enables structural recursion: `fmap($a, f)` inside
        // `fmap(@(sum $a $b), f)` is deferred until `$a` is concrete.
        let pending_id = self.alloc_rel_id();
        self.pending_macro_calls.insert(
            pending_id,
            PendingMacroCall {
                name: cm_name,
                arity: cm_arity,
                args,
            },
        );
        Ok(Rel::Call(pending_id))
    }

    /// Try to match an equation's term patterns against the given args.
    /// Returns (rel_subst, term_subst) if all term patterns match.
    fn try_match_equation(
        &self,
        eq: &MacroEquation<B::Constraint>,
        args: &[MacroArg<B::Constraint>],
        param_kinds: &[ParamKind],
    ) -> Option<EquationMatch<B::Constraint>> {
        use crate::matching::match_terms_combined;

        let mut rel_subst: HashMap<RelId, Rel<B::Constraint>> = HashMap::new();
        let mut combined_term_subst = crate::subst::Subst::new();
        let mut rel_idx = 0;

        for (i, (kind, arg)) in param_kinds.iter().zip(args.iter()).enumerate() {
            match (kind, arg) {
                (ParamKind::Relation, MacroArg::Rel(rel)) => {
                    if rel_idx < eq.rel_params.len() {
                        let (_, pid) = &eq.rel_params[rel_idx];
                        rel_subst.insert(*pid, rel.clone());
                        rel_idx += 1;
                    }
                }
                (ParamKind::Term, MacroArg::Term(actual_tid)) => {
                    if let Some(Some(pattern)) = eq.term_patterns.get(i) {
                        // Match pattern against actual term.
                        match match_terms_combined(*pattern, *actual_tid, &self.terms) {
                            Some(subst) => {
                                // Merge into combined_term_subst.
                                for (var, binding) in subst.iter() {
                                    if let Some(existing) = combined_term_subst.get(var) {
                                        if existing != binding {
                                            return None; // Conflicting bindings.
                                        }
                                    } else {
                                        combined_term_subst.bind(var, binding);
                                    }
                                }
                            }
                            None => return None,
                        }
                    } else {
                        return None;
                    }
                }
                _ => return None,
            }
        }
        Some((rel_subst, combined_term_subst))
    }

    /// Expand a call to an already-defined macro.
    ///
    /// For single-equation macros (all-Relation params), this works as before.
    /// For multi-equation macros (pattern-matching), tries each equation in order
    /// and expands with the first matching one.
    fn expand_macro_call(
        &mut self,
        name: &str,
        arity: usize,
        args: Vec<MacroArg<B::Constraint>>,
        call_pos: usize,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        // Expansion depth check.
        if self.expansion_depth >= 128 {
            return Err(ParseError {
                message: format!(
                    "macro expansion depth exceeded (128) for '{}/{}' \
                     — likely non-structural recursion",
                    name, arity,
                ),
                position: call_pos,
            });
        }
        self.expansion_depth += 1;

        let result = self.expand_macro_call_inner(name, arity, args, call_pos);

        self.expansion_depth -= 1;
        result
    }

    fn expand_macro_call_inner(
        &mut self,
        name: &str,
        arity: usize,
        args: Vec<MacroArg<B::Constraint>>,
        call_pos: usize,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        let key = (name.to_string(), arity);

        // Clone what we need from the MacroDef to avoid borrowing self.
        let (param_kinds, equations) = {
            let def = &self.macro_defs[&key];
            (def.param_kinds.clone(), def.equations.clone())
        };

        // Try each equation in order.
        for eq in &equations {
            if let Some((rel_subst, term_subst)) = self.try_match_equation(eq, &args, &param_kinds)
            {
                return self.expand_with_equation(eq, &rel_subst, &term_subst, call_pos);
            }
        }

        // No equation matched.
        Err(ParseError {
            message: format!(
                "no matching equation for '{}/{}' with the given term arguments",
                name, arity,
            ),
            position: call_pos,
        })
    }

    /// Expand a macro using a specific matched equation.
    fn expand_with_equation(
        &mut self,
        eq: &MacroEquation<B::Constraint>,
        rel_subst: &HashMap<RelId, Rel<B::Constraint>>,
        term_subst: &crate::subst::Subst,
        call_pos: usize,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        let fresh_id = self.alloc_rel_id();

        // Substitute relation params and self-references.
        let mut expanded = substitute_in_rel(&eq.body, rel_subst, eq.self_id, fresh_id);

        // Resolve any pending macro calls in the expanded body.
        // Apply both rel_subst (for relation params) and term_subst (for meta-vars
        // from pattern matching) to deferred calls.
        if !self.pending_macro_calls.is_empty() {
            expanded = self
                .resolve_pending_inner(expanded, rel_subst, Some(term_subst))
                .map_err(|msg| ParseError {
                    message: msg,
                    position: call_pos,
                })?;
        }

        // If the expanded body contains Call(fresh_id), it's recursive — wrap in Fix.
        if contains_call(&expanded, fresh_id) {
            Ok(Rel::Fix(fresh_id, Arc::new(expanded)))
        } else {
            Ok(expanded)
        }
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

/// Extract `(name, arity, param_kinds)` from the text after `rel ` in a macro definition header.
/// Returns `None` if this isn't a macro definition (no parameter list).
fn extract_macro_signature(after_rel: &str) -> Option<(String, usize, Vec<ParamKind>)> {
    let s = after_rel.trim_start();
    // Parse the name (lowercase identifier).
    let name_end = s
        .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .unwrap_or(s.len());
    if name_end == 0 {
        return None;
    }
    let name = &s[..name_end];
    let rest = s[name_end..].trim_start();
    // Must have '(' immediately.
    let rest = rest.strip_prefix('(')?;
    // Scan parameter list with depth tracking for nested parens/brackets.
    let mut kinds = Vec::new();
    let mut depth = 1usize;
    let mut saw_content = false;
    let mut is_term = false;
    for c in rest.chars() {
        match c {
            '(' | '[' => {
                depth += 1;
                saw_content = true;
            }
            ')' | ']' => {
                depth -= 1;
                if depth == 0 {
                    if saw_content {
                        kinds.push(if is_term {
                            ParamKind::Term
                        } else {
                            ParamKind::Relation
                        });
                    }
                    break;
                }
                saw_content = true;
            }
            ',' if depth == 1 => {
                if saw_content {
                    kinds.push(if is_term {
                        ParamKind::Term
                    } else {
                        ParamKind::Relation
                    });
                }
                saw_content = false;
                is_term = false;
            }
            '@' if depth == 1 && !saw_content => {
                is_term = true;
                saw_content = true;
            }
            _ if !c.is_ascii_whitespace() => {
                saw_content = true;
            }
            _ => {}
        }
    }
    if kinds.is_empty() {
        return None;
    }
    let arity = kinds.len();
    Some((name.to_string(), arity, kinds))
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
    builder: &mut ChrProgramBuilder,
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
            let (pred, arity) = decl.split_once('/').ok_or_else(|| ParseError {
                message: "Expected constraint declaration like name/arity".to_string(),
                position: 0,
            })?;
            let pred = pred.trim();
            let arity: u8 = arity.trim().parse().map_err(|_| ParseError {
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
    builder: &mut ChrProgramBuilder,
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
    builder: &mut ChrProgramBuilder,
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
    builder: &mut ChrProgramBuilder,
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
        // Detect `$x = $y` equality constraints in the body.
        if let Some(eq_pos) = find_top_level_token(part, "=") {
            // Guard: must not be part of `<=>` or `==>`.
            let prev = if eq_pos > 0 {
                part.as_bytes().get(eq_pos - 1).copied()
            } else {
                None
            };
            let next = part.as_bytes().get(eq_pos + 1).copied();
            let is_arrow = prev == Some(b'<') || prev == Some(b'=') || next == Some(b'>');
            if !is_arrow {
                let lhs_str = part[..eq_pos].trim();
                let rhs_str = part[eq_pos + 1..].trim();
                let mut lhs_pos = 0;
                let lhs = parse_chr_pat_term(lhs_str, &mut lhs_pos, builder, symbols, rvars)?;
                let mut rhs_pos = 0;
                let rhs = parse_chr_pat_term(rhs_str, &mut rhs_pos, builder, symbols, rvars)?;
                instrs.push(BodyInstr::AddBuiltin {
                    bid: BuiltinId::EQ,
                    args: vec![ArgExpr::Pat(lhs), ArgExpr::Pat(rhs)].into_boxed_slice(),
                });
                continue;
            }
        }
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
    builder: &mut ChrProgramBuilder,
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
    builder: &mut ChrProgramBuilder,
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
            GuardInstr::TopFunctor {
                t: target,
                f: symbols.intern(&functor),
                arity,
            }
        }
        "match" => {
            let pat = parse_chr_pat_term_bound(input, &mut pos, builder, symbols, rvars)?;
            let target = parse_chr_guard_val(input, &mut pos, symbols, terms, rvars)?;
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
    if peek_char(input, pos) != Some(')') {
        return Err(ParseError {
            message: "Expected ')' after guard arguments".to_string(),
            position: pos,
        });
    }
    pos += 1;

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
    builder: &mut ChrProgramBuilder,
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
            args.push(parse_chr_pat_term(
                input, &mut pos, builder, symbols, rvars,
            )?);
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
    let expected = builder.pred_arity(pred).map(|a| a as usize).unwrap_or(0);
    if args.len() != expected {
        return Err(ParseError {
            message: format!(
                "constraint '{}' expects {} args, got {}",
                name,
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
    builder: &mut ChrProgramBuilder,
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
            PatVarMode::BoundOnly(rvars) => *rvars.get(&name).ok_or_else(|| ParseError {
                message: format!("Guard variable '${}' must be bound by a head", name),
                position: *pos,
            })?,
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
    builder: &mut ChrProgramBuilder,
    symbols: &mut SymbolStore,
    rvars: &mut HashMap<String, RVar>,
) -> Result<PatId, ParseError> {
    parse_chr_pat_term_impl(input, pos, builder, symbols, &mut PatVarMode::Create(rvars))
}

fn parse_chr_pat_term_bound(
    input: &str,
    pos: &mut usize,
    builder: &mut ChrProgramBuilder,
    symbols: &mut SymbolStore,
    rvars: &HashMap<String, RVar>,
) -> Result<PatId, ParseError> {
    parse_chr_pat_term_impl(
        input,
        pos,
        builder,
        symbols,
        &mut PatVarMode::BoundOnly(rvars),
    )
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
                let part = input[start..idx].trim();
                if !part.is_empty() {
                    parts.push(part);
                }
                start = idx + 1;
            }
            _ => {}
        }
    }
    if start < input.len() {
        let part = input[start..].trim();
        if !part.is_empty() {
            parts.push(part);
        }
    }
    parts
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

// ============================================================================
// Macro expansion helpers
// ============================================================================

/// Substitute `Call(id)` nodes in a `Rel` tree according to a substitution map.
/// Also replaces `Call(self_id)` with `Call(fresh_id)` for recursive references.
fn substitute_in_rel<C: Clone>(
    rel: &Rel<C>,
    subst: &HashMap<RelId, Rel<C>>,
    self_id: RelId,
    fresh_id: RelId,
) -> Rel<C> {
    match rel {
        Rel::Call(id) if subst.contains_key(id) => subst[id].clone(),
        Rel::Call(id) if *id == self_id => Rel::Call(fresh_id),
        Rel::Call(_) | Rel::Zero | Rel::Atom(_) => rel.clone(),
        Rel::Or(a, b) => Rel::Or(
            Arc::new(substitute_in_rel(a, subst, self_id, fresh_id)),
            Arc::new(substitute_in_rel(b, subst, self_id, fresh_id)),
        ),
        Rel::And(a, b) => Rel::And(
            Arc::new(substitute_in_rel(a, subst, self_id, fresh_id)),
            Arc::new(substitute_in_rel(b, subst, self_id, fresh_id)),
        ),
        Rel::Seq(xs) => {
            let new_xs: Vec<Arc<Rel<C>>> = xs
                .iter()
                .map(|x| Arc::new(substitute_in_rel(x, subst, self_id, fresh_id)))
                .collect();
            Rel::Seq(Arc::from(new_xs))
        }
        Rel::Fix(id, body) => Rel::Fix(
            *id,
            Arc::new(substitute_in_rel(body, subst, self_id, fresh_id)),
        ),
    }
}

/// Check whether a `Rel` tree contains any `Call(id)` matching a predicate.
fn rel_has_call_where<C>(rel: &Rel<C>, pred: impl Fn(RelId) -> bool + Copy) -> bool {
    match rel {
        Rel::Call(id) => pred(*id),
        Rel::Zero | Rel::Atom(_) => false,
        Rel::Or(a, b) | Rel::And(a, b) => {
            rel_has_call_where(a, pred) || rel_has_call_where(b, pred)
        }
        Rel::Seq(xs) => xs.iter().any(|x| rel_has_call_where(x, pred)),
        Rel::Fix(_, body) => rel_has_call_where(body, pred),
    }
}

/// Check whether a `Rel` tree contains `Call(target_id)` anywhere.
fn contains_call<C>(rel: &Rel<C>, target_id: RelId) -> bool {
    rel_has_call_where(rel, |id| id == target_id)
}

/// Check whether a `Rel` tree contains any `Call(id)` where `id` is in the given set.
fn contains_any_call<C>(rel: &Rel<C>, ids: &HashSet<RelId>) -> bool {
    rel_has_call_where(rel, |id| ids.contains(&id))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Create a parser with the standard CHR `eq` theory (eq/2, simplification rule).
    fn parser_with_eq_theory() -> Parser<ChrConstraintBuilder> {
        let mut parser = Parser::with_chr();
        parser
            .parse_theory_def(
                r#"
theory eq {
  constraint eq/2
  (eq $x $x) <=> .
}
"#,
            )
            .expect("parse eq theory");
        parser
    }

    /// Register the standard fmap equations (unit, xvar, sum) on a parser.
    fn define_fmap_sum(parser: &mut Parser) {
        parser
            .parse_rel_def("rel fmap(@unit, f) { $x -> $x }")
            .expect("fmap/unit");
        parser
            .parse_rel_def("rel fmap(@xvar, f) { f }")
            .expect("fmap/xvar");
        parser
            .parse_rel_def(
                "rel fmap(@(sum $a $b), f) { \
                   [(inl $x) -> $x ; fmap($a, f) ; $y -> (inl $y)] \
                 | [(inr $x) -> $x ; fmap($b, f) ; $y -> (inr $y)] \
                 }",
            )
            .expect("fmap/sum");
    }

    /// Register the m/unit, m/xvar, m/pair equations on a parser.
    fn define_m_pair(parser: &mut Parser) {
        parser
            .parse_rel_def("rel m(@unit, f) { $x -> $x }")
            .expect("m/unit");
        parser
            .parse_rel_def("rel m(@xvar, f) { f }")
            .expect("m/xvar");
        parser
            .parse_rel_def("rel m(@(pair $a $b), f) { m($a, f) ; m($b, f) }")
            .expect("m/pair");
    }

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
        let (name, rel) = result.unwrap().into_relation();
        assert_eq!(name, "id");
        assert!(matches!(rel, Rel::Fix(_, _)));
    }

    #[test]
    fn parse_rel_def_with_or() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_def("rel test { a -> b | c -> d }");
        assert!(result.is_ok());
        let (name, rel) = result.unwrap().into_relation();
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
        let (name, _rel) = result.unwrap().into_relation();
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
        let mut parser = parser_with_eq_theory();
        let nf = parser
            .parse_rule("(pair $x $y) { (eq $x $y) } -> $x")
            .expect("parse rule with constraint");

        assert_eq!(nf.drop_fresh.constraint.store().alive_count, 1);
        let pred = nf
            .drop_fresh
            .constraint
            .program
            .pred_id("eq")
            .expect("eq predicate id");
        let inst = nf
            .drop_fresh
            .constraint
            .store()
            .inst
            .iter()
            .find(|c| c.alive)
            .expect("alive constraint");
        assert_eq!(inst.pred, pred);
    }

    #[test]
    fn atom_lhs_with_constraint_block_parses_as_rule() {
        let mut parser = Parser::with_chr();
        let theory = r#"
theory t {
    constraint p/2
    constraint q/2
    (p $x $y), (q $y $z) <=> (p $x $z).
}
"#;
        parser.parse_theory_def(theory).expect("parse theory");
        let (name, rel) = parser
            .parse_rel_def("rel test { a { (p a b), (q b c) } -> a }")
            .expect("atom LHS with constraint block must parse as rule")
            .into_relation();
        assert_eq!(name, "test");
        match rel {
            Rel::Fix(_, _) => {}
            _ => panic!("expected Fix"),
        }
    }

    #[test]
    fn constraint_with_unknown_predicate_fails() {
        let mut parser = parser_with_eq_theory();
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
            .store()
            .inst
            .iter()
            .filter(|c| c.alive && c.pred == q)
            .count();
        assert_eq!(count, 1, "Expected guard to add q(z)");
    }

    #[test]
    fn constraint_arity_mismatch_fails() {
        let mut parser = parser_with_eq_theory();
        let err = match parser.parse_rule("$x { (eq $x) } -> $x") {
            Ok(_) => panic!("expected arity mismatch error"),
            Err(err) => err,
        };
        assert!(
            err.message.contains("expects") && err.message.contains("args"),
            "unexpected error: {}",
            err
        );
    }

    #[test]
    fn format_nf_includes_constraints() {
        let mut parser = parser_with_eq_theory();
        let nf = parser
            .parse_rule("(pair $x $y) { (eq $x $y) } -> $x")
            .expect("parse rule with constraint");
        let mut terms = parser.take_terms();
        let rendered = crate::nf::format_nf(&nf, &mut terms, parser.symbols()).expect("format nf");
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
        // Parser contains SymbolStore, TermStore, HashMap<String, RelId>,
        // macro_defs HashMap, and current_macro Option.
        assert!(
            size < 1300,
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

    // ========================================================================
    // EQUALITY IN RULE BODIES
    // ========================================================================

    #[test]
    fn theory_parses_equality_in_body() {
        let mut parser = Parser::with_chr();
        let theory = r#"
theory eq_test {
  constraint p/2
  (p $x $y) <=> $x = $y.
}
"#;
        parser
            .parse_theory_def(theory)
            .expect("parse theory with equality in body");
    }

    #[test]
    fn equality_in_body_produces_subst_via_parser() {
        let mut parser = Parser::with_chr();
        let theory = r#"
theory eq_test {
  constraint p/1
  (p $x) <=> $x = z.
}
"#;
        parser.parse_theory_def(theory).expect("parse theory");
        let nf = parser
            .parse_rule("$x { (p $x) } -> $x")
            .expect("parse rule with eq constraint");

        let mut terms = parser.take_terms();
        let (normalized, subst_opt) = nf
            .drop_fresh
            .constraint
            .normalize(&mut terms)
            .expect("normalize constraints");

        let subst = subst_opt.expect("should produce a substitution from $x = z");
        // The constraint p(Var) was simplified, and the body ran $x = z,
        // binding the variable to the ground term z.
        assert!(!subst.is_empty(), "subst should be non-empty from $x = z");
        assert!(
            normalized.is_empty(),
            "p should have been removed by simplification"
        );
    }

    #[test]
    fn equality_arrow_not_confused_with_eq() {
        let mut parser = Parser::with_chr();
        // Ensure that `==>` and `<=>` are not confused with `=`.
        let theory = r#"
theory arrow_test {
  constraint p/1
  constraint q/1
  (p $x) ==> (q $x).
}
"#;
        parser
            .parse_theory_def(theory)
            .expect("parse theory with ==> arrow");
    }

    // ========================================================================
    // MACRO DEFINITION AND EXPANSION TESTS
    // ========================================================================

    #[test]
    fn parse_non_recursive_macro_returns_macro() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_def("rel double(r) { r ; r }");
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());
        assert!(
            matches!(result.unwrap(), RelDef::Macro(_, _)),
            "Macro def should return RelDef::Macro"
        );
        assert!(
            parser.macro_defs.contains_key(&("double".to_string(), 1)),
            "Macro should be stored in macro_defs"
        );
    }

    #[test]
    fn parse_macro_two_params() {
        let mut parser = Parser::new();
        let result = parser.parse_rel_def("rel compose(f, g) { f ; g }");
        assert!(result.is_ok());
        assert!(matches!(result.unwrap(), RelDef::Macro(_, 2)));
        assert!(parser.macro_defs.contains_key(&("compose".to_string(), 2)));
    }

    #[test]
    fn expand_non_recursive_macro_substitutes_params() {
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel double(r) { r ; r }")
            .expect("define macro");

        // Use the macro in a body: double([$x -> (s $x)])
        let rel = parser
            .parse_rel_body("double([$x -> (s $x)])")
            .expect("expand macro");

        // Should be Seq([Atom, Atom]) — the rule duplicated.
        match rel {
            Rel::Seq(factors) => {
                assert_eq!(factors.len(), 2, "double(r) should produce r;r = Seq of 2");
                assert!(
                    matches!(factors[0].as_ref(), Rel::Atom(_)),
                    "First element should be Atom"
                );
                assert!(
                    matches!(factors[1].as_ref(), Rel::Atom(_)),
                    "Second element should be Atom"
                );
            }
            _ => panic!("Expected Seq from double expansion, got {:?}", rel),
        }
    }

    #[test]
    fn expand_recursive_macro_wraps_in_fix() {
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel repeat(r) { r | [r ; repeat(r)] }")
            .expect("define recursive macro");

        let rel = parser
            .parse_rel_body("repeat([$x -> (s $x)])")
            .expect("expand recursive macro");

        // Should be Fix(_, Or(Atom, Seq([Atom, Call(_)])))
        match rel {
            Rel::Fix(id, body) => match body.as_ref() {
                Rel::Or(left, right) => {
                    assert!(
                        matches!(left.as_ref(), Rel::Atom(_)),
                        "Left branch should be the base case atom"
                    );
                    match right.as_ref() {
                        Rel::Seq(factors) => {
                            assert_eq!(factors.len(), 2);
                            assert!(matches!(factors[0].as_ref(), Rel::Atom(_)));
                            assert!(
                                matches!(factors[1].as_ref(), Rel::Call(call_id) if *call_id == id),
                                "Recursive call should reference the Fix id"
                            );
                        }
                        _ => panic!("Right branch should be Seq"),
                    }
                }
                _ => panic!("Fix body should be Or"),
            },
            _ => panic!("Expected Fix wrapping recursive macro expansion"),
        }
    }

    #[test]
    fn macro_arity_overloading() {
        let mut parser = Parser::new();
        // Define a plain relation `foo`
        let result = parser.parse_rel_def("rel foo { a -> b }");
        assert!(
            matches!(result.unwrap(), RelDef::Relation(_, _)),
            "plain rel should return Relation"
        );

        // Define a macro `foo(x)` — different arity, different entity.
        let result = parser.parse_rel_def("rel foo(x) { x ; x }");
        assert!(
            matches!(result.unwrap(), RelDef::Macro(_, _)),
            "macro should return Macro"
        );

        // Both should coexist.
        assert!(parser.relations.contains_key("foo"));
        assert!(parser.macro_defs.contains_key(&("foo".to_string(), 1)));
    }

    #[test]
    fn macro_call_wrong_arity_errors() {
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel double(r) { r ; r }")
            .expect("define double/1");

        // Call with wrong arity
        let err = parser
            .parse_rel_body("double(a -> b, c -> d)")
            .expect_err("wrong arity should fail");
        assert!(
            err.message.contains("undefined macro 'double/2'"),
            "Expected arity error, got: {}",
            err.message
        );
    }

    #[test]
    fn macro_undefined_errors() {
        let mut parser = Parser::new();
        let err = parser
            .parse_rel_body("nonexistent(a -> b)")
            .expect_err("undefined macro should fail");
        assert!(
            err.message.contains("undefined macro"),
            "Expected undefined error, got: {}",
            err.message
        );
    }

    #[test]
    fn macro_empty_params_errors() {
        let mut parser = Parser::new();
        let err = parser
            .parse_rel_def("rel bad() { a -> b }")
            .expect_err("empty params should fail");
        assert!(
            err.message.contains("cannot be empty"),
            "Expected empty params error, got: {}",
            err.message
        );
    }

    #[test]
    fn macro_cross_call_with_param_propagation() {
        let mut parser = Parser::new();
        // Define compose(f, g) = f ; g
        parser
            .parse_rel_def("rel compose(f, g) { f ; g }")
            .expect("define compose");
        // Define double(r) = compose(r, r)
        parser
            .parse_rel_def("rel double(r) { compose(r, r) }")
            .expect("define double using compose");

        // Expand double([$x -> (s $x)])
        let rel = parser
            .parse_rel_body("double([$x -> (s $x)])")
            .expect("expand double");

        // compose(r, r) with r = the rule should produce Seq([rule, rule])
        match rel {
            Rel::Seq(factors) => {
                assert_eq!(factors.len(), 2, "compose(r, r) = r;r");
            }
            _ => panic!("Expected Seq, got {:?}", rel),
        }
    }

    #[test]
    fn macro_recursive_identity_self_call() {
        let mut parser = Parser::new();
        // fold(alg, base) uses fold(alg, base) in body — identity self-call.
        let result = parser.parse_rel_def("rel fold(alg, base) { base | [alg ; fold(alg, base)] }");
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());
        assert!(matches!(result.unwrap(), RelDef::Macro(_, _)), "Should be parsed as macro");

        // Stored in macro_defs.
        let def = parser
            .macro_defs
            .get(&("fold".to_string(), 2))
            .expect("fold/2 should be in macro_defs");

        // Body should have a self-call (Call to self_id).
        let eq = &def.equations[0];
        assert!(
            contains_call(&eq.body, eq.self_id),
            "Body should contain a self-call"
        );
    }

    #[test]
    fn macro_non_identity_self_call_deferred_then_depth_limit() {
        let mut parser = Parser::new();
        // flip(a, b) { flip(b, a) } — non-identity self-call is deferred as pending.
        // Definition succeeds...
        parser
            .parse_rel_def("rel flip(a, b) { flip(b, a) }")
            .expect("non-identity self-call deferred as pending");

        // ...but expansion hits infinite recursion (depth limit).
        let err = parser
            .parse_rel_body("flip([$x -> $x], [$y -> $y])")
            .expect_err("non-structural recursion should hit depth limit");
        assert!(
            err.message.contains("expansion depth exceeded"),
            "Expected depth limit error, got: {}",
            err.message
        );
    }

    #[test]
    fn macro_concrete_self_call_deferred_then_depth_limit() {
        let mut parser = Parser::new();
        // foo(a) { foo([$x -> $x]) } — concrete arg self-call is deferred.
        // Definition succeeds...
        parser
            .parse_rel_def("rel foo(a) { foo([$x -> $x]) }")
            .expect("concrete-arg self-call deferred as pending");

        // ...but expansion hits infinite recursion (depth limit).
        let err = parser
            .parse_rel_body("foo([$y -> $y])")
            .expect_err("non-structural recursion should hit depth limit");
        assert!(
            err.message.contains("expansion depth exceeded"),
            "Expected depth limit error, got: {}",
            err.message
        );
    }

    #[test]
    fn macro_param_not_leaked_after_definition() {
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel m(r) { r ; r }")
            .expect("define macro");

        // After defining the macro, the param name `r` should NOT be
        // registered as a relation in the parser.
        assert!(
            !parser.relations.contains_key("r"),
            "Macro param 'r' should not leak into relations"
        );
    }

    #[test]
    fn macro_arg_is_full_relation_expr() {
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel apply(f) { f }")
            .expect("define apply");

        // Pass a complex relation expression as arg: or, seq, and
        let rel = parser
            .parse_rel_body("apply([a -> b | c -> d])")
            .expect("expand with complex arg");
        // Should be Or(Atom, Atom) — the arg itself.
        assert!(matches!(rel, Rel::Or(_, _)));
    }

    #[test]
    fn macro_non_recursive_no_fix_wrap() {
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel id_wrap(f) { f }")
            .expect("define id_wrap");

        let rel = parser
            .parse_rel_body("id_wrap([$x -> $x])")
            .expect("expand id_wrap");

        // Should NOT be wrapped in Fix since there's no recursion.
        assert!(
            !matches!(rel, Rel::Fix(_, _)),
            "Non-recursive expansion should not have Fix"
        );
    }

    #[test]
    fn macro_names_returns_defined_macros() {
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel double(r) { r ; r }")
            .expect("define double");
        parser
            .parse_rel_def("rel compose(f, g) { f ; g }")
            .expect("define compose");

        let names = parser.macro_names();
        assert_eq!(names.len(), 2);
        let name_set: HashSet<(String, usize)> = names.into_iter().collect();
        assert!(name_set.contains(&("double".to_string(), 1)));
        assert!(name_set.contains(&("compose".to_string(), 2)));
    }

    // ========================================================================
    // PATTERN-MATCHING MACRO TESTS
    // ========================================================================

    // --- Signature Detection ---

    #[test]
    fn extract_signature_all_relation() {
        let sig = extract_macro_signature("compose(f, g) { f ; g }");
        assert_eq!(
            sig,
            Some((
                "compose".to_string(),
                2,
                vec![ParamKind::Relation, ParamKind::Relation]
            ))
        );
    }

    #[test]
    fn extract_signature_mixed() {
        let sig = extract_macro_signature("fmap(@t, f) { f }");
        assert_eq!(
            sig,
            Some((
                "fmap".to_string(),
                2,
                vec![ParamKind::Term, ParamKind::Relation]
            ))
        );
    }

    #[test]
    fn extract_signature_all_term() {
        let sig = extract_macro_signature("m(@a, @b) { $x -> $x }");
        assert_eq!(
            sig,
            Some(("m".to_string(), 2, vec![ParamKind::Term, ParamKind::Term]))
        );
    }

    // --- Single-Equation Term Patterns ---

    #[test]
    fn term_param_atom_pattern() {
        let mut parser = Parser::new();
        // Define a macro with a term pattern matching the atom `z`.
        parser
            .parse_rel_def("rel m(@z, f) { f }")
            .expect("define m with atom term pattern");

        // Call with matching term.
        let rel = parser
            .parse_rel_body("m(z, [$x -> (s $x)])")
            .expect("expand m(z, ...)");

        // Should be the relation arg (the rule), not wrapped in Fix.
        assert!(
            matches!(rel, Rel::Atom(_)),
            "Expected Atom from expansion, got {:?}",
            rel
        );
    }

    #[test]
    fn term_param_compound_pattern() {
        let mut parser = Parser::new();
        // Pattern (s $a) matches compound terms and binds meta-var $a.
        // The body uses $a in a recursive call that we don't have yet,
        // so let's just verify expansion with identity body.
        parser
            .parse_rel_def("rel m(@(s $a), f) { f }")
            .expect("define m with compound term pattern");

        // Call with matching term (s z).
        let rel = parser
            .parse_rel_body("m((s z), [$x -> (s $x)])")
            .expect("expand m((s z), ...)");

        assert!(
            matches!(rel, Rel::Atom(_)),
            "Expected Atom from expansion, got {:?}",
            rel
        );
    }

    #[test]
    fn term_param_no_match_errors() {
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel m(@z, f) { f }")
            .expect("define m with z pattern");

        // Call with non-matching term.
        let err = parser
            .parse_rel_body("m((s z), [$x -> $x])")
            .expect_err("should fail: (s z) doesn't match z");
        assert!(
            err.message.contains("no matching equation"),
            "Expected no-match error, got: {}",
            err.message
        );
    }

    // --- Multi-Equation Dispatch ---

    #[test]
    fn multi_equation_selects_first_match() {
        let mut parser = Parser::new();
        // Two equations for m/2: one for `z`, one for `(s $a)`.
        parser
            .parse_rel_def("rel m(@z, f) { f }")
            .expect("define m/2 equation 1");
        parser
            .parse_rel_def("rel m(@(s $a), f) { f ; f }")
            .expect("define m/2 equation 2");

        // z matches equation 1 → body is `f` → Atom
        let rel_z = parser
            .parse_rel_body("m(z, [$x -> (s $x)])")
            .expect("expand m(z, ...)");
        assert!(
            matches!(rel_z, Rel::Atom(_)),
            "z should match first equation (body = f), got {:?}",
            rel_z
        );

        // (s z) matches equation 2 → body is `f ; f` → Seq of 2
        let rel_s = parser
            .parse_rel_body("m((s z), [$x -> (s $x)])")
            .expect("expand m((s z), ...)");
        match rel_s {
            Rel::Seq(factors) => {
                assert_eq!(factors.len(), 2, "second equation body is f;f = Seq of 2");
            }
            _ => panic!("Expected Seq from second equation, got {:?}", rel_s),
        }
    }

    #[test]
    fn param_kind_mismatch_errors() {
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel m(@z, f) { f }")
            .expect("define m with @-first");

        // Second equation has different @-positions.
        let err = parser
            .parse_rel_def("rel m(g, @z) { g }")
            .expect_err("mismatched param kinds should error");
        assert!(
            err.message.contains("parameter kinds"),
            "Expected param-kind mismatch error, got: {}",
            err.message
        );
    }

    // --- Recursive Expansion ---

    #[test]
    fn fmap_sum_unit_xvar() {
        let mut parser = Parser::new();
        define_fmap_sum(&mut parser);

        // Expand fmap((sum unit xvar), [$x -> (s $x)])
        // Should produce Or(inl_branch, inr_branch) where:
        // - inl_branch has fmap(unit, f) = Seq[unwrap, identity, rewrap]
        // - inr_branch has fmap(xvar, f) = Seq[unwrap, f, rewrap]
        let rel = parser
            .parse_rel_body("fmap((sum unit xvar), [$x -> (s $x)])")
            .expect("expand fmap((sum unit xvar), ...)");

        // The result should be an Or (two branches from `|`).
        match &rel {
            Rel::Or(_, _) => {
                // Correct: the two branches from the sum equation.
            }
            _ => panic!("Expected Or from fmap(sum unit xvar), got {:?}", rel),
        }
    }

    #[test]
    fn fmap_nested_sum_depth_2() {
        let mut parser = Parser::new();
        define_fmap_sum(&mut parser);

        // Depth-2: fmap((sum (sum unit xvar) unit), inc)
        // Should expand without error — structural recursion terminates.
        let rel = parser
            .parse_rel_body("fmap((sum (sum unit xvar) unit), [$x -> (s $x)])")
            .expect("expand depth-2 nested fmap");

        // Top level: Or from outer sum.
        assert!(
            matches!(&rel, Rel::Or(_, _)),
            "Expected Or at top level, got {:?}",
            rel
        );
    }

    // --- Self-Call Handling ---

    #[test]
    fn identity_self_call_with_term_param() {
        let mut parser = Parser::new();
        // fmap(@(sum $a $b), f) calling fmap((sum $a $b), f) should be identity.
        parser
            .parse_rel_def(
                "rel fmap(@(sum $a $b), f) { \
                   [(inl $x) -> $x ; fmap($a, f) ; $y -> (inl $y)] \
                 | [(inr $x) -> $x ; fmap($b, f) ; $y -> (inr $y)] \
                 | fmap((sum $a $b), f) \
                 }",
            )
            .expect("define fmap with identity self-call");

        let def = parser
            .macro_defs
            .get(&("fmap".to_string(), 2))
            .expect("fmap/2 should be in macro_defs");
        let eq = &def.equations[0];

        // Body should contain a self-call (identity).
        assert!(
            contains_call(&eq.body, eq.self_id),
            "Body should contain identity self-call"
        );
    }

    #[test]
    fn structural_self_call_deferred() {
        let mut parser = Parser::new();
        // fmap(@(sum $a $b), f) calling fmap($a, f) — structurally smaller.
        // Should be deferred (pending), not error.
        parser
            .parse_rel_def(
                "rel fmap(@(sum $a $b), f) { \
                   fmap($a, f) \
                 }",
            )
            .expect("structural self-call should be deferred, not error");

        // The body should contain a pending call, not a direct self-call.
        let def = parser
            .macro_defs
            .get(&("fmap".to_string(), 2))
            .expect("fmap/2 should be in macro_defs");
        let eq = &def.equations[0];

        // Body should NOT contain Call(self_id) — it's deferred as a pending call.
        assert!(
            !contains_call(&eq.body, eq.self_id),
            "Structural self-call should be deferred, not identity"
        );
    }

    // --- Forward References ---

    #[test]
    fn forward_ref_with_term_params() {
        let mut parser = Parser::new();
        let stmts = vec![
            "rel a(@z, f) { b(z, f) }".to_string(),
            "rel b(@z, f) { f }".to_string(),
        ];
        parser.scan_macro_signatures(&stmts);

        for stmt in &stmts {
            parser.parse_rel_def(stmt).expect("parse macro");
        }

        // Expand a(z, [$x -> $x]) — should resolve b(z, ...) via forward ref.
        let rel = parser
            .parse_rel_body("a(z, [$x -> $x])")
            .expect("expand with forward ref");

        assert!(
            matches!(rel, Rel::Atom(_)),
            "Expected Atom after forward ref resolution, got {:?}",
            rel
        );
    }

    // --- Meta-var Scoping ---

    #[test]
    fn meta_vars_dont_leak() {
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel m(@(s $a), f) { f }")
            .expect("define m with meta-var $a");

        // After definition, $a should NOT be in the relations map.
        assert!(
            !parser.relations.contains_key("a"),
            "Meta-var 'a' should not leak into relations"
        );
    }

    // --- Expansion Depth Limit ---

    #[test]
    fn infinite_expansion_depth_limit() {
        let mut parser = Parser::new();
        // Two equations that bounce: inf(@z) expands to call inf((s z)),
        // and inf(@(s $a)) expands to call inf(z).
        // This is non-structural mutual recursion that never terminates.
        parser
            .parse_rel_def("rel inf(@z) { inf((s z)) }")
            .expect("define inf/z");
        parser
            .parse_rel_def("rel inf(@(s $a)) { inf(z) }")
            .expect("define inf/s");

        let err = parser
            .parse_rel_body("inf(z)")
            .expect_err("should hit depth limit");
        assert!(
            err.message.contains("expansion depth exceeded"),
            "Expected depth limit error, got: {}",
            err.message
        );
    }

    // --- End-to-End Integration ---

    #[test]
    fn polynomial_functor_fmap_end_to_end() {
        let mut parser = Parser::new();
        define_fmap_sum(&mut parser);
        // Simplified product: just applies fmap to the first component.
        // Full product semantics would need And or a more complex piping,
        // but for testing dispatch and recursive expansion this suffices.
        parser
            .parse_rel_def(
                "rel fmap(@(prod $a $b), f) { \
                   (pair $x $y) -> $x ; fmap($a, f) \
                 }",
            )
            .expect("fmap/prod");

        // Test 1: Simple sum of unit and xvar
        let r1 = parser
            .parse_rel_body("fmap((sum unit xvar), [$x -> (s $x)])")
            .expect("fmap(sum unit xvar)");
        assert!(matches!(&r1, Rel::Or(_, _)), "sum → Or");

        // Test 2: Product
        let r2 = parser
            .parse_rel_body("fmap((prod xvar xvar), [$x -> (s $x)])")
            .expect("fmap(prod xvar xvar)");
        // Product body is a single rule → Atom(Seq(...)) or just an Atom
        assert!(
            matches!(&r2, Rel::Atom(_) | Rel::Seq(_)),
            "prod → Atom or Seq, got {:?}",
            r2
        );

        // Test 3: Nested sum-of-prod
        let r3 = parser
            .parse_rel_body("fmap((sum (prod xvar unit) xvar), [$x -> (s $x)])")
            .expect("fmap(sum(prod xvar unit) xvar)");
        assert!(matches!(&r3, Rel::Or(_, _)), "sum-of-prod → Or");

        // Test 4: All-unit is all identity
        let r4 = parser
            .parse_rel_body("fmap(unit, [$x -> (s $x)])")
            .expect("fmap(unit)");
        assert!(
            matches!(&r4, Rel::Atom(_)),
            "fmap(unit) should be identity (Atom), got {:?}",
            r4
        );

        // Test 5: xvar is just the functor argument
        let r5 = parser
            .parse_rel_body("fmap(xvar, [$x -> (s $x)])")
            .expect("fmap(xvar)");
        assert!(
            matches!(&r5, Rel::Atom(_)),
            "fmap(xvar) should be f (Atom), got {:?}",
            r5
        );
    }

    #[test]
    fn term_arg_at_call_site_must_be_ground() {
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel m(@z) { $x -> $x }")
            .expect("define m");

        // Calling with a variable in a term arg at top level should error.
        let err = parser
            .parse_rel_body("m($a)")
            .expect_err("term args at call sites must be ground");
        assert!(
            err.message.contains("ground"),
            "Expected ground error, got: {}",
            err.message
        );
    }

    #[test]
    fn pure_relation_macros_expand_correctly() {
        // Verify that pure relation macros (no @ params) expand correctly.
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel double(r) { r ; r }")
            .expect("define double");
        parser
            .parse_rel_def("rel compose(f, g) { f ; g }")
            .expect("define compose");
        parser
            .parse_rel_def("rel repeat(r) { r | [r ; repeat(r)] }")
            .expect("define repeat");

        // double expands to Seq of 2
        let r1 = parser
            .parse_rel_body("double([$x -> (s $x)])")
            .expect("expand double");
        assert!(matches!(&r1, Rel::Seq(_)));

        // compose expands to Seq of 2
        let r2 = parser
            .parse_rel_body("compose([$x -> (s $x)], [$y -> (s $y)])")
            .expect("expand compose");
        assert!(matches!(&r2, Rel::Seq(_)));

        // repeat expands to Fix(Or(Atom, Seq))
        let r3 = parser
            .parse_rel_body("repeat([$x -> (s $x)])")
            .expect("expand repeat");
        assert!(matches!(&r3, Rel::Fix(_, _)));
    }

    // ========================================================================
    // DEEP STRUCTURAL VERIFICATION TESTS
    // ========================================================================

    /// Helper: compare two Rel trees structurally, ignoring RelId values.
    /// Returns true if they have the same shape and the same Atoms.
    fn rel_shape_eq<C: PartialEq>(a: &Rel<C>, b: &Rel<C>) -> bool {
        match (a, b) {
            (Rel::Zero, Rel::Zero) => true,
            (Rel::Atom(x), Rel::Atom(y)) => x == y,
            (Rel::Or(a1, a2), Rel::Or(b1, b2)) => rel_shape_eq(a1, b1) && rel_shape_eq(a2, b2),
            (Rel::And(a1, a2), Rel::And(b1, b2)) => rel_shape_eq(a1, b1) && rel_shape_eq(a2, b2),
            (Rel::Seq(xs), Rel::Seq(ys)) => {
                xs.len() == ys.len() && xs.iter().zip(ys.iter()).all(|(x, y)| rel_shape_eq(x, y))
            }
            (Rel::Fix(_, body_a), Rel::Fix(_, body_b)) => rel_shape_eq(body_a, body_b),
            (Rel::Call(_), Rel::Call(_)) => true, // RelIds differ but both are calls
            _ => false,
        }
    }

    #[test]
    fn fmap_unit_expands_to_identity_rule() {
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel fmap(@unit, f) { $x -> $x }")
            .expect("define fmap/unit");

        let expanded = parser
            .parse_rel_body("fmap(unit, [$y -> (s $y)])")
            .expect("expand fmap(unit, ...)");

        // fmap(unit, f) = { $x -> $x } regardless of f.
        // Compare against directly parsed identity rule.
        let expected = parser
            .parse_rel_body("$x -> $x")
            .expect("parse identity rule");

        assert!(
            rel_shape_eq(&expanded, &expected),
            "fmap(unit, f) should expand to identity rule.\n\
             Got: {:?}\nExpected: {:?}",
            expanded,
            expected
        );
    }

    #[test]
    fn fmap_xvar_expands_to_passed_relation() {
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel fmap(@xvar, f) { f }")
            .expect("define fmap/xvar");

        let expanded = parser
            .parse_rel_body("fmap(xvar, [$y -> (s $y)])")
            .expect("expand fmap(xvar, ...)");

        let expected = parser
            .parse_rel_body("$y -> (s $y)")
            .expect("parse inc rule");

        assert!(
            rel_shape_eq(&expanded, &expected),
            "fmap(xvar, f) should expand to f itself.\n\
             Got: {:?}\nExpected: {:?}",
            expanded,
            expected
        );
    }

    #[test]
    fn fmap_sum_inner_branches_correct() {
        let mut parser = Parser::new();
        define_fmap_sum(&mut parser);

        let expanded = parser
            .parse_rel_body("fmap((sum unit xvar), [$z -> (s $z)])")
            .expect("expand fmap(sum unit xvar)");

        // Expected: Or(
        //   Seq[(inl $x) -> $x, $x -> $x, $y -> (inl $y)],  // unit branch: identity
        //   Seq[(inr $x) -> $x, $z -> (s $z), $y -> (inr $y)]  // xvar branch: inc
        // )
        let expected = parser
            .parse_rel_body(
                "[(inl $x) -> $x ; $x -> $x ; $y -> (inl $y)] \
                 | [(inr $x) -> $x ; [$z -> (s $z)] ; $y -> (inr $y)]",
            )
            .expect("parse expected expansion");

        assert!(
            rel_shape_eq(&expanded, &expected),
            "fmap(sum unit xvar) inner branches should match.\n\
             Got: {:?}\nExpected: {:?}",
            expanded,
            expected
        );
    }

    #[test]
    fn fmap_nested_sum_inner_or_present() {
        let mut parser = Parser::new();
        define_fmap_sum(&mut parser);

        // fmap((sum (sum unit xvar) unit), f)
        // Left branch: fmap((sum unit xvar), f) → another Or
        // Right branch: fmap(unit, f) → identity
        let expanded = parser
            .parse_rel_body("fmap((sum (sum unit xvar) unit), [$z -> (s $z)])")
            .expect("expand nested fmap");

        // Top level should be Or.
        match &expanded {
            Rel::Or(left, right) => {
                // Left branch: Seq[(inl $x) -> $x, fmap(sum unit xvar, f), $y -> (inl $y)]
                // where fmap(sum unit xvar, f) should itself be an Or.
                match left.as_ref() {
                    Rel::Seq(factors) => {
                        assert_eq!(factors.len(), 3, "left branch should be Seq of 3");
                        // Middle element should be the nested Or from fmap(sum unit xvar).
                        assert!(
                            matches!(factors[1].as_ref(), Rel::Or(_, _)),
                            "Inner fmap(sum unit xvar) should produce Or, got {:?}",
                            factors[1]
                        );
                    }
                    _ => panic!("Left branch should be Seq, got {:?}", left),
                }
                // Right branch: Seq[(inr $x) -> $x, identity, $y -> (inr $y)]
                match right.as_ref() {
                    Rel::Seq(factors) => {
                        assert_eq!(factors.len(), 3, "right branch should be Seq of 3");
                        // Middle element should be identity (Atom).
                        assert!(
                            matches!(factors[1].as_ref(), Rel::Atom(_)),
                            "fmap(unit) should produce Atom, got {:?}",
                            factors[1]
                        );
                    }
                    _ => panic!("Right branch should be Seq, got {:?}", right),
                }
            }
            _ => panic!("Expected Or at top level, got {:?}", expanded),
        }
    }

    #[test]
    fn meta_var_binding_propagates_correctly() {
        // Verify that $a and $b bind to the correct sub-terms and propagate
        // into recursive calls. If bindings were swapped, the expansion
        // would have xvar (=f) in the left branch and identity in the right.
        let mut parser = Parser::new();
        define_m_pair(&mut parser);

        let expanded = parser
            .parse_rel_body("m((pair unit xvar), [$z -> (s $z)])")
            .expect("expand m(pair unit xvar)");

        // Should be Seq[m(unit, f), m(xvar, f)] = Seq[identity, f]
        match &expanded {
            Rel::Seq(factors) => {
                assert_eq!(factors.len(), 2, "pair body is Seq of 2");

                // First: m(unit, f) = identity ($x -> $x)
                let identity = parser.parse_rel_body("$x -> $x").expect("parse identity");
                assert!(
                    rel_shape_eq(factors[0].as_ref(), &identity),
                    "m(unit, f) should be identity, got {:?}",
                    factors[0]
                );

                // Second: m(xvar, f) = f ($z -> (s $z))
                let f_rel = parser.parse_rel_body("$z -> (s $z)").expect("parse f");
                assert!(
                    rel_shape_eq(factors[1].as_ref(), &f_rel),
                    "m(xvar, f) should be f, got {:?}",
                    factors[1]
                );
            }
            _ => panic!("Expected Seq from pair expansion, got {:?}", expanded),
        }
    }

    #[test]
    fn meta_var_binding_not_swapped() {
        // Like `meta_var_binding_propagates_correctly` but with reversed sub-terms
        // to confirm order matters.
        let mut parser = Parser::new();
        define_m_pair(&mut parser);

        // Now call with (pair xvar unit) — reversed from meta_var_binding_propagates_correctly.
        let expanded = parser
            .parse_rel_body("m((pair xvar unit), [$z -> (s $z)])")
            .expect("expand m(pair xvar unit)");

        // Should be Seq[m(xvar, f), m(unit, f)] = Seq[f, identity]
        match &expanded {
            Rel::Seq(factors) => {
                assert_eq!(factors.len(), 2);

                let f_rel = parser.parse_rel_body("$z -> (s $z)").expect("parse f");
                let identity = parser.parse_rel_body("$x -> $x").expect("parse identity");

                // First should be f (xvar), second should be identity (unit).
                assert!(
                    rel_shape_eq(factors[0].as_ref(), &f_rel),
                    "First should be f (xvar), got {:?}",
                    factors[0]
                );
                assert!(
                    rel_shape_eq(factors[1].as_ref(), &identity),
                    "Second should be identity (unit), got {:?}",
                    factors[1]
                );
            }
            _ => panic!("Expected Seq, got {:?}", expanded),
        }
    }

    #[test]
    fn all_term_params_macro() {
        // Macro with only term params (no relation params at all).
        // Note: meta-vars from term patterns cannot appear in rule LHS/RHS
        // (rules are NF-factored at parse time). So bodies must not reference $n.
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel tag(@z) { $x -> (tagged_z $x) }")
            .expect("tag/z");
        parser
            .parse_rel_def("rel tag(@(s $n)) { $x -> (tagged_s $x) }")
            .expect("tag/s");

        let r1 = parser.parse_rel_body("tag(z)").expect("expand tag(z)");
        let expected_z = parser
            .parse_rel_body("$x -> (tagged_z $x)")
            .expect("parse expected");
        assert!(
            rel_shape_eq(&r1, &expected_z),
            "tag(z) expansion mismatch.\nGot: {:?}\nExpected: {:?}",
            r1,
            expected_z
        );

        let r2 = parser
            .parse_rel_body("tag((s z))")
            .expect("expand tag((s z))");
        let expected_s = parser
            .parse_rel_body("$x -> (tagged_s $x)")
            .expect("parse expected");
        assert!(
            rel_shape_eq(&r2, &expected_s),
            "tag((s z)) expansion mismatch.\nGot: {:?}\nExpected: {:?}",
            r2,
            expected_s
        );
    }

    #[test]
    fn two_term_param_positions() {
        // Macro with two @-parameters.
        let mut parser = Parser::new();
        parser
            .parse_rel_def("rel combine(@z, @z) { $x -> (both_z $x) }")
            .expect("combine/z,z");
        parser
            .parse_rel_def("rel combine(@z, @(s $n)) { $x -> (z_and_s $x) }")
            .expect("combine/z,s");
        parser
            .parse_rel_def("rel combine(@(s $m), @z) { $x -> (s_and_z $x) }")
            .expect("combine/s,z");

        let r1 = parser
            .parse_rel_body("combine(z, z)")
            .expect("expand combine(z, z)");
        let e1 = parser
            .parse_rel_body("$x -> (both_z $x)")
            .expect("expected");
        assert!(rel_shape_eq(&r1, &e1), "combine(z,z) wrong: {:?}", r1);

        let r2 = parser
            .parse_rel_body("combine(z, (s z))")
            .expect("expand combine(z, (s z))");
        let e2 = parser
            .parse_rel_body("$x -> (z_and_s $x)")
            .expect("expected");
        assert!(rel_shape_eq(&r2, &e2), "combine(z,(s z)) wrong: {:?}", r2);

        let r3 = parser
            .parse_rel_body("combine((s z), z)")
            .expect("expand combine((s z), z)");
        let e3 = parser
            .parse_rel_body("$x -> (s_and_z $x)")
            .expect("expected");
        assert!(rel_shape_eq(&r3, &e3), "combine((s z),z) wrong: {:?}", r3);

        // No equation matches (s, s).
        let err = parser
            .parse_rel_body("combine((s z), (s z))")
            .expect_err("(s,s) should not match");
        assert!(err.message.contains("no matching equation"));
    }
}
