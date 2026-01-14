//! Compiler from parsed file format to Goal IR.
//!
//! Compiles relation definitions into the internal Goal representation.

use std::collections::HashMap;
use std::fmt;

use smallvec::SmallVec;

use crate::api::Engine;
use crate::constraint::ConstraintOps;
use crate::goal::{GoalId, RelId, RuleId};
use crate::nf::NF;
use crate::term::TermId;

use super::file_parser::{ParsedExpr, ParsedFile, ParsedTerm};

/// Compilation error with location information.
#[derive(Debug, Clone, PartialEq)]
pub struct CompileError {
    pub line: usize,
    pub message: String,
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.line, self.message)
    }
}

impl std::error::Error for CompileError {}

/// Compiler for relation definitions.
pub struct Compiler<'a, C: ConstraintOps + 'static> {
    engine: &'a mut Engine<C>,
    /// Map from relation name to RelId (for recursive calls).
    rel_ids: HashMap<String, RelId>,
}

impl<'a, C: ConstraintOps + Default + Clone + 'static> Compiler<'a, C> {
    /// Create a new compiler for the given engine.
    pub fn new(engine: &'a mut Engine<C>) -> Self {
        Self {
            engine,
            rel_ids: HashMap::new(),
        }
    }

    /// Compile a parsed file into the engine.
    ///
    /// Returns a map from relation names to their compiled GoalIds.
    pub fn compile_file(
        &mut self,
        file: ParsedFile,
    ) -> Result<HashMap<String, GoalId>, CompileError> {
        // First pass: register all relation names
        for rel in &file.relations {
            let rel_id = self.engine.define_relation(&rel.name);
            self.rel_ids.insert(rel.name.clone(), rel_id);
        }

        // Second pass: compile each relation body
        let mut relation_goals = HashMap::new();
        for rel in &file.relations {
            let rel_id = *self.rel_ids.get(&rel.name).unwrap();
            let body_id = self.compile_expr(&rel.body)?;

            // Wrap with Fix - this stores the goal in the goal store
            let fix_id = self.engine.fix(rel_id, body_id);

            relation_goals.insert(rel.name.clone(), fix_id);
        }

        Ok(relation_goals)
    }

    /// Compile an expression to a GoalId.
    fn compile_expr(&mut self, expr: &ParsedExpr) -> Result<GoalId, CompileError> {
        match expr {
            ParsedExpr::Rule { lhs, rhs, line } => {
                let rule_id = self.compile_rule(lhs, rhs, *line)?;
                Ok(self.engine.rule(rule_id))
            }
            ParsedExpr::Seq(exprs) => {
                let goal_ids: Result<SmallVec<[GoalId; 4]>, _> =
                    exprs.iter().map(|e| self.compile_expr(e)).collect();
                Ok(self.engine.seq(goal_ids?))
            }
            ParsedExpr::Alt(exprs) => {
                let goal_ids: Result<SmallVec<[GoalId; 2]>, _> =
                    exprs.iter().map(|e| self.compile_expr(e)).collect();
                Ok(self.engine.alt(goal_ids?))
            }
            ParsedExpr::Both(exprs) => {
                let goal_ids: Result<SmallVec<[GoalId; 4]>, _> =
                    exprs.iter().map(|e| self.compile_expr(e)).collect();
                Ok(self.engine.both(goal_ids?))
            }
            ParsedExpr::Call(name) => {
                let rel_id = self.rel_ids.get(name).ok_or_else(|| CompileError {
                    line: 0,
                    message: format!("Undefined relation: '{}'", name),
                })?;
                Ok(self.engine.call(*rel_id))
            }
            ParsedExpr::Term(term) => {
                // Bare term becomes identity relation: term -> term
                let rule_id = self.compile_rule(term, term, 0)?;
                Ok(self.engine.rule(rule_id))
            }
        }
    }

    /// Compile a rewrite rule to a RuleId (which references an NF).
    fn compile_rule(
        &mut self,
        lhs: &ParsedTerm,
        rhs: &ParsedTerm,
        _line: usize,
    ) -> Result<RuleId, CompileError> {
        let mut var_map: HashMap<String, u32> = HashMap::new();
        let mut next_var = 0u32;

        // Convert LHS term to TermId, assigning var indices
        let lhs_id = self.term_to_id(lhs, &mut var_map, &mut next_var)?;

        // Convert RHS term to TermId, reusing var indices for shared vars
        let rhs_id = self.term_to_id(rhs, &mut var_map, &mut next_var)?;

        // Factor the rule into NF
        let nf = NF::factor(lhs_id, rhs_id, C::default(), self.engine.terms_mut());

        // Add to rule store
        let rule_id = self.engine.rules_mut().add(nf);

        Ok(rule_id)
    }

    /// Convert a ParsedTerm to a TermId.
    ///
    /// Variables are assigned indices in order of first appearance.
    fn term_to_id(
        &self,
        term: &ParsedTerm,
        var_map: &mut HashMap<String, u32>,
        next_var: &mut u32,
    ) -> Result<TermId, CompileError> {
        match term {
            ParsedTerm::Var(name) => {
                let idx = if let Some(&idx) = var_map.get(name) {
                    idx
                } else {
                    let idx = *next_var;
                    var_map.insert(name.clone(), idx);
                    *next_var += 1;
                    idx
                };
                Ok(self.engine.var(idx))
            }
            ParsedTerm::Atom(name) => {
                let sym = self.engine.intern(name);
                Ok(self.engine.app(sym, SmallVec::new()))
            }
            ParsedTerm::App(ctor, args) => {
                let sym = self.engine.intern(ctor);
                let arg_ids: Result<SmallVec<[TermId; 4]>, _> = args
                    .iter()
                    .map(|arg| self.term_to_id(arg, var_map, next_var))
                    .collect();
                Ok(self.engine.app(sym, arg_ids?))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cli::file_parser::{FileParser, ParsedExpr, ParsedTerm, RelationDef};
    use crate::goal::Goal;

    // ========== TERM COMPILATION TESTS ==========

    #[test]
    fn compile_term_variable() {
        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);
        let mut var_map = HashMap::new();
        let mut next_var = 0;

        let term = ParsedTerm::Var("x".to_string());
        let id = compiler
            .term_to_id(&term, &mut var_map, &mut next_var)
            .unwrap();

        assert_eq!(engine.terms().is_var(id), Some(0));
        assert_eq!(next_var, 1);
    }

    #[test]
    fn compile_term_variable_reuses_index() {
        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);
        let mut var_map = HashMap::new();
        let mut next_var = 0;

        let term1 = ParsedTerm::Var("x".to_string());
        let term2 = ParsedTerm::Var("x".to_string());
        let id1 = compiler
            .term_to_id(&term1, &mut var_map, &mut next_var)
            .unwrap();
        let id2 = compiler
            .term_to_id(&term2, &mut var_map, &mut next_var)
            .unwrap();

        assert_eq!(id1, id2);
        assert_eq!(next_var, 1);
    }

    #[test]
    fn compile_term_multiple_variables() {
        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);
        let mut var_map = HashMap::new();
        let mut next_var = 0;

        let term_x = ParsedTerm::Var("x".to_string());
        let term_y = ParsedTerm::Var("y".to_string());
        let id_x = compiler
            .term_to_id(&term_x, &mut var_map, &mut next_var)
            .unwrap();
        let id_y = compiler
            .term_to_id(&term_y, &mut var_map, &mut next_var)
            .unwrap();

        assert_eq!(engine.terms().is_var(id_x), Some(0));
        assert_eq!(engine.terms().is_var(id_y), Some(1));
        assert_eq!(next_var, 2);
    }

    #[test]
    fn compile_term_atom() {
        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);
        let mut var_map = HashMap::new();
        let mut next_var = 0;

        let term = ParsedTerm::Atom("z".to_string());
        let id = compiler
            .term_to_id(&term, &mut var_map, &mut next_var)
            .unwrap();

        let (sym, args) = engine.terms().is_app(id).unwrap();
        assert_eq!(engine.symbols().resolve(sym), Some("z"));
        assert!(args.is_empty());
    }

    #[test]
    fn compile_term_application() {
        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);
        let mut var_map = HashMap::new();
        let mut next_var = 0;

        let term = ParsedTerm::App(
            "cons".to_string(),
            vec![
                ParsedTerm::Var("x".to_string()),
                ParsedTerm::Var("y".to_string()),
            ],
        );
        let id = compiler
            .term_to_id(&term, &mut var_map, &mut next_var)
            .unwrap();

        let (sym, args) = engine.terms().is_app(id).unwrap();
        assert_eq!(engine.symbols().resolve(sym), Some("cons"));
        assert_eq!(args.len(), 2);
        assert_eq!(engine.terms().is_var(args[0]), Some(0));
        assert_eq!(engine.terms().is_var(args[1]), Some(1));
    }

    #[test]
    fn compile_term_nested_application() {
        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);
        let mut var_map = HashMap::new();
        let mut next_var = 0;

        // (s (s z))
        let term = ParsedTerm::App(
            "s".to_string(),
            vec![ParsedTerm::App(
                "s".to_string(),
                vec![ParsedTerm::Atom("z".to_string())],
            )],
        );
        let id = compiler
            .term_to_id(&term, &mut var_map, &mut next_var)
            .unwrap();

        let (sym, args) = engine.terms().is_app(id).unwrap();
        assert_eq!(engine.symbols().resolve(sym), Some("s"));
        assert_eq!(args.len(), 1);

        let (inner_sym, inner_args) = engine.terms().is_app(args[0]).unwrap();
        assert_eq!(engine.symbols().resolve(inner_sym), Some("s"));
        assert_eq!(inner_args.len(), 1);

        let (leaf_sym, leaf_args) = engine.terms().is_app(inner_args[0]).unwrap();
        assert_eq!(engine.symbols().resolve(leaf_sym), Some("z"));
        assert!(leaf_args.is_empty());
    }

    // ========== RULE COMPILATION TESTS ==========

    #[test]
    fn compile_single_rule() {
        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);

        let lhs = ParsedTerm::Var("x".to_string());
        let rhs = ParsedTerm::Var("x".to_string());
        let rule_id = compiler.compile_rule(&lhs, &rhs, 1).unwrap();

        assert_eq!(rule_id, 0);
        assert!(engine.rules().get(rule_id).is_some());
    }

    #[test]
    fn compile_rule_with_different_vars() {
        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);

        // (cons z $y) -> $y
        let lhs = ParsedTerm::App(
            "cons".to_string(),
            vec![
                ParsedTerm::Atom("z".to_string()),
                ParsedTerm::Var("y".to_string()),
            ],
        );
        let rhs = ParsedTerm::Var("y".to_string());
        let rule_id = compiler.compile_rule(&lhs, &rhs, 1).unwrap();

        let nf = engine.rules().get(rule_id).unwrap();
        assert_eq!(nf.match_pats.len(), 1);
        assert_eq!(nf.build_pats.len(), 1);
    }

    // ========== EXPRESSION COMPILATION TESTS ==========

    #[test]
    fn compile_expr_alt() {
        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);

        let expr = ParsedExpr::Alt(vec![
            ParsedExpr::Rule {
                lhs: ParsedTerm::Var("x".to_string()),
                rhs: ParsedTerm::Var("x".to_string()),
                line: 1,
            },
            ParsedExpr::Rule {
                lhs: ParsedTerm::Var("y".to_string()),
                rhs: ParsedTerm::Var("y".to_string()),
                line: 2,
            },
        ]);

        let goal_id = compiler.compile_expr(&expr).unwrap();
        match engine.goals().get(goal_id) {
            Some(Goal::Alt(branches)) => assert_eq!(branches.len(), 2),
            _ => panic!("Expected Alt goal"),
        }
    }

    #[test]
    fn compile_expr_seq() {
        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);

        let expr = ParsedExpr::Seq(vec![
            ParsedExpr::Rule {
                lhs: ParsedTerm::Var("x".to_string()),
                rhs: ParsedTerm::Var("x".to_string()),
                line: 1,
            },
            ParsedExpr::Rule {
                lhs: ParsedTerm::Var("y".to_string()),
                rhs: ParsedTerm::Var("y".to_string()),
                line: 2,
            },
        ]);

        let goal_id = compiler.compile_expr(&expr).unwrap();
        match engine.goals().get(goal_id) {
            Some(Goal::Seq(steps)) => assert_eq!(steps.len(), 2),
            _ => panic!("Expected Seq goal"),
        }
    }

    #[test]
    fn compile_expr_both() {
        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);

        let expr = ParsedExpr::Both(vec![
            ParsedExpr::Rule {
                lhs: ParsedTerm::Var("x".to_string()),
                rhs: ParsedTerm::Var("x".to_string()),
                line: 1,
            },
            ParsedExpr::Rule {
                lhs: ParsedTerm::Var("y".to_string()),
                rhs: ParsedTerm::Var("y".to_string()),
                line: 2,
            },
        ]);

        let goal_id = compiler.compile_expr(&expr).unwrap();
        match engine.goals().get(goal_id) {
            Some(Goal::Both(constraints)) => assert_eq!(constraints.len(), 2),
            _ => panic!("Expected Both goal"),
        }
    }

    #[test]
    fn compile_expr_call_undefined_errors() {
        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);

        let expr = ParsedExpr::Call("undefined".to_string());
        let result = compiler.compile_expr(&expr);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.message.contains("Undefined relation"));
    }

    #[test]
    fn compile_expr_call_defined() {
        let mut engine: Engine<()> = Engine::new();
        let rel_id = engine.define_relation("test");
        let mut compiler = Compiler::new(&mut engine);
        compiler.rel_ids.insert("test".to_string(), rel_id);

        let expr = ParsedExpr::Call("test".to_string());
        let goal_id = compiler.compile_expr(&expr).unwrap();

        match engine.goals().get(goal_id) {
            Some(Goal::Call(r)) => assert_eq!(*r, rel_id),
            _ => panic!("Expected Call goal"),
        }
    }

    // ========== FILE COMPILATION TESTS ==========

    #[test]
    fn compile_empty_file() {
        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);

        let file = ParsedFile { relations: vec![] };
        let names = compiler.compile_file(file).unwrap();

        assert!(names.is_empty());
    }

    #[test]
    fn compile_single_relation() {
        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);

        let file = ParsedFile {
            relations: vec![RelationDef {
                name: "identity".to_string(),
                body: ParsedExpr::Rule {
                    lhs: ParsedTerm::Var("x".to_string()),
                    rhs: ParsedTerm::Var("x".to_string()),
                    line: 1,
                },
                line: 1,
            }],
        };
        let result = compiler.compile_file(file).unwrap();

        assert!(result.contains_key("identity"));
        assert_eq!(result.len(), 1);
        assert_eq!(engine.rel_name(0), Some("identity"));
    }

    #[test]
    fn compile_recursive_relation() {
        let input = r#"
            rel add {
                (cons z $y) -> $y
                | [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
            }
        "#;
        let mut parser = FileParser::new(input);
        let file = parser.parse_file().unwrap();

        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);
        let result = compiler.compile_file(file).unwrap();

        assert!(result.contains_key("add"));
        assert_eq!(result.len(), 1);

        // Check that the relation was defined
        assert_eq!(engine.rel_name(0), Some("add"));

        // The goal store should have multiple goals now
        assert!(engine.goals().len() > 0);
    }

    #[test]
    fn compile_multiple_relations() {
        let input = r#"
            rel first { $x -> $x }
            rel second { $y -> $y }
        "#;
        let mut parser = FileParser::new(input);
        let file = parser.parse_file().unwrap();

        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);
        let names = compiler.compile_file(file).unwrap();

        assert_eq!(names.len(), 2);
        assert_eq!(engine.rel_name(0), Some("first"));
        assert_eq!(engine.rel_name(1), Some("second"));
    }

    #[test]
    fn compile_relation_with_forward_call() {
        // Test that forward references work (second calls first, defined later)
        let input = r#"
            rel first { $x -> $x | second }
            rel second { $y -> $y }
        "#;
        let mut parser = FileParser::new(input);
        let file = parser.parse_file().unwrap();

        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);
        let names = compiler.compile_file(file).unwrap();

        assert_eq!(names.len(), 2);
    }

    #[test]
    fn compile_treecalc() {
        let input = r#"
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

        let mut engine: Engine<()> = Engine::new();
        let mut compiler = Compiler::new(&mut engine);
        let result = compiler.compile_file(file).unwrap();

        assert!(result.contains_key("app"));
        assert!(result.contains_key("eval"));
        assert_eq!(result.len(), 2);
        assert_eq!(engine.rel_name(0), Some("app"));
        assert_eq!(engine.rel_name(1), Some("eval"));
    }

    // ========== ERROR TESTS ==========

    #[test]
    fn compile_error_display() {
        let err = CompileError {
            line: 5,
            message: "Test error".to_string(),
        };
        assert_eq!(err.to_string(), "line 5: Test error");
    }
}
