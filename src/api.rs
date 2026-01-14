//! Public API for rwlog - relational programming via term rewriting.
//!
//! This module provides a high-level interface for defining relations,
//! building goals, and executing queries.

use std::sync::Arc;

use smallvec::SmallVec;

use crate::constraint::ConstraintOps;
use crate::eval::{step, EvalCtx, RuleStore, StepResult};
use crate::goal::{Goal, GoalId, GoalStore, RelId};
use crate::nf::NF;
use crate::symbol::SymbolStore;
use crate::task::Task;
use crate::term::{TermId, TermStore};

/// An answer from a query - a normal form representing a relation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Answer<C> {
    /// The normal form representing this answer.
    pub nf: NF<C>,
}

impl<C> Answer<C> {
    /// Create a new answer from a normal form.
    pub fn new(nf: NF<C>) -> Self {
        Self { nf }
    }
}

/// The main engine for executing relational queries.
///
/// The Engine manages:
/// - Symbol interning
/// - Term hashconsing
/// - Goal definitions
/// - Rule compilation
/// - Query execution
pub struct Engine<C: ConstraintOps + 'static> {
    /// Symbol store for interning function/relation names.
    symbols: Arc<SymbolStore>,
    /// Term store for hashconsing terms.
    terms: TermStore,
    /// Goal store for goal definitions.
    goals: GoalStore,
    /// Rule store for compiled rules.
    rules: RuleStore<C>,
    /// Next task ID.
    next_task_id: u32,
}

impl<C: ConstraintOps + 'static> Engine<C> {
    /// Create a new empty engine.
    pub fn new() -> Self {
        Self {
            symbols: Arc::new(SymbolStore::new()),
            terms: TermStore::new(),
            goals: GoalStore::new(),
            rules: RuleStore::new(),
            next_task_id: 0,
        }
    }

    /// Get a reference to the symbol store.
    pub fn symbols(&self) -> &SymbolStore {
        &self.symbols
    }

    /// Get a reference to the term store.
    pub fn terms(&self) -> &TermStore {
        &self.terms
    }

    /// Get a mutable reference to the term store.
    pub fn terms_mut(&mut self) -> &mut TermStore {
        &mut self.terms
    }

    /// Get a mutable reference to the goal store.
    pub fn goals_mut(&mut self) -> &mut GoalStore {
        &mut self.goals
    }

    /// Get a reference to the goal store.
    pub fn goals(&self) -> &GoalStore {
        &self.goals
    }

    /// Get a mutable reference to the rule store.
    pub fn rules_mut(&mut self) -> &mut RuleStore<C> {
        &mut self.rules
    }

    /// Get a reference to the rule store.
    pub fn rules(&self) -> &RuleStore<C> {
        &self.rules
    }

    /// Intern a symbol (function or relation name).
    pub fn intern(&self, name: &str) -> lasso::Spur {
        self.symbols.intern(name)
    }

    /// Create a variable term.
    pub fn var(&self, index: u32) -> TermId {
        self.terms.var(index)
    }

    /// Create an application term.
    pub fn app(&self, func: lasso::Spur, args: impl Into<SmallVec<[TermId; 4]>>) -> TermId {
        self.terms.app(func, args.into())
    }

    /// Define a new relation with the given name using the goal store.
    /// Returns the RelId for use in Fix/Call goals.
    pub fn define_relation(&mut self, name: &str) -> RelId {
        self.goals.new_rel(name)
    }

    /// Get the name of a relation by ID.
    pub fn rel_name(&self, rel_id: RelId) -> Option<&str> {
        self.goals.rel_name(rel_id)
    }

    /// Add a goal to the goal store.
    pub fn add_goal(&mut self, goal: Goal) -> GoalId {
        self.goals.add_goal(goal)
    }

    /// Create a Fail goal.
    pub fn fail(&mut self) -> GoalId {
        self.goals.fail()
    }

    /// Create a Rule goal.
    pub fn rule(&mut self, rule_id: u32) -> GoalId {
        self.goals.rule(rule_id)
    }

    /// Create an Alt (disjunction) goal.
    pub fn alt(&mut self, branches: impl Into<SmallVec<[GoalId; 2]>>) -> GoalId {
        self.goals.alt(branches)
    }

    /// Create a Seq (sequential composition) goal.
    pub fn seq(&mut self, steps: impl Into<SmallVec<[GoalId; 4]>>) -> GoalId {
        self.goals.seq(steps)
    }

    /// Create a Both (conjunction/meet) goal.
    pub fn both(&mut self, goals: impl Into<SmallVec<[GoalId; 4]>>) -> GoalId {
        self.goals.both(goals)
    }

    /// Create a Fix (recursive definition) goal.
    pub fn fix(&mut self, rel_id: RelId, body: GoalId) -> GoalId {
        self.goals.fix(rel_id, body)
    }

    /// Create a Call (recursive call) goal.
    pub fn call(&mut self, rel_id: RelId) -> GoalId {
        self.goals.call(rel_id)
    }

    /// Create a task for evaluating a goal with the given input.
    fn create_task(&mut self, goal_id: GoalId, input: NF<C>) -> Task<C> {
        let id = self.next_task_id;
        self.next_task_id += 1;
        Task::new(id, goal_id, input)
    }

    /// Execute a query and collect all answers up to a limit.
    ///
    /// The input is the initial normal form (typically an identity relation).
    /// The max_steps parameter limits computation to prevent infinite loops.
    pub fn query(&mut self, goal_id: GoalId, input: NF<C>, max_steps: usize) -> Vec<Answer<C>> {
        let mut task = self.create_task(goal_id, input);
        let mut answers = Vec::new();

        for _ in 0..max_steps {
            let mut ctx = EvalCtx {
                goals: &self.goals,
                rules: &self.rules,
                terms: &mut self.terms,
            };

            match step(&mut task, &mut ctx) {
                StepResult::Continue => continue,
                StepResult::Yielded(nf) => {
                    // Check if there are continuations to process
                    if task.kont_is_empty() {
                        // No continuations - this is a final answer
                        answers.push(Answer::new(nf));
                        // After yielding, backtrack to find more answers
                        let mut ctx2 = EvalCtx {
                            goals: &self.goals,
                            rules: &self.rules,
                            terms: &mut self.terms,
                        };
                        crate::eval::backtrack(&mut task, &mut ctx2);
                    } else {
                        // Process the yield through continuations (e.g., Seq needs to continue)
                        let mut ctx2 = EvalCtx {
                            goals: &self.goals,
                            rules: &self.rules,
                            terms: &mut self.terms,
                        };
                        let resume_result =
                            crate::eval::resume_after_yield(&mut task, nf, &mut ctx2);
                        // resume_after_yield may return Yielded when continuation completes
                        // (e.g., Seq done, or Alt yielding to try more branches)
                        if let StepResult::Yielded(final_nf) = resume_result {
                            // Always collect yields from resume_after_yield
                            answers.push(Answer::new(final_nf));
                            // Backtrack to find more answers (will try remaining Alt branches, etc.)
                            let mut ctx3 = EvalCtx {
                                goals: &self.goals,
                                rules: &self.rules,
                                terms: &mut self.terms,
                            };
                            crate::eval::backtrack(&mut task, &mut ctx3);
                        }
                        // If Continue, the next step() will continue processing
                    }
                }
                StepResult::Done => break,
                StepResult::Blocked(rel_id) => {
                    // Find the matching FixFrame and recursively evaluate
                    if let Some(fix_goal) = task.find_fix_goal(rel_id) {
                        // Recursively query the Fix goal with the current input
                        // This ensures nested Calls can also resolve via the FixFrame
                        let recursive_input = task.input.clone();
                        let recursive_answers = self.query(fix_goal, recursive_input, max_steps / 2);

                        if recursive_answers.is_empty() {
                            // No answers from recursive call - backtrack
                            let mut ctx2 = EvalCtx {
                                goals: &self.goals,
                                rules: &self.rules,
                                terms: &mut self.terms,
                            };
                            crate::eval::backtrack(&mut task, &mut ctx2);
                        } else {
                            // Resume with the answers from the recursive call
                            let call_answers: Vec<NF<C>> =
                                recursive_answers.into_iter().map(|a| a.nf).collect();
                            let mut ctx2 = EvalCtx {
                                goals: &self.goals,
                                rules: &self.rules,
                                terms: &mut self.terms,
                            };
                            crate::eval::resume_after_call(&mut task, call_answers, &mut ctx2);
                        }
                    } else {
                        // No matching FixFrame found - this is an error
                        break;
                    }
                }
            }
        }

        answers
    }

    /// Execute a query with an identity input (most common case).
    pub fn query_identity(&mut self, goal_id: GoalId, max_steps: usize) -> Vec<Answer<C>> {
        let input = NF::identity(C::default());
        self.query(goal_id, input, max_steps)
    }
}

impl<C: ConstraintOps + 'static> Default for Engine<C> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use smallvec::smallvec;

    // ========== ENGINE CREATION TESTS ==========

    #[test]
    fn engine_new() {
        let engine: Engine<()> = Engine::new();
        assert_eq!(engine.next_task_id, 0);
    }

    #[test]
    fn engine_default() {
        let engine: Engine<()> = Engine::default();
        assert_eq!(engine.next_task_id, 0);
    }

    // ========== SYMBOL INTERNING TESTS ==========

    #[test]
    fn engine_intern_symbol() {
        let engine: Engine<()> = Engine::new();
        let sym1 = engine.intern("foo");
        let sym2 = engine.intern("foo");
        assert_eq!(sym1, sym2);
    }

    #[test]
    fn engine_intern_different_symbols() {
        let engine: Engine<()> = Engine::new();
        let sym1 = engine.intern("foo");
        let sym2 = engine.intern("bar");
        assert_ne!(sym1, sym2);
    }

    // ========== TERM CREATION TESTS ==========

    #[test]
    fn engine_create_var() {
        let engine: Engine<()> = Engine::new();
        let v0 = engine.var(0);
        let v1 = engine.var(1);
        assert_ne!(v0, v1);
    }

    #[test]
    fn engine_create_app() {
        let engine: Engine<()> = Engine::new();
        let f = engine.intern("f");
        let v0 = engine.var(0);
        let app = engine.app(f, smallvec![v0]);
        assert_ne!(app, v0);
    }

    #[test]
    fn engine_app_hashcons() {
        let engine: Engine<()> = Engine::new();
        let f = engine.intern("f");
        let v0 = engine.var(0);
        let app1 = engine.app(f, smallvec![v0]);
        let app2 = engine.app(f, smallvec![v0]);
        assert_eq!(app1, app2);
    }

    // ========== RELATION DEFINITION TESTS ==========

    #[test]
    fn engine_define_relation() {
        let mut engine: Engine<()> = Engine::new();
        let rel = engine.define_relation("append");
        assert_eq!(rel, 0);
    }

    #[test]
    fn engine_define_multiple_relations() {
        let mut engine: Engine<()> = Engine::new();
        let rel1 = engine.define_relation("append");
        let rel2 = engine.define_relation("member");
        assert_eq!(rel1, 0);
        assert_eq!(rel2, 1);
    }

    #[test]
    fn engine_rel_name() {
        let mut engine: Engine<()> = Engine::new();
        let rel = engine.define_relation("append");
        assert_eq!(engine.rel_name(rel), Some("append"));
        assert_eq!(engine.rel_name(999), None);
    }

    // ========== GOAL STORE TESTS ==========

    #[test]
    fn engine_add_goal() {
        let mut engine: Engine<()> = Engine::new();
        let goal_id = engine.add_goal(Goal::Fail);
        assert_eq!(goal_id, 0);
    }

    #[test]
    fn engine_add_multiple_goals() {
        let mut engine: Engine<()> = Engine::new();
        let g1 = engine.add_goal(Goal::Fail);
        let g2 = engine.add_goal(Goal::Fail);
        assert_eq!(g1, 0);
        assert_eq!(g2, 1);
    }

    #[test]
    fn engine_fail_goal() {
        let mut engine: Engine<()> = Engine::new();
        let g = engine.fail();
        assert_eq!(engine.goals().get(g), Some(&Goal::Fail));
    }

    #[test]
    fn engine_rule_goal() {
        let mut engine: Engine<()> = Engine::new();
        let g = engine.rule(42);
        assert_eq!(engine.goals().get(g), Some(&Goal::Rule(42)));
    }

    #[test]
    fn engine_alt_goal() {
        let mut engine: Engine<()> = Engine::new();
        let g1 = engine.fail();
        let g2 = engine.fail();
        let alt = engine.alt(smallvec![g1, g2]);
        assert!(matches!(engine.goals().get(alt), Some(Goal::Alt(_))));
    }

    #[test]
    fn engine_seq_goal() {
        let mut engine: Engine<()> = Engine::new();
        let g1 = engine.fail();
        let g2 = engine.fail();
        let seq = engine.seq(smallvec![g1, g2]);
        assert!(matches!(engine.goals().get(seq), Some(Goal::Seq(_))));
    }

    #[test]
    fn engine_both_goal() {
        let mut engine: Engine<()> = Engine::new();
        let g1 = engine.fail();
        let g2 = engine.fail();
        let both = engine.both(smallvec![g1, g2]);
        assert!(matches!(engine.goals().get(both), Some(Goal::Both(_))));
    }

    #[test]
    fn engine_fix_call_goals() {
        let mut engine: Engine<()> = Engine::new();
        let rel = engine.define_relation("test");
        let body = engine.fail();
        let fix = engine.fix(rel, body);
        let call = engine.call(rel);
        assert!(matches!(engine.goals().get(fix), Some(Goal::Fix(_, _))));
        assert!(matches!(engine.goals().get(call), Some(Goal::Call(_))));
    }

    // ========== QUERY TESTS ==========

    #[test]
    fn query_fail_goal_returns_empty() {
        let mut engine: Engine<()> = Engine::new();
        let fail_id = engine.add_goal(Goal::Fail);
        let answers = engine.query_identity(fail_id, 1000);
        assert!(answers.is_empty());
    }

    #[test]
    fn query_rule_goal_returns_nf() {
        let mut engine: Engine<()> = Engine::new();

        // Create an identity rule with arity 0 (matches identity input)
        let nf: NF<()> = NF::identity(());
        let rule_id = engine.rules_mut().add(nf);

        let rule_goal = engine.add_goal(Goal::Rule(rule_id));
        let answers = engine.query_identity(rule_goal, 1000);
        assert_eq!(answers.len(), 1);
    }

    #[test]
    fn query_alt_goal_returns_multiple_answers() {
        let mut engine: Engine<()> = Engine::new();

        // Create two rules with arity 0
        let nf1: NF<()> = NF::identity(());
        let nf2: NF<()> = NF::identity(());
        let rule1 = engine.rules_mut().add(nf1);
        let rule2 = engine.rules_mut().add(nf2);

        let g1 = engine.add_goal(Goal::Rule(rule1));
        let g2 = engine.add_goal(Goal::Rule(rule2));
        let alt = engine.add_goal(Goal::Alt(smallvec![g1, g2]));

        let answers = engine.query_identity(alt, 1000);
        assert_eq!(answers.len(), 2);
    }

    #[test]
    fn query_seq_goal_composes_rules() {
        let mut engine: Engine<()> = Engine::new();

        // Create identity rules that compose to identity
        let nf: NF<()> = NF::identity(());
        let rule_id = engine.rules_mut().add(nf);

        let g1 = engine.add_goal(Goal::Rule(rule_id));
        let g2 = engine.add_goal(Goal::Rule(rule_id));
        let seq = engine.add_goal(Goal::Seq(smallvec![g1, g2]));

        let answers = engine.query_identity(seq, 1000);
        assert_eq!(answers.len(), 1);
    }

    /// Regression test for backward query bug.
    ///
    /// When Seq(Alt(...), rule) is evaluated:
    /// 1. Alt yields intermediate result with AltNext continuation
    /// 2. SeqNext continuation should compose that result with `rule`
    /// 3. BUG: resume_after_yield returning Yielded was treated as final,
    ///    causing backtrack to skip SeqNext instead of processing it
    #[test]
    fn query_seq_of_alt_composes_all_branches() {
        let mut engine: Engine<()> = Engine::new();

        // Create two identity rules for Alt
        let nf1: NF<()> = NF::identity(());
        let nf2: NF<()> = NF::identity(());
        let rule1 = engine.rules_mut().add(nf1);
        let rule2 = engine.rules_mut().add(nf2);

        // Create third identity rule for Seq composition
        let nf3: NF<()> = NF::identity(());
        let rule3 = engine.rules_mut().add(nf3);

        // Build: Seq(Alt(rule1, rule2), rule3)
        let g1 = engine.add_goal(Goal::Rule(rule1));
        let g2 = engine.add_goal(Goal::Rule(rule2));
        let alt = engine.add_goal(Goal::Alt(smallvec![g1, g2]));
        let g3 = engine.add_goal(Goal::Rule(rule3));
        let seq = engine.add_goal(Goal::Seq(smallvec![alt, g3]));

        // Each Alt branch should compose with rule3
        // Bug: Would incorrectly return 2 answers from Alt without composing
        let answers = engine.query_identity(seq, 1000);

        // With identity rules, we should get 2 answers (one per Alt branch,
        // each composed with rule3 which is also identity)
        assert_eq!(
            answers.len(),
            2,
            "Seq(Alt(r1,r2), r3) should yield 2 composed answers, not intermediate Alt results"
        );
    }

    #[test]
    fn query_both_goal_meets_rules() {
        let mut engine: Engine<()> = Engine::new();

        // Create identity rules
        let nf: NF<()> = NF::identity(());
        let rule_id = engine.rules_mut().add(nf);

        let g1 = engine.add_goal(Goal::Rule(rule_id));
        let g2 = engine.add_goal(Goal::Rule(rule_id));
        let both = engine.add_goal(Goal::Both(smallvec![g1, g2]));

        let answers = engine.query_identity(both, 1000);
        assert_eq!(answers.len(), 1);
    }

    // ========== ANSWER TESTS ==========

    #[test]
    fn answer_new() {
        let nf: NF<()> = NF::identity(());
        let answer = Answer::new(nf.clone());
        assert_eq!(answer.nf, nf);
    }

    // ========== INTEGRATION TESTS ==========

    #[test]
    fn integration_simple_query() {
        let mut engine: Engine<()> = Engine::new();

        // Create a simple arity-0 rule that yields one answer
        let nf: NF<()> = NF::identity(());
        let rule_id = engine.rules_mut().add(nf);
        let goal = engine.add_goal(Goal::Rule(rule_id));

        let answers = engine.query_identity(goal, 1000);
        assert_eq!(answers.len(), 1);
    }

    #[test]
    fn integration_multiple_facts() {
        let mut engine: Engine<()> = Engine::new();

        // Create two arity-0 rules
        let nf1: NF<()> = NF::identity(());
        let nf2: NF<()> = NF::identity(());

        let rule1 = engine.rules_mut().add(nf1);
        let rule2 = engine.rules_mut().add(nf2);

        let g1 = engine.add_goal(Goal::Rule(rule1));
        let g2 = engine.add_goal(Goal::Rule(rule2));
        let alt = engine.add_goal(Goal::Alt(smallvec![g1, g2]));

        let answers = engine.query_identity(alt, 1000);
        assert_eq!(answers.len(), 2);
    }
}
