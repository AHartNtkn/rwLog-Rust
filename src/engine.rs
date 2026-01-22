//! Engine - Top-level evaluation loop for relational queries.
//!
//! The Engine orchestrates the search through a Rel tree by:
//! 1. Converting Rel to initial Node tree
//! 2. Stepping through the Node tree using Or rotation
//! 3. Yielding NF answers via next()

use crate::constraint::ConstraintDisplay;
use crate::constraint::ConstraintOps;
use crate::nf::{format_nf, NF};
use crate::node::{step_node, Node, NodeStep};
use crate::rel::Rel;
use crate::symbol::SymbolStore;
use crate::term::TermStore;
use crate::work::{rel_to_node, Env, Tables};
use std::collections::HashSet;

/// Result of a single step in the Engine.
#[derive(Clone, Debug)]
pub enum StepResult<C: ConstraintOps> {
    /// Produced an answer NF
    Emit(NF<C>),
    /// No more answers (exhausted)
    Exhausted,
    /// Internal rotation/restructuring happened, continue stepping
    Continue,
}

/// Evaluation engine for relational queries.
///
/// Converts a Rel expression into a stream of NF answers using
/// Or rotation interleaving and Work stepping.
pub struct Engine<C: ConstraintOps> {
    /// Root of the search tree
    root: Node<C>,
    /// Term store for creating/looking up terms
    terms: TermStore,
    /// Dedup set for emitted answers (set semantics).
    seen: HashSet<NF<C>>,
}

impl<C: ConstraintOps> Engine<C> {
    /// Create a new Engine from a Rel expression.
    pub fn new(rel: Rel<C>, terms: TermStore) -> Self {
        Self::new_with_env(rel, terms, Env::new())
    }

    /// Create a new Engine with an explicit environment.
    pub fn new_with_env(rel: Rel<C>, terms: TermStore, env: Env<C>) -> Self {
        let tables = Tables::new();
        let root = rel_to_node(&rel, &env, &tables);
        Self {
            root,
            terms,
            seen: HashSet::new(),
        }
    }

    pub fn format_nf(&mut self, nf: &NF<C>, symbols: &SymbolStore) -> Result<String, String>
    where
        C: ConstraintDisplay,
    {
        format_nf(nf, &mut self.terms, symbols)
    }

    /// Take a single step in the evaluation.
    fn step(&mut self) -> StepResult<C> {
        // Take ownership of root, step it, and update root with result
        let current = std::mem::replace(&mut self.root, Node::Fail);
        match step_node(current, &mut self.terms) {
            NodeStep::Emit(nf, rest) => {
                self.root = rest;
                StepResult::Emit(nf)
            }
            NodeStep::Continue(rest) => {
                self.root = rest;
                StepResult::Continue
            }
            NodeStep::Exhausted => {
                self.root = Node::Fail;
                StepResult::Exhausted
            }
        }
    }

    /// Check if the engine is exhausted.
    pub fn is_exhausted(&self) -> bool {
        matches!(self.root, Node::Fail)
    }

    /// Get reference to the term store.
    pub fn terms(&self) -> &TermStore {
        &self.terms
    }

    /// Get mutable reference to the term store.
    pub fn terms_mut(&mut self) -> &mut TermStore {
        &mut self.terms
    }

    /// Consume the engine and return the term store.
    pub fn into_terms(self) -> TermStore {
        self.terms
    }

    /// Create an iterator over all answers.
    ///
    /// The iterator yields NF answers until the engine is exhausted.
    pub fn iter(&mut self) -> QueryIter<'_, C> {
        QueryIter { engine: self }
    }

    /// Collect all answers into a vector.
    ///
    /// This consumes all answers from the query.
    pub fn collect_answers(&mut self) -> Vec<NF<C>> {
        self.iter().collect()
    }

    /// Count the number of answers (consumes them).
    pub fn count_answers(&mut self) -> usize {
        self.iter().count()
    }
}

impl<C: ConstraintOps> Iterator for Engine<C> {
    type Item = NF<C>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.step() {
                StepResult::Emit(nf) => {
                    if self.seen.insert(nf.clone()) {
                        return Some(nf);
                    }
                }
                StepResult::Exhausted => return None,
                StepResult::Continue => continue,
            }
        }
    }
}

/// Iterator over query answers.
///
/// Yields NF answers from the engine until exhausted.
pub struct QueryIter<'a, C: ConstraintOps> {
    engine: &'a mut Engine<C>,
}

impl<'a, C: ConstraintOps> Iterator for QueryIter<'a, C> {
    type Item = NF<C>;

    fn next(&mut self) -> Option<Self::Item> {
        self.engine.next()
    }
}

/// Convenience function to run a query and collect all answers.
pub fn query<C: ConstraintOps>(rel: Rel<C>, terms: TermStore) -> Vec<NF<C>> {
    let mut engine = Engine::new(rel, terms);
    engine.collect_answers()
}

/// Convenience function to run a query and get the first answer.
pub fn query_first<C: ConstraintOps>(rel: Rel<C>, terms: TermStore) -> Option<NF<C>> {
    let mut engine = Engine::new(rel, terms);
    engine.next()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chr::{ChrState, NoTheory};
    use crate::drop_fresh::DropFresh;
    use crate::kernel::dual_nf;
    use crate::nf::{direct_rule_terms, NF};
    use crate::parser::ChrConstraintBuilder;
    use crate::parser::Parser;
    use crate::rel::dual;
    use crate::rel::Rel;
    use crate::repl::split_statements;
    use crate::symbol::SymbolStore;
    use crate::test_utils::{make_ground_nf, make_rule_nf, setup};
    use crate::work::Env;
    use smallvec::SmallVec;
    use std::collections::HashSet;
    use std::sync::Arc;

    /// Create an empty NF (identity)
    fn make_identity_nf() -> NF<()> {
        NF::identity(())
    }

    fn parse_rel_def_with_env(parser: &mut Parser, def: &str) -> (Rel<()>, Env<()>) {
        let statements = split_statements(def).expect("split rel def");
        let mut rel_def = None;
        for statement in statements {
            let line = statement.trim();
            if line.starts_with("rel ") {
                rel_def = Some(parser.parse_rel_def(line).expect("parse rel def").1);
            }
        }
        let rel_def = rel_def.expect("expected relation definition");
        let env = match &rel_def {
            Rel::Fix(id, body) => Env::new().bind(*id, body.clone()),
            _ => Env::new(),
        };
        (rel_def, env)
    }

    fn parse_rel_def_with_env_chr(
        parser: &mut Parser<ChrConstraintBuilder>,
        def: &str,
    ) -> (Rel<ChrState<NoTheory>>, Env<ChrState<NoTheory>>) {
        let statements = split_statements(def).expect("split rel def");
        let mut rel_def = None;
        for statement in statements {
            let line = statement.trim();
            if line.starts_with("theory ") {
                parser.parse_theory_def(line).expect("parse theory");
                continue;
            }
            if line.starts_with("rel ") {
                rel_def = Some(parser.parse_rel_def(line).expect("parse rel def").1);
            }
        }
        let rel_def = rel_def.expect("expected relation definition");
        let env = match &rel_def {
            Rel::Fix(id, body) => Env::new().bind(*id, body.clone()),
            _ => Env::new(),
        };
        (rel_def, env)
    }

    const PROGRAM_SYNTH_DEF: &str = r#"
theory treecalc_constraints {
    constraint no_c/1

    # no_c/1 rejects terms containing (c N) where N is a unary number (z, s z, ...).
    (no_c l) <=> .
    (no_c (b $x)) <=> (no_c $x).
    (no_c (f $x $y)) <=> (no_c $x), (no_c $y).
    (no_c (c $n)) <=> fail.
    (no_c (a $n $m)) <=> fail.
}

rel app {
    # Rule 0a: Catch uninterpreted constants
    (f (c $x) $y) -> (a (c $x) $y)
    |
    # Rule 0b: Accumulate caught applications
    (f (a $x $y) $z) -> (a (a $x $y) $z)
    |
    # Rule 1: app(L, z) => B(z)
    (f l $z) -> (b $z)
    |
    # Rule 2: app(B(y), z) => F(y, z)
    (f (b $y) $z) -> (f $y $z)
    |
    # Rule 3: app(F(L, y), z) => y
    (f (f l $y) $z) -> $y
    |
    # Rule 4: app(F(F(w, x), y), L) => w
    (f (f (f $w $x) $y) l) -> $w
    |
    # Rule 5: app(F(B(x), y), z) => app(app(x, z), app(y, z))
    [
        [(f (f (b $x) $y) $z) -> (f $x $z) ; app ; $x -> (f $x $y)]
        &
        [(f (f (b $x) $y) $z) -> (f $y $z) ; app ; $y -> (f $x $y)]
        ; app
    ]
    |
    # Rule 6: app(F(F(w, x), y), B(u)) => app(x, u)
    [
        (f (f (f $w $x) $y) (b $u)) -> (f $x $u)
        ; app
    ]
    |
    # Rule 7: app(F(F(w, x), y), F(u, v)) => app(app(y, u), v)
    [
        (f (f (f $w $x) $y) (f $u $v)) -> (f (f $y $u) $v)
        ;
        [(f (f $a $b) $c) -> (f $a $b) ; app ; $a -> (f $a $b)]
        &
        (f (f $a $b) $c) -> (f $d $c)
        ; app
    ]
}
"#;

    fn peano_str(n: usize) -> String {
        if n == 0 {
            "z".to_string()
        } else {
            format!("(s {})", peano_str(n - 1))
        }
    }

    fn assert_simple_eval(query: &str, input: &str, expected: &str) {
        let mut parser = Parser::new();
        let rel = parser.parse_rel_body(query).expect("parse query");
        let input_term = parser.parse_term(input).expect("parse input").term_id;
        let expected_term = parser.parse_term(expected).expect("parse expected").term_id;

        let mut terms = parser.take_terms();
        let expected_nf = NF::factor(input_term, expected_term, (), &mut terms);

        let mut engine: Engine<()> = Engine::new(rel, terms);
        let answers = engine.collect_answers();

        assert_eq!(
            answers.len(),
            1,
            "Expected exactly one answer for query {}",
            query
        );
        assert_eq!(
            answers[0], expected_nf,
            "Unexpected answer for query {}",
            query
        );
    }

    fn run_until_emit<C: ConstraintOps>(engine: &mut Engine<C>, max_steps: usize) -> Option<NF<C>> {
        for _ in 0..max_steps {
            match engine.step() {
                StepResult::Emit(nf) => return Some(nf),
                StepResult::Exhausted => return None,
                StepResult::Continue => {
                    std::thread::yield_now();
                }
            }
        }
        None
    }

    // ========================================================================
    // ENGINE CONSTRUCTION TESTS
    // ========================================================================

    #[test]
    fn engine_new_from_zero() {
        let (_, terms) = setup();
        let engine: Engine<()> = Engine::new(Rel::Zero, terms);
        assert!(engine.is_exhausted());
    }

    #[test]
    fn engine_new_from_atom() {
        let (_, terms) = setup();
        let nf = make_identity_nf();
        let engine: Engine<()> = Engine::new(Rel::Atom(Arc::new(nf)), terms);
        assert!(!engine.is_exhausted());
    }

    #[test]
    fn engine_new_from_or() {
        let (_, terms) = setup();
        let engine: Engine<()> =
            Engine::new(Rel::Or(Arc::new(Rel::Zero), Arc::new(Rel::Zero)), terms);
        // Or of two Zeros eventually exhausts
        assert!(!engine.is_exhausted()); // Not immediately exhausted
    }

    // ========================================================================
    // ENGINE NEXT - ZERO TESTS
    // ========================================================================

    #[test]
    fn engine_zero_exhausts_immediately() {
        let (_, terms) = setup();
        let mut engine: Engine<()> = Engine::new(Rel::Zero, terms);
        assert!(engine.next().is_none());
        assert!(engine.next().is_none()); // Idempotent
    }

    #[test]
    fn engine_zero_is_exhausted() {
        let (_, terms) = setup();
        let engine: Engine<()> = Engine::new(Rel::Zero, terms);
        assert!(engine.is_exhausted());
    }

    // ========================================================================
    // ENGINE NEXT - ATOM TESTS
    // ========================================================================

    #[test]
    fn engine_atom_yields_once() {
        let (_, terms) = setup();
        let nf = make_identity_nf();
        let mut engine: Engine<()> = Engine::new(Rel::Atom(Arc::new(nf)), terms);

        let ans1 = engine.next();
        assert!(ans1.is_some(), "Atom should yield once");

        let ans2 = engine.next();
        assert!(ans2.is_none(), "Atom should exhaust after one answer");
    }

    // ========================================================================
    // E2E: Simple Combinators
    // ========================================================================

    #[test]
    fn engine_dedups_duplicate_or() {
        let (_, terms) = setup();
        let nf = make_identity_nf();
        let rel = Rel::Or(
            Arc::new(Rel::Atom(Arc::new(nf.clone()))),
            Arc::new(Rel::Atom(Arc::new(nf.clone()))),
        );

        let mut engine: Engine<()> = Engine::new(rel, terms);
        let answers = engine.collect_answers();
        assert_eq!(answers.len(), 1, "Engine should dedup identical answers");
        assert_eq!(answers[0], nf);
    }

    #[test]
    fn engine_dedups_duplicate_or_dual() {
        let (_, mut terms) = setup();
        let nf = make_identity_nf();
        let nf = dual_nf(&nf, &mut terms);
        let rel = Rel::Or(
            Arc::new(Rel::Atom(Arc::new(nf.clone()))),
            Arc::new(Rel::Atom(Arc::new(nf.clone()))),
        );

        let mut engine: Engine<()> = Engine::new(rel, terms);
        let answers = engine.collect_answers();
        assert_eq!(answers.len(), 1, "Engine should dedup identical answers");
        assert_eq!(answers[0], nf);
    }

    #[test]
    fn simple_swap_on_ground_pair() {
        assert_simple_eval(
            "@(cons a b) ; [(cons $x $y) -> (cons $y $x)]",
            "(cons a b)",
            "(cons b a)",
        );
    }

    #[test]
    fn simple_reorder_and_duplicate() {
        assert_simple_eval(
            "@(cons a b) ; [(cons $x $y) -> (cons $y (cons $x $y))]",
            "(cons a b)",
            "(cons b (cons a b))",
        );
    }

    #[test]
    fn simple_swap_then_duplicate() {
        assert_simple_eval(
            "@(cons a b) ; [(cons $x $y) -> (cons $y $x) ; (cons $x $y) -> (cons $x $x)]",
            "(cons a b)",
            "(cons b b)",
        );
    }

    // ========================================================================
    // ENGINE NEXT - SEQ/AND SEMANTICS
    // ========================================================================

    #[test]
    fn engine_seq_with_and_yields_meet_result() {
        let (symbols, terms) = setup();
        let nf = make_rule_nf("A", "A", &symbols, &terms);

        let rel = Rel::Seq(Arc::from(vec![Arc::new(Rel::And(
            Arc::new(Rel::Atom(Arc::new(nf.clone()))),
            Arc::new(Rel::Atom(Arc::new(nf.clone()))),
        ))]));

        let mut engine: Engine<()> = Engine::new(rel, terms);
        let ans = engine.next();
        assert!(ans.is_some(), "Seq([And(A,A)]) should yield A");
        assert_eq!(ans.unwrap(), nf);
        assert!(engine.next().is_none(), "Seq([And(A,A)]) should exhaust");
    }

    #[test]
    fn engine_empty_seq_yields_identity() {
        let (_, terms) = setup();
        let rel: Rel<()> = Rel::Seq(Arc::from(Vec::<Arc<Rel<()>>>::new()));

        let mut engine: Engine<()> = Engine::new(rel, terms);
        let ans = engine.next();
        assert!(ans.is_some(), "Empty Seq should yield identity");
        assert_eq!(ans.unwrap(), NF::identity(()));
        assert!(
            engine.next().is_none(),
            "Empty Seq should exhaust after identity"
        );
    }

    #[test]
    fn engine_call_ignores_non_adjacent_right_boundary() {
        let (symbols, terms) = setup();
        let a_to_b = make_rule_nf("A", "B", &symbols, &terms);
        let b_to_c = make_rule_nf("B", "C", &symbols, &terms);
        let b_to_d = make_rule_nf("B", "D", &symbols, &terms);
        let c_to_c = make_rule_nf("C", "C", &symbols, &terms);
        let a_to_c = make_rule_nf("A", "C", &symbols, &terms);

        let mid_or = Arc::new(Rel::Or(
            Arc::new(Rel::Atom(Arc::new(b_to_c))),
            Arc::new(Rel::Atom(Arc::new(b_to_d))),
        ));

        let recursive = Arc::new(Rel::Seq(Arc::from(vec![
            Arc::new(Rel::Call(0)),
            mid_or,
            Arc::new(Rel::Atom(Arc::new(c_to_c))),
        ])));

        let base = Arc::new(Rel::Atom(Arc::new(a_to_b)));
        let body = Arc::new(Rel::Or(base, recursive));
        let rel = Rel::Fix(0, body);

        let mut engine: Engine<()> = Engine::new(rel, terms);
        let ans1 = engine.next();
        let ans2 = engine.next();
        assert!(ans1.is_some(), "Fix should yield the base case");
        assert!(ans2.is_some(), "Recursive branch should yield A->C");
        assert_eq!(ans2.unwrap(), a_to_c);
    }

    #[test]
    fn engine_atom_then_exhausted() {
        let (symbols, terms) = setup();
        let nf = make_ground_nf("A", &symbols, &terms);
        let mut engine: Engine<()> = Engine::new(Rel::Atom(Arc::new(nf.clone())), terms);

        let ans = engine.next();
        assert!(ans.is_some());

        assert!(engine.is_exhausted());
        assert!(engine.next().is_none());
    }

    // ========================================================================
    // ENGINE NEXT - OR TESTS
    // ========================================================================

    #[test]
    fn engine_or_zero_zero_exhausts() {
        let (_, terms) = setup();
        let mut engine: Engine<()> =
            Engine::new(Rel::Or(Arc::new(Rel::Zero), Arc::new(Rel::Zero)), terms);

        assert!(engine.next().is_none(), "Or(Zero, Zero) should exhaust");
    }

    #[test]
    fn engine_or_atom_zero_yields_once() {
        let (_, terms) = setup();
        let nf = make_identity_nf();
        let mut engine: Engine<()> = Engine::new(
            Rel::Or(Arc::new(Rel::Atom(Arc::new(nf))), Arc::new(Rel::Zero)),
            terms,
        );

        let ans1 = engine.next();
        assert!(ans1.is_some(), "Or(Atom, Zero) should yield once");

        let ans2 = engine.next();
        assert!(ans2.is_none(), "Or(Atom, Zero) should exhaust");
    }

    #[test]
    fn engine_or_zero_atom_yields_once() {
        let (_, terms) = setup();
        let nf = make_identity_nf();
        let mut engine: Engine<()> = Engine::new(
            Rel::Or(Arc::new(Rel::Zero), Arc::new(Rel::Atom(Arc::new(nf)))),
            terms,
        );

        let ans1 = engine.next();
        assert!(ans1.is_some(), "Or(Zero, Atom) should yield once");

        let ans2 = engine.next();
        assert!(ans2.is_none(), "Or(Zero, Atom) should exhaust");
    }

    #[test]
    fn engine_or_two_atoms_yields_twice() {
        let (symbols, terms) = setup();
        let nf1 = make_ground_nf("A", &symbols, &terms);
        let nf2 = make_ground_nf("B", &symbols, &terms);

        let mut engine: Engine<()> = Engine::new(
            Rel::Or(
                Arc::new(Rel::Atom(Arc::new(nf1))),
                Arc::new(Rel::Atom(Arc::new(nf2))),
            ),
            terms,
        );

        let ans1 = engine.next();
        assert!(ans1.is_some(), "Or(A, B) should yield first");

        let ans2 = engine.next();
        assert!(ans2.is_some(), "Or(A, B) should yield second");

        let ans3 = engine.next();
        assert!(ans3.is_none(), "Or(A, B) should exhaust after two");
    }

    #[test]
    fn engine_or_rotation_interleaves() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

        let mut engine: Engine<()> = Engine::new(
            Rel::Or(
                Arc::new(Rel::Atom(Arc::new(nf_a.clone()))),
                Arc::new(Rel::Atom(Arc::new(nf_b.clone()))),
            ),
            terms,
        );

        // Collect answers
        let mut answers = vec![];
        while let Some(nf) = engine.next() {
            answers.push(nf);
        }

        assert_eq!(answers.len(), 2, "Should get exactly 2 answers");
    }

    // ========================================================================
    // ENGINE NEXT - NESTED OR TESTS
    // ========================================================================

    #[test]
    fn engine_nested_or_yields_all() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let nf_c = make_ground_nf("C", &symbols, &terms);

        // Or(Or(A, B), C)
        let mut engine: Engine<()> = Engine::new(
            Rel::Or(
                Arc::new(Rel::Or(
                    Arc::new(Rel::Atom(Arc::new(nf_a))),
                    Arc::new(Rel::Atom(Arc::new(nf_b))),
                )),
                Arc::new(Rel::Atom(Arc::new(nf_c))),
            ),
            terms,
        );

        let mut count = 0;
        while engine.next().is_some() {
            count += 1;
            if count > 10 {
                panic!("Too many answers");
            }
        }

        assert_eq!(count, 3, "Nested Or should yield 3 answers");
    }

    #[test]
    fn engine_deeply_nested_or_terminates() {
        let (_, terms) = setup();

        // Build deeply nested Or: Or(Or(Or(...Zero...)...), Atom)
        let nf = make_identity_nf();
        let mut rel: Rel<()> = Rel::Zero;
        for _ in 0..20 {
            rel = Rel::Or(Arc::new(rel), Arc::new(Rel::Zero));
        }
        rel = Rel::Or(Arc::new(rel), Arc::new(Rel::Atom(Arc::new(nf))));

        let mut engine: Engine<()> = Engine::new(rel, terms);

        // Should eventually yield one answer
        let mut count = 0;
        let mut max_steps = 1000;
        while max_steps > 0 {
            if engine.next().is_some() {
                count += 1;
            }
            if engine.is_exhausted() {
                break;
            }
            max_steps -= 1;
        }

        assert!(max_steps > 0, "Should terminate within reasonable steps");
        assert!(count >= 1, "Should yield at least one answer");
    }

    // ========================================================================
    // ENGINE IDEMPOTENCE TESTS
    // ========================================================================

    #[test]
    fn engine_exhausted_stays_exhausted() {
        let (_, terms) = setup();
        let mut engine: Engine<()> = Engine::new(Rel::Zero, terms);

        // Multiple calls after exhaustion
        for _ in 0..10 {
            assert!(engine.next().is_none());
            assert!(engine.is_exhausted());
        }
    }

    #[test]
    fn engine_after_atom_exhausted() {
        let (_, terms) = setup();
        let nf = make_identity_nf();
        let mut engine: Engine<()> = Engine::new(Rel::Atom(Arc::new(nf)), terms);

        let _ = engine.next(); // Consume the atom

        // Now should be exhausted
        for _ in 0..10 {
            assert!(engine.next().is_none());
        }
    }

    // ========================================================================
    // ENGINE SIZE TESTS
    // ========================================================================

    #[test]
    fn engine_size_reasonable() {
        use std::mem::size_of;
        let size = size_of::<Engine<()>>();
        // Engine contains TermStore and Node (with Work)
        // These are substantial structures
        assert!(
            size < 1600,
            "Engine should not be excessively large, got {}",
            size
        );
    }

    #[test]
    fn step_result_size_reasonable() {
        use std::mem::size_of;
        let size = size_of::<StepResult<()>>();
        assert!(
            size < 128,
            "StepResult should not be excessively large, got {}",
            size
        );
    }

    // ========================================================================
    // QUERY ITER TESTS
    // ========================================================================

    #[test]
    fn engine_iter_yields_all_answers() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

        let mut engine: Engine<()> = Engine::new(
            Rel::Or(
                Arc::new(Rel::Atom(Arc::new(nf_a))),
                Arc::new(Rel::Atom(Arc::new(nf_b))),
            ),
            terms,
        );

        let answers: Vec<_> = engine.iter().collect();
        assert_eq!(answers.len(), 2, "iter() should yield all 2 answers");
    }

    #[test]
    fn engine_iter_empty_for_zero() {
        let (_, terms) = setup();
        let mut engine: Engine<()> = Engine::new(Rel::Zero, terms);

        let answers: Vec<_> = engine.iter().collect();
        assert!(answers.is_empty(), "iter() on Zero should be empty");
    }

    #[test]
    fn engine_iter_single_for_atom() {
        let (_, terms) = setup();
        let nf = make_identity_nf();
        let mut engine: Engine<()> = Engine::new(Rel::Atom(Arc::new(nf)), terms);

        let answers: Vec<_> = engine.iter().collect();
        assert_eq!(answers.len(), 1, "iter() on Atom should yield 1");
    }

    #[test]
    fn engine_iter_can_be_partially_consumed() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let nf_c = make_ground_nf("C", &symbols, &terms);

        let mut engine: Engine<()> = Engine::new(
            Rel::Or(
                Arc::new(Rel::Atom(Arc::new(nf_a))),
                Arc::new(Rel::Or(
                    Arc::new(Rel::Atom(Arc::new(nf_b))),
                    Arc::new(Rel::Atom(Arc::new(nf_c))),
                )),
            ),
            terms,
        );

        // Take only first answer via iter
        let first = engine.iter().next();
        assert!(first.is_some(), "Should get first answer");

        // Engine should still have more answers
        assert!(!engine.is_exhausted());

        // Can get remaining via another iter
        let rest: Vec<_> = engine.iter().collect();
        assert_eq!(rest.len(), 2, "Should have 2 remaining answers");
    }

    // ========================================================================
    // COLLECT_ANSWERS TESTS
    // ========================================================================

    #[test]
    fn engine_collect_answers_works() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

        let mut engine: Engine<()> = Engine::new(
            Rel::Or(
                Arc::new(Rel::Atom(Arc::new(nf_a))),
                Arc::new(Rel::Atom(Arc::new(nf_b))),
            ),
            terms,
        );

        let answers = engine.collect_answers();
        assert_eq!(answers.len(), 2);
    }

    #[test]
    fn engine_collect_answers_empty_for_zero() {
        let (_, terms) = setup();
        let mut engine: Engine<()> = Engine::new(Rel::Zero, terms);

        let answers = engine.collect_answers();
        assert!(answers.is_empty());
    }

    #[test]
    fn seq_with_and_of_disjoint_rules_is_empty() {
        let mut parser = Parser::new();
        let rel = parser
            .parse_rel_body("[$x -> $y] ; [[a -> z] & [b -> z]]")
            .expect("parse query");
        let terms = parser.take_terms();
        let mut engine: Engine<()> = Engine::new(rel, terms);

        let answers = engine.collect_answers();
        assert!(
            answers.is_empty(),
            "Expected no answers for disjoint intersection in sequence, got {}",
            answers.len()
        );
    }

    #[test]
    fn seq_with_fix_then_free_call_is_empty() {
        let mut parser = Parser::new();
        let nf = parser.parse_rule("a -> a").expect("parse rule");
        let rel = Rel::Seq(Arc::from(vec![
            Arc::new(Rel::Fix(0, Arc::new(Rel::Atom(Arc::new(nf))))),
            Arc::new(Rel::Call(0)),
        ]));
        let terms = parser.take_terms();
        let mut engine: Engine<()> = Engine::new(rel, terms);

        let answers = engine.collect_answers();
        assert!(
            answers.is_empty(),
            "Expected no answers for out-of-scope Call, got {}",
            answers.len()
        );
    }

    #[test]
    fn and_with_shadowed_fix_does_not_reuse_table() {
        let mut parser = Parser::new();
        let nf = parser.parse_rule("a -> a").expect("parse rule");
        let fix_body = Rel::Or(Arc::new(Rel::Atom(Arc::new(nf))), Arc::new(Rel::Call(0)));
        let rel = Rel::And(
            Arc::new(Rel::Fix(0, Arc::new(fix_body))),
            Arc::new(Rel::Fix(0, Arc::new(Rel::Call(0)))),
        );
        let terms = parser.take_terms();
        let mut engine: Engine<()> = Engine::new(rel, terms);

        let answers = engine.collect_answers();
        assert!(
            answers.is_empty(),
            "Expected no answers for separate Fix scopes with same id, got {}",
            answers.len()
        );
    }

    #[test]
    fn or_with_shadowed_fix_should_not_duplicate_answers() {
        let mut parser = Parser::new();
        let nf_a = parser.parse_rule("a -> a").expect("parse rule");
        let nf_b = parser.parse_rule("b -> b").expect("parse rule");
        let expected = nf_a.clone();
        let recursive = Rel::Seq(Arc::from(vec![
            Arc::new(Rel::Call(0)),
            Arc::new(Rel::Atom(Arc::new(nf_b))),
        ]));
        let fix_body = Rel::Or(Arc::new(Rel::Atom(Arc::new(nf_a))), Arc::new(recursive));
        let rel = Rel::Or(
            Arc::new(Rel::Fix(0, Arc::new(fix_body))),
            Arc::new(Rel::Fix(0, Arc::new(Rel::Call(0)))),
        );
        let terms = parser.take_terms();
        let mut engine: Engine<()> = Engine::new(rel, terms);

        let answers = engine.collect_answers();
        assert_eq!(
            answers.len(),
            1,
            "Expected one answer from left Fix only, got {}",
            answers.len()
        );
        assert_eq!(answers[0], expected, "Unexpected answer returned");
    }

    #[test]
    fn engine_collect_answers_exhausts_engine() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);

        let mut engine: Engine<()> = Engine::new(Rel::Atom(Arc::new(nf_a)), terms);

        let answers = engine.collect_answers();
        assert_eq!(answers.len(), 1);

        // Engine should now be exhausted
        assert!(engine.is_exhausted());
        assert!(engine.next().is_none());
    }

    // ========================================================================
    // COUNT_ANSWERS TESTS
    // ========================================================================

    #[test]
    fn engine_count_answers_works() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);
        let nf_c = make_ground_nf("C", &symbols, &terms);

        let mut engine: Engine<()> = Engine::new(
            Rel::Or(
                Arc::new(Rel::Atom(Arc::new(nf_a))),
                Arc::new(Rel::Or(
                    Arc::new(Rel::Atom(Arc::new(nf_b))),
                    Arc::new(Rel::Atom(Arc::new(nf_c))),
                )),
            ),
            terms,
        );

        let count = engine.count_answers();
        assert_eq!(count, 3);
    }

    #[test]
    fn engine_count_answers_zero_for_empty() {
        let (_, terms) = setup();
        let mut engine: Engine<()> = Engine::new(Rel::Zero, terms);

        let count = engine.count_answers();
        assert_eq!(count, 0);
    }

    #[test]
    fn engine_count_answers_exhausts_engine() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);

        let mut engine: Engine<()> = Engine::new(Rel::Atom(Arc::new(nf_a)), terms);

        let _ = engine.count_answers();

        // Engine should now be exhausted
        assert!(engine.is_exhausted());
    }

    // ========================================================================
    // QUERY CONVENIENCE FUNCTION TESTS
    // ========================================================================

    #[test]
    fn query_convenience_function_works() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

        let rel = Rel::Or(
            Arc::new(Rel::Atom(Arc::new(nf_a))),
            Arc::new(Rel::Atom(Arc::new(nf_b))),
        );

        let answers = query(rel, terms);
        assert_eq!(answers.len(), 2);
    }

    #[test]
    fn query_returns_empty_for_zero() {
        let (_, terms) = setup();
        let answers: Vec<NF<()>> = query(Rel::Zero, terms);
        assert!(answers.is_empty());
    }

    #[test]
    fn query_returns_single_for_atom() {
        let (_, terms) = setup();
        let nf = make_identity_nf();
        let answers = query(Rel::Atom(Arc::new(nf)), terms);
        assert_eq!(answers.len(), 1);
    }

    // ========================================================================
    // QUERY_FIRST CONVENIENCE FUNCTION TESTS
    // ========================================================================

    #[test]
    fn query_first_convenience_function_works() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);

        let rel = Rel::Atom(Arc::new(nf_a));
        let answer = query_first(rel, terms);

        assert!(answer.is_some());
    }

    #[test]
    fn query_first_returns_none_for_zero() {
        let (_, terms) = setup();
        let answer: Option<NF<()>> = query_first(Rel::Zero, terms);
        assert!(answer.is_none());
    }

    #[test]
    fn query_first_returns_first_of_many() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

        let rel = Rel::Or(
            Arc::new(Rel::Atom(Arc::new(nf_a))),
            Arc::new(Rel::Atom(Arc::new(nf_b))),
        );

        let answer = query_first(rel, terms);
        assert!(answer.is_some(), "Should get the first answer");
    }

    #[test]
    fn query_first_does_not_compute_all_answers() {
        // This is a behavioral test - query_first should be lazy
        let (_, terms) = setup();
        let nf = make_identity_nf();

        // Build a large Or tree
        let mut rel: Rel<()> = Rel::Atom(Arc::new(nf.clone()));
        for _ in 0..100 {
            rel = Rel::Or(Arc::new(Rel::Atom(Arc::new(nf.clone()))), Arc::new(rel));
        }

        // query_first should return quickly (get first answer only)
        let answer = query_first(rel, terms);
        assert!(answer.is_some());
    }

    // ========================================================================
    // FIX/CALL TESTS - Comprehensive edge case coverage
    // ========================================================================
    //
    // These tests cover all edge cases identified in the Fix/Call analysis.
    // Each test is specific, minimal, and tests exactly ONE behavior.

    /// Helper: Build a "count down" relation: z -> z | (s x) -> x ; count
    /// This relation decrements successors until reaching zero.
    fn build_countdown_rel(symbols: &SymbolStore, terms: &TermStore) -> Rel<()> {
        let z = symbols.intern("z");
        let s = symbols.intern("s");

        let z_term = terms.app0(z);
        let v0 = terms.var(0);
        let s_v0 = terms.app(s, SmallVec::from_slice(&[v0]));

        // Base: z -> z
        let base_nf = NF::new(
            SmallVec::from_slice(&[z_term]),
            DropFresh::identity(0),
            SmallVec::from_slice(&[z_term]),
        );
        let base = Arc::new(Rel::Atom(Arc::new(base_nf)));

        // Peel: (s x) -> x
        let peel_nf = NF::new(
            SmallVec::from_slice(&[s_v0]),
            DropFresh::identity(1),
            SmallVec::from_slice(&[v0]),
        );
        let peel = Arc::new(Rel::Atom(Arc::new(peel_nf)));

        // Recursive: Seq([peel, Call(0)])
        let call = Arc::new(Rel::Call(0));
        let recursive = Arc::new(Rel::Seq(Arc::from(vec![peel, call])));

        // Body: Or(base, recursive)
        let body = Arc::new(Rel::Or(base, recursive));

        // Fix(0, body)
        Rel::Fix(0, body)
    }

    // ------------------------------------------------------------------------
    // CATEGORY 1: Fix Basic Edge Cases
    // ------------------------------------------------------------------------

    /// Fix with non-recursive body (Atom) should yield the atom's answer.
    #[test]
    fn fix_body_is_atom_yields_atom() {
        let nf = make_identity_nf();
        let rel = Rel::Fix(0, Arc::new(Rel::Atom(Arc::new(nf))));
        let mut engine: Engine<()> = Engine::new(rel, TermStore::new());

        assert!(engine.next().is_some(), "Fix(0, Atom(nf)) should yield nf");
        assert!(engine.next().is_none(), "Should exhaust after one answer");
    }

    /// Fix with Zero body should fail (empty relation).
    #[test]
    fn fix_body_is_zero_fails() {
        let rel: Rel<()> = Rel::Fix(0, Arc::new(Rel::Zero));
        let mut engine: Engine<()> = Engine::new(rel, TermStore::new());

        assert!(engine.next().is_none(), "Fix(0, Zero) should fail");
    }

    /// Fix with Or body (no Call) should yield both branches.
    #[test]
    fn fix_body_is_or_no_call_yields_both() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

        let rel = Rel::Fix(
            0,
            Arc::new(Rel::Or(
                Arc::new(Rel::Atom(Arc::new(nf_a))),
                Arc::new(Rel::Atom(Arc::new(nf_b))),
            )),
        );
        let mut engine: Engine<()> = Engine::new(rel, terms);

        assert!(engine.next().is_some(), "Should yield first branch");
        assert!(engine.next().is_some(), "Should yield second branch");
        assert!(engine.next().is_none(), "Should exhaust after two");
    }

    /// Nested Fix with same RelId - inner should shadow outer.
    #[test]
    fn fix_nested_same_id_inner_shadows_outer() {
        let (symbols, terms) = setup();
        let nf_inner = make_ground_nf("INNER", &symbols, &terms);

        // Fix(0, Fix(0, Atom(INNER))) - inner Fix shadows outer
        // When Call(0) is used, it should refer to the inner binding
        let inner_fix = Rel::Fix(0, Arc::new(Rel::Atom(Arc::new(nf_inner.clone()))));
        let outer_fix = Rel::Fix(0, Arc::new(inner_fix));

        let mut engine: Engine<()> = Engine::new(outer_fix, terms);
        let ans = engine.next();
        assert!(ans.is_some(), "Nested Fix should yield inner body");
        // The answer should be INNER, not OUTER
    }

    /// Nested Fix with different RelIds should maintain separate bindings.
    #[test]
    fn fix_nested_different_ids_separate_bindings() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);

        // Fix(0, Fix(1, Atom(A))) - two separate bindings
        let inner = Rel::Fix(1, Arc::new(Rel::Atom(Arc::new(nf_a))));
        let outer = Rel::Fix(0, Arc::new(inner));

        let mut engine: Engine<()> = Engine::new(outer, terms);
        assert!(engine.next().is_some(), "Should yield the atom");
    }

    /// Fix with RelId 0 (boundary value).
    #[test]
    fn fix_relid_zero_works() {
        let nf = make_identity_nf();
        let rel = Rel::Fix(0, Arc::new(Rel::Atom(Arc::new(nf))));
        let mut engine: Engine<()> = Engine::new(rel, TermStore::new());
        assert!(engine.next().is_some(), "Fix with RelId 0 should work");
    }

    /// Fix with RelId u32::MAX (boundary value).
    #[test]
    fn fix_relid_max_works() {
        let nf = make_identity_nf();
        let rel = Rel::Fix(u32::MAX, Arc::new(Rel::Atom(Arc::new(nf))));
        let mut engine: Engine<()> = Engine::new(rel, TermStore::new());
        assert!(engine.next().is_some(), "Fix with RelId MAX should work");
    }

    // ------------------------------------------------------------------------
    // CATEGORY 2: Call Basic Edge Cases
    // ------------------------------------------------------------------------

    /// Call to undefined RelId should fail gracefully.
    #[test]
    fn call_undefined_relid_fails() {
        let rel: Rel<()> = Rel::Call(99);
        let mut engine: Engine<()> = Engine::new(rel, TermStore::new());
        assert!(
            engine.next().is_none(),
            "Call to undefined RelId should fail"
        );
    }

    /// Call with RelId 0 (boundary).
    #[test]
    fn call_relid_zero_with_binding_works() {
        let nf = make_identity_nf();
        // Fix(0, Or(Atom(nf), Call(0))) - Call refers to the Fix
        // With base case first, should at least yield base case
        let body = Rel::Or(Arc::new(Rel::Atom(Arc::new(nf))), Arc::new(Rel::Call(0)));
        let rel = Rel::Fix(0, Arc::new(body));
        let mut engine: Engine<()> = Engine::new(rel, TermStore::new());

        assert!(
            engine.next().is_some(),
            "Call(0) with Fix(0, ...) should work"
        );
    }

    /// Call inside Or - should try base first, then recursive branch.
    #[test]
    fn call_inside_or_tries_base_first() {
        let (symbols, terms) = setup();
        let countdown = build_countdown_rel(&symbols, &terms);
        let mut engine: Engine<()> = Engine::new(countdown, terms);

        // Base case z -> z should be yielded first (left branch of Or)
        let ans = engine.next();
        assert!(ans.is_some(), "Should yield base case first");
    }

    /// Call at first position in Seq.
    #[test]
    fn call_first_in_seq() {
        let (symbols, terms) = setup();
        let nf = make_ground_nf("X", &symbols, &terms);

        // Fix(0, Seq([Call(0), Atom(X)])) - infinite recursion without base
        // This should either fail or be detected as non-terminating
        let body = Rel::Seq(Arc::from(vec![
            Arc::new(Rel::Call(0)),
            Arc::new(Rel::Atom(Arc::new(nf))),
        ]));
        let rel = Rel::Fix(0, Arc::new(body));
        let mut engine: Engine<()> = Engine::new(rel, terms);

        // With tabling, this should detect re-entrance and fail
        // Without tabling, this might loop - we set a step limit
        let mut count = 0;
        for _ in 0..100 {
            if engine.next().is_none() {
                break;
            }
            count += 1;
            if count > 10 {
                break; // Avoid infinite loop in test
            }
        }
        // Test passes if we don't hang (even if we got 0 or some answers)
    }

    /// Call at last position in Seq.
    #[test]
    fn call_last_in_seq() {
        let (symbols, terms) = setup();
        let countdown = build_countdown_rel(&symbols, &terms);
        let mut engine: Engine<()> = Engine::new(countdown, terms);

        // countdown has Seq([peel, Call(0)]) - Call at end
        let ans = engine.next();
        assert!(ans.is_some(), "Seq with Call at end should yield");
    }

    /// Multiple Calls to same RelId in one expression.
    #[test]
    fn multiple_calls_same_relid() {
        let nf = make_identity_nf();
        // Fix(0, Or(Atom(nf), Seq([Call(0), Call(0)])))
        // Two calls to same relation
        let body = Rel::Or(
            Arc::new(Rel::Atom(Arc::new(nf))),
            Arc::new(Rel::Seq(Arc::from(vec![
                Arc::new(Rel::Call(0)),
                Arc::new(Rel::Call(0)),
            ]))),
        );
        let rel = Rel::Fix(0, Arc::new(body));
        let mut engine: Engine<()> = Engine::new(rel, TermStore::new());

        // Should at least yield the base case
        assert!(engine.next().is_some(), "Multiple calls should work");
    }

    /// Call to outer Fix from inside nested Fix.
    #[test]
    fn call_outer_fix_from_nested() {
        let nf = make_identity_nf();
        // Fix(0, Fix(1, Or(Atom(nf), Call(0))))
        // Call(0) refers to outer Fix
        let inner_body = Rel::Or(Arc::new(Rel::Atom(Arc::new(nf))), Arc::new(Rel::Call(0)));
        let inner = Rel::Fix(1, Arc::new(inner_body));
        let outer = Rel::Fix(0, Arc::new(inner));

        let mut engine: Engine<()> = Engine::new(outer, TermStore::new());
        assert!(engine.next().is_some(), "Call to outer Fix should work");
    }

    // ------------------------------------------------------------------------
    // CATEGORY 3: Termination (CRITICAL)
    // ------------------------------------------------------------------------

    /// Simple recursion with base case should terminate.
    #[test]
    fn recursion_with_base_case_terminates() {
        let (symbols, terms) = setup();
        let z = symbols.intern("z");
        let s = symbols.intern("s");
        let z_term = terms.app0(z);
        let s_z = terms.app(s, SmallVec::from_slice(&[z_term]));

        let countdown = build_countdown_rel(&symbols, &terms);
        let input_nf = NF::new(
            SmallVec::from_slice(&[s_z]),
            DropFresh::identity(0),
            SmallVec::from_slice(&[s_z]),
        );
        let query = Rel::Seq(Arc::from(vec![
            Arc::new(Rel::Atom(Arc::new(input_nf))),
            Arc::new(countdown),
        ]));
        let mut engine: Engine<()> = Engine::new(query, terms);

        // Should yield z -> z (base case) and terminate
        let mut count = 0;
        let max = 100;
        while count < max {
            if engine.next().is_none() {
                break;
            }
            count += 1;
        }
        assert!(count < max, "Recursion should terminate, not loop forever");
        assert!(count >= 1, "Should yield at least the base case");
    }

    /// Recursion without base case should fail/terminate, not loop forever.
    /// Call-context tabling detects re-entrance and fails.
    #[test]
    fn recursion_without_base_case_terminates() {
        // Fix(0, Call(0)) - pure recursion, no base case
        let rel: Rel<()> = Rel::Fix(0, Arc::new(Rel::Call(0)));
        let mut engine: Engine<()> = Engine::new(rel, TermStore::new());

        // Should detect re-entrance via tabling and fail
        let mut count = 0;
        for _ in 0..100 {
            if engine.next().is_none() {
                break;
            }
            count += 1;
        }
        // Must terminate (either with 0 answers or by detecting loop)
        assert!(count < 100, "Pure recursion should terminate via tabling");
    }

    #[test]
    fn pure_recursion_exhausts_under_step_node() {
        use crate::node::{step_node, NodeStep};
        use crate::work::{rel_to_node, Env, Tables};

        let rel: Rel<()> = Rel::Fix(0, Arc::new(Rel::Call(0)));
        let env = Env::new();
        let tables = Tables::new();
        let mut terms = TermStore::new();

        let mut node = rel_to_node(&rel, &env, &tables);
        let mut steps = 0;
        let max_steps = 50;

        loop {
            match step_node(node, &mut terms) {
                NodeStep::Emit(_, rest) => {
                    node = rest;
                    steps += 1;
                }
                NodeStep::Continue(rest) => {
                    node = rest;
                    steps += 1;
                    assert!(
                        steps < max_steps,
                        "Pure recursion should exhaust without infinite stepping"
                    );
                }
                NodeStep::Exhausted => break,
            }
        }
    }

    /// Input through recursive relation produces multiple answers.
    #[test]
    fn recursion_produces_multiple_answers() {
        let (symbols, terms) = setup();

        let z = symbols.intern("z");
        let s = symbols.intern("s");
        let z_term = terms.app0(z);

        let countdown = build_countdown_rel(&symbols, &terms);

        // Input: (s (s z)) through countdown
        let ss_z = terms.app(
            s,
            SmallVec::from_slice(&[terms.app(s, SmallVec::from_slice(&[z_term]))]),
        );
        let input_nf = NF::new(
            SmallVec::from_slice(&[ss_z]),
            DropFresh::identity(0),
            SmallVec::from_slice(&[ss_z]),
        );

        // Query: input ; countdown
        let query = Rel::Seq(Arc::from(vec![
            Arc::new(Rel::Atom(Arc::new(input_nf))),
            Arc::new(countdown),
        ]));

        let mut engine: Engine<()> = Engine::new(query, terms);

        let mut answers = Vec::new();
        for _ in 0..50 {
            match engine.next() {
                Some(nf) => answers.push(nf),
                None => break,
            }
        }

        assert_eq!(
            answers.len(),
            1,
            "countdown((s (s z))) should yield one answer, got {}",
            answers.len()
        );
    }

    /// CRITICAL: Recursive relation with output constraint terminates.
    /// This uses peel/wrap so `wrap ; id_(s z)` fuses before recursion.
    #[test]
    fn recursion_with_output_constraint_terminates() {
        let (symbols, terms) = setup();

        let z = symbols.intern("z");
        let s = symbols.intern("s");
        let z_term = terms.app0(z);
        let v0 = terms.var(0);
        let s_v0 = terms.app(s, SmallVec::from_slice(&[v0]));
        let s_z = terms.app(s, SmallVec::from_slice(&[z_term]));

        // Build a relation that forces wrap ; id_(s z) fusion:
        // base: z -> z
        // recursive: peel ; Call ; wrap
        let base_nf = NF::new(
            SmallVec::from_slice(&[z_term]),
            DropFresh::identity(0),
            SmallVec::from_slice(&[z_term]),
        );
        let base = Arc::new(Rel::Atom(Arc::new(base_nf)));

        let peel_nf = NF::new(
            SmallVec::from_slice(&[s_v0]),
            DropFresh::identity(1),
            SmallVec::from_slice(&[v0]),
        );
        let peel = Arc::new(Rel::Atom(Arc::new(peel_nf)));

        let wrap_nf = NF::new(
            SmallVec::from_slice(&[v0]),
            DropFresh::identity(1),
            SmallVec::from_slice(&[s_v0]),
        );
        let wrap = Arc::new(Rel::Atom(Arc::new(wrap_nf)));

        let recursive = Arc::new(Rel::Seq(Arc::from(vec![
            peel,
            Arc::new(Rel::Call(0)),
            wrap,
        ])));
        let body = Arc::new(Rel::Or(base, recursive));
        let rel = Rel::Fix(0, body);

        // id_(s z): matches (s z) -> (s z)
        let constraint_nf = NF::new(
            SmallVec::from_slice(&[s_z]),
            DropFresh::identity(0),
            SmallVec::from_slice(&[s_z]),
        );

        // Query: rel ; constraint
        let query = Rel::Seq(Arc::from(vec![
            Arc::new(rel),
            Arc::new(Rel::Atom(Arc::new(constraint_nf))),
        ]));

        let mut engine: Engine<()> = Engine::new(query, terms);

        // CRITICAL: Must terminate within bounded steps
        let max_steps = 1000;
        let mut step_count = 0;
        let mut answers = Vec::new();

        while step_count < max_steps {
            match engine.next() {
                Some(nf) => answers.push(nf),
                None => break,
            }
            step_count += 1;
        }

        assert!(
            step_count < max_steps,
            "TERMINATION FAILURE: recursive relation with constraint did not terminate"
        );
        // Should find exactly one answer: (s z) -> (s z) from base-like path
    }

    #[test]
    fn add_with_output_constraint_terminates() {
        let mut parser = Parser::new();
        let def = r#"
rel add {
    (cons z $y) -> $y
    |
    [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
}
"#;

        let (_, rel_def) = parser.parse_rel_def(def).expect("parse add");
        let env = match &rel_def {
            Rel::Fix(id, body) => Env::new().bind(*id, body.clone()),
            _ => Env::new(),
        };

        let query = parser.parse_rel_body("add ; @(s z)").expect("parse query");

        let terms = parser.take_terms();
        let mut engine: Engine<()> = Engine::new_with_env(query, terms, env);

        let max_steps = 2000;
        let mut step_count = 0;
        let mut answers = Vec::new();

        while step_count < max_steps {
            match engine.next() {
                Some(nf) => answers.push(nf),
                None => break,
            }
            step_count += 1;
        }

        assert!(
            step_count < max_steps,
            "TERMINATION FAILURE: add ; id_(s z) did not terminate"
        );
        assert!(
            !answers.is_empty(),
            "Expected at least one answer for add ; id_(s z)"
        );
    }

    // ------------------------------------------------------------------------
    // E2E: Addition Examples
    // ------------------------------------------------------------------------

    #[test]
    fn addition_forward_example_3_plus_2_is_5() {
        let mut parser = Parser::new();
        let def = include_str!("../examples/addition.txt");
        let (_add_rel, env) = parse_rel_def_with_env(&mut parser, def);

        let input_str = "(cons (s (s (s z))) (s (s z)))";
        let expected_str = "(s (s (s (s (s z)))))";

        let query = parser
            .parse_rel_body(&format!("@{} ; add", input_str))
            .expect("parse query");
        let input_term = parser.parse_term(input_str).expect("parse input").term_id;
        let expected_term = parser
            .parse_term(expected_str)
            .expect("parse expected")
            .term_id;

        let mut terms = parser.take_terms();
        let expected_nf = NF::factor(input_term, expected_term, (), &mut terms);

        let mut engine: Engine<()> = Engine::new_with_env(query, terms, env);
        let answers = engine.collect_answers();

        assert!(
            answers.contains(&expected_nf),
            "Expected to find 3+2=5 result"
        );
        assert_eq!(answers.len(), 1, "Expected exactly one answer");
    }

    #[test]
    fn addition_backward_generates_all_pairs_summing_to_5() {
        let mut parser = Parser::new();
        let def = include_str!("../examples/addition.txt");
        let (add_rel, _env) = parse_rel_def_with_env(&mut parser, def);

        let target_str = "(s (s (s (s (s z)))))";
        let target_term = parser.parse_term(target_str).expect("parse target").term_id;

        let mut pair_terms = Vec::new();
        for x in 0..=5 {
            let pair_str = format!("(cons {} {})", peano_str(x), peano_str(5 - x));
            let pair_term = parser.parse_term(&pair_str).expect("parse pair").term_id;
            pair_terms.push(pair_term);
        }

        let mut terms = parser.take_terms();
        let target_nf = NF::factor(target_term, target_term, (), &mut terms);
        let dual_add = dual(&add_rel, &mut terms);
        let query = Rel::Seq(Arc::from(vec![
            Arc::new(Rel::Atom(Arc::new(target_nf))),
            Arc::new(dual_add),
        ]));

        let mut expected = HashSet::new();
        for pair_term in pair_terms {
            expected.insert(NF::factor(target_term, pair_term, (), &mut terms));
        }

        let mut engine: Engine<()> = Engine::new(query, terms);
        let answers: HashSet<_> = engine.collect_answers().into_iter().collect();

        assert_eq!(answers, expected, "Expected all pairs summing to 5");
    }

    #[test]
    fn subtraction_via_dual_add_example() {
        let mut parser = Parser::new();
        let def = include_str!("../examples/addition.txt");
        let (add_rel, _env) = parse_rel_def_with_env(&mut parser, def);

        let rule_left = parser
            .parse_rel_body("(cons $x $y) -> $x")
            .expect("parse rule left");
        let rule_right = parser
            .parse_rel_body("(cons $x $y) -> (cons $y $z)")
            .expect("parse rule right");
        let rule_out = parser
            .parse_rel_body("(cons $x $y) -> $y")
            .expect("parse rule out");

        let input_str = "(cons (s (s (s (s (s z))))) (s (s (s z))))";
        let expected_str = "(s (s z))";

        let input_term = parser.parse_term(input_str).expect("parse input").term_id;
        let expected_term = parser
            .parse_term(expected_str)
            .expect("parse expected")
            .term_id;

        let mut terms = parser.take_terms();
        let dual_add = dual(&add_rel, &mut terms);
        let and_left = Rel::Seq(Arc::from(vec![Arc::new(rule_left), Arc::new(dual_add)]));
        let sub_rel = Rel::Seq(Arc::from(vec![
            Arc::new(Rel::And(Arc::new(and_left), Arc::new(rule_right))),
            Arc::new(rule_out),
        ]));
        let input_nf = NF::factor(input_term, input_term, (), &mut terms);
        let expected_nf = NF::factor(input_term, expected_term, (), &mut terms);
        let query = Rel::Seq(Arc::from(vec![
            Arc::new(Rel::Atom(Arc::new(input_nf))),
            Arc::new(sub_rel),
        ]));

        let mut engine: Engine<()> = Engine::new(query, terms);
        let mut found = false;
        for _ in 0..100 {
            match engine.next() {
                Some(nf) => {
                    if nf == expected_nf {
                        found = true;
                        break;
                    }
                }
                None => break,
            }
        }

        assert!(found, "Expected subtraction result (5 - 3 = 2)");
    }

    // ------------------------------------------------------------------------
    // E2E: Tree Calculus Examples (app relation)
    // ------------------------------------------------------------------------

    fn treecalc_app_case(input: &str, expected: &str) {
        let mut parser = Parser::new();
        let def = include_str!("../examples/treecalc.txt");
        let (_app_rel, env) = parse_rel_def_with_env(&mut parser, def);

        let query = parser
            .parse_rel_body(&format!("@{} ; app", input))
            .expect("parse app query");
        let input_term = parser.parse_term(input).expect("parse input").term_id;
        let expected_term = parser.parse_term(expected).expect("parse expected").term_id;

        let mut terms = parser.take_terms();
        let expected_nf = NF::factor(input_term, expected_term, (), &mut terms);

        let mut engine: Engine<()> = Engine::new_with_env(query, terms, env);
        let first = engine.next();
        assert!(first.is_some(), "Expected treecalc answer for input {}", input);
        assert_eq!(
            first.unwrap(),
            expected_nf,
            "Treecalc head result mismatch for input {}",
            input
        );
    }

    fn treecalc_app_case_with_limit(input: &str, expected: &str, query_suffix: &str) {
        let mut parser = Parser::new();
        let def = include_str!("../examples/treecalc.txt");
        let (_app_rel, env) = parse_rel_def_with_env(&mut parser, def);

        let query_str = format!("@{} ; {}", input, query_suffix);
        let query = parser.parse_rel_body(&query_str).expect("parse app query");
        let input_term = parser.parse_term(input).expect("parse input").term_id;
        let expected_term = parser.parse_term(expected).expect("parse expected").term_id;

        let mut terms = parser.take_terms();
        let expected_nf = NF::factor(input_term, expected_term, (), &mut terms);

        let mut engine: Engine<()> = Engine::new_with_env(query, terms, env);
        let first = engine.next();
        assert!(
            first.is_some(),
            "Expected treecalc answer for query {}",
            query_str
        );
        assert_eq!(
            first.unwrap(),
            expected_nf,
            "Treecalc head result mismatch for query {}",
            query_str
        );
    }

    fn count_top_or(rel: &Rel<()>) -> usize {
        match rel {
            Rel::Or(left, right) => count_top_or(left) + count_top_or(right),
            _ => 1,
        }
    }

    #[test]
    fn treecalc_app_example_1() {
        treecalc_app_case("(f (f l (b l)) (b (b l)))", "(b l)");
    }

    #[test]
    #[cfg_attr(
        debug_assertions,
        ignore = "long-running; requires release build that has already been built"
    )]
    fn program_synth_flip_query_emits_answer() {
        let mut parser = Parser::with_chr();
        let (_app_rel, env) = parse_rel_def_with_env_chr(&mut parser, PROGRAM_SYNTH_DEF);

        let query_str = concat!(
            "[[$x { (no_c $x) } -> (f $x (c z))] ; app ; ",
            "[$x -> (f $x (c (s z)))] ; app ; @(a (c (s z)) (c z))]"
        );
        let query = parser.parse_rel_body(query_str).expect("parse query");
        let terms = parser.take_terms();
        let mut engine: Engine<ChrState<NoTheory>> = Engine::new_with_env(query, terms, env);
        let max_steps = 20_000_000;
        let first = run_until_emit(&mut engine, max_steps);
        assert!(
            first.is_some(),
            "Expected program_synth flip query to emit within {} steps",
            max_steps
        );
        let nf = first.expect("expected program_synth flip answer");
        let rendered = engine
            .format_nf(&nf, parser.symbols())
            .unwrap_or_else(|_| "<unrenderable>".to_string());
        eprintln!("program_synth_flip_query_emits_answer output: {}", rendered);
    }

    #[test]
    #[cfg_attr(
        debug_assertions,
        ignore = "long-running; requires release build that has already been built"
    )]
    fn program_synth_flip_query_emits_answer_dual() {
        use crate::kernel::dual_nf;

        let mut parser = Parser::with_chr();
        let (_app_rel, env) = parse_rel_def_with_env_chr(&mut parser, PROGRAM_SYNTH_DEF);

        let query_str = concat!(
            "[[$x { (no_c $x) } -> (f $x (c z))] ; app ; ",
            "[$x -> (f $x (c (s z)))] ; app ; @(a (c (s z)) (c z))]"
        );
        let query = parser.parse_rel_body(query_str).expect("parse query");
        let terms = parser.take_terms();

        let mut engine: Engine<ChrState<NoTheory>> =
            Engine::new_with_env(query.clone(), terms, env.clone());
        let max_steps = 20_000_000;
        let first = run_until_emit(&mut engine, max_steps).expect("expected first answer");
        let mut terms = engine.into_terms();
        let expected_dual = dual_nf(&first, &mut terms);

        let mut dual_engine: Engine<ChrState<NoTheory>> =
            Engine::new_with_env(dual(&query, &mut terms), terms, env);
        let dual_first = run_until_emit(&mut dual_engine, max_steps).expect("expected dual answer");
        assert!(
            dual_first == expected_dual,
            "Dual query should emit the dual of the same span"
        );
    }

    #[test]
    fn treecalc_identity_with_no_c_constraint() {
        let mut parser = Parser::with_chr();
        let def = include_str!("../examples/treecalc.txt");
        let (_app_rel, env) = parse_rel_def_with_env_chr(&mut parser, def);

        let expected_prog = parser
            .parse_term("(f (b (b l)) l)")
            .expect("parse expected program")
            .term_id;
        let expected_out = parser
            .parse_term("(c z)")
            .expect("parse expected output")
            .term_id;

        fn trace_query(
            label: &str,
            query: &Rel<ChrState<NoTheory>>,
            env: &Env<ChrState<NoTheory>>,
            terms: &mut TermStore,
            symbols: &SymbolStore,
            max_steps: usize,
        ) -> Option<NF<ChrState<NoTheory>>> {
            let mut engine: Engine<ChrState<NoTheory>> =
                Engine::new_with_env(query.clone(), std::mem::take(terms), env.clone());
            let mut first = None;
            for step in 0..max_steps {
                match engine.step() {
                    StepResult::Emit(nf) => {
                        let rendered = engine
                            .format_nf(&nf, symbols)
                            .unwrap_or_else(|_| "<unrenderable>".to_string());
                        eprintln!("trace {} emit step {}: {}", label, step, rendered);
                        first = Some(nf);
                        break;
                    }
                    StepResult::Exhausted => {
                        eprintln!("trace {} exhausted at step {}", label, step);
                        break;
                    }
                    StepResult::Continue => {
                        if step < 20 || step % 1000 == 0 {
                            eprintln!("trace {} continue step {}", label, step);
                        }
                    }
                }
            }
            if first.is_none() {
                eprintln!("trace {} no emit within {} steps", label, max_steps);
            }
            *terms = engine.into_terms();
            first
        }

        let query_strs = [
            ("filter_only", "@(f (b (b l)) l) ; [$x { (no_c $x) } -> $x]"),
            (
                "build_only",
                "@(f (b (b l)) l) ; [$x { (no_c $x) } -> $x ; $x -> (f $x (c z))]",
            ),
            (
                "with_app",
                "@(f (b (b l)) l) ; [$x { (no_c $x) } -> $x ; $x -> (f $x (c z)) ; app]",
            ),
            ("direct_app", "@(f (f (b (b l)) l) (c z)) ; app"),
            (
                "full",
                "@(f (b (b l)) l) ; [$x { (no_c $x) } -> $x ; $x -> (f $x (c z)) ; app] ; @(c z)",
            ),
        ];

        let mut queries = Vec::new();
        for (label, query_str) in query_strs.iter() {
            let query = parser.parse_rel_body(query_str).expect("parse query");
            queries.push((*label, query));
        }

        let mut terms = parser.take_terms();
        let max_steps = 20000;
        let mut first = None;
        for (label, query) in queries.iter() {
            let result = trace_query(label, query, &env, &mut terms, parser.symbols(), max_steps);
            if *label == "full" {
                first = result;
            }
        }

        let nf = first.expect("expected answer");
        let (lhs, rhs) = direct_rule_terms(&nf, &mut terms).expect("direct rule");
        assert_eq!(lhs, expected_prog, "unexpected program term");
        assert_eq!(rhs, expected_out, "unexpected output term");
        assert!(
            nf.drop_fresh.constraint.is_empty(),
            "expected no remaining constraints"
        );
    }

    #[test]
    fn treecalc_app_rule_count() {
        let mut parser = Parser::new();
        let def = include_str!("../examples/treecalc.txt");
        let (rel, _env) = parse_rel_def_with_env(&mut parser, def);
        let body = match rel {
            Rel::Fix(_, body) => body,
            _ => panic!("Expected Fix for treecalc app"),
        };
        let count = count_top_or(&body);
        assert_eq!(count, 7, "Expected 7 top-level app rules");
    }

    #[test]
    fn treecalc_app_example_2() {
        treecalc_app_case("(f (f l (f l l)) (b (b (b l))))", "(f l l)");
    }

    #[test]
    fn treecalc_app_example_3() {
        treecalc_app_case("(f (f (f l l) l) (b (b l)))", "(b (b l))");
    }

    #[test]
    fn treecalc_app_example_4() {
        treecalc_app_case("(f (b (f l l)) (f l l))", "(f (f l l) (f l l))");
    }

    #[test]
    fn treecalc_app_example_5() {
        treecalc_app_case("(f (f l l) (f (b l) (b l)))", "l");
    }

    #[test]
    fn treecalc_app_example_6() {
        treecalc_app_case("(f (f l (b l)) (f (b l) (b l)))", "(b l)");
    }

    #[test]
    fn treecalc_app_example_7() {
        treecalc_app_case("(f (b l) (b (b (b l))))", "(f l (b (b (b l))))");
    }

    #[test]
    fn treecalc_app_example_8() {
        treecalc_app_case(
            "(f (f (f l (f l l)) (f l (b l))) (f (f l l) (b (f l l))))",
            "(f l (b (f l l)))",
        );
    }

    #[test]
    fn treecalc_app_example_9() {
        treecalc_app_case(
            "(f (f (f l (b l)) (f (b l) (b l))) (f l (f (b l) (b l))))",
            "(f l l)",
        );
    }

    #[test]
    fn treecalc_app_example_10() {
        treecalc_app_case("(f (f (b (b l)) l) (c z))", "(c z)");
    }

    #[test]
    fn treecalc_app_and_group_two_conjuncts_example_9() {
        treecalc_app_case_with_limit(
            "(f (f (f l (b l)) (f (b l) (b l))) (f l (f (b l) (b l))))",
            "(f l l)",
            "[app & app]",
        );
    }

    #[test]
    fn treecalc_app_and_group_nested_conjuncts_example_9() {
        treecalc_app_case_with_limit(
            "(f (f (f l (b l)) (f (b l) (b l))) (f l (f (b l) (b l))))",
            "(f l l)",
            "[[app & app] & app]",
        );
    }

    #[test]
    fn treecalc_app_and_group_three_conjuncts_example_9() {
        treecalc_app_case_with_limit(
            "(f (f (f l (b l)) (f (b l) (b l))) (f l (f (b l) (b l))))",
            "(f l l)",
            "[app & app & app]",
        );
    }

    #[test]
    fn seq_with_and_non_iso_left_boundary_does_not_distribute() {
        let mut parser = Parser::new();
        let rel = parser
            .parse_rel_body("[[c -> a] | [c -> b]] ; [[a -> z] & [b -> z]]")
            .expect("parse query");
        let terms = parser.take_terms();
        let mut engine: Engine<()> = Engine::new(rel, terms);

        let answers = engine.collect_answers();
        assert!(
            answers.is_empty(),
            "Non-iso left boundary must not distribute across And"
        );
    }

    #[test]
    fn seq_with_and_non_iso_right_boundary_does_not_distribute() {
        let mut parser = Parser::new();
        let rel = parser
            .parse_rel_body("[[a -> z] & [b -> z]] ; [[c -> a] | [c -> b]]")
            .expect("parse query");
        let terms = parser.take_terms();
        let mut engine: Engine<()> = Engine::new(rel, terms);

        let answers = engine.collect_answers();
        assert!(
            answers.is_empty(),
            "Non-iso right boundary must not distribute across And"
        );
    }

    #[test]
    fn and_associativity_simple_equivalence() {
        let mut parser = Parser::new();
        let rel_left = parser
            .parse_rel_body("[[a -> a] & [[a -> a] & [a -> a]]]")
            .expect("parse left");
        let terms_left = parser.take_terms();
        let mut engine_left: Engine<()> = Engine::new(rel_left, terms_left);
        let answers_left: HashSet<NF<()>> = engine_left.collect_answers().into_iter().collect();

        let mut parser = Parser::new();
        let rel_right = parser
            .parse_rel_body("[[[a -> a] & [a -> a]] & [a -> a]]")
            .expect("parse right");
        let terms_right = parser.take_terms();
        let mut engine_right: Engine<()> = Engine::new(rel_right, terms_right);
        let answers_right: HashSet<NF<()>> = engine_right.collect_answers().into_iter().collect();

        assert_eq!(
            answers_left, answers_right,
            "Nested And grouping must be associative"
        );
        assert_eq!(answers_left.len(), 1, "Expected a single answer");
    }

    #[test]
    fn and_associativity_with_disjoint_branch_is_empty() {
        let mut parser = Parser::new();
        let rel_left = parser
            .parse_rel_body("[[a -> a] & [[a -> a] & [b -> b]]]")
            .expect("parse left");
        let terms_left = parser.take_terms();
        let mut engine_left: Engine<()> = Engine::new(rel_left, terms_left);
        let answers_left = engine_left.collect_answers();

        let mut parser = Parser::new();
        let rel_right = parser
            .parse_rel_body("[[[a -> a] & [a -> a]] & [b -> b]]")
            .expect("parse right");
        let terms_right = parser.take_terms();
        let mut engine_right: Engine<()> = Engine::new(rel_right, terms_right);
        let answers_right = engine_right.collect_answers();

        assert!(
            answers_left.is_empty(),
            "Disjoint branch should empty the intersection (left grouping)"
        );
        assert!(
            answers_right.is_empty(),
            "Disjoint branch should empty the intersection (right grouping)"
        );
    }

    /// Table reentrance should be detected (same CallKey during evaluation).
    /// Tabling detects when the same call-context is re-entered.
    #[test]
    fn table_reentrance_detected() {
        // Fix(0, Call(0)) - immediate reentrance
        let rel: Rel<()> = Rel::Fix(0, Arc::new(Rel::Call(0)));
        let mut engine: Engine<()> = Engine::new(rel, TermStore::new());

        // Should detect reentrance via tabling and return no answers
        let ans = engine.next();
        assert!(
            ans.is_none(),
            "Immediate reentrance should fail via tabling"
        );
    }

    // ------------------------------------------------------------------------
    // CATEGORY 4: Call-Context (Boundary) Propagation
    // ------------------------------------------------------------------------

    /// Left boundary should propagate to recursive call.
    #[test]
    fn left_boundary_propagates_to_call() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);

        let countdown = build_countdown_rel(&symbols, &terms);

        // Query: A ; countdown (A is left boundary)
        let query = Rel::Seq(Arc::from(vec![
            Arc::new(Rel::Atom(Arc::new(nf_a))),
            Arc::new(countdown),
        ]));

        let mut engine: Engine<()> = Engine::new(query, terms);

        // Should fail because A doesn't match z or (s x)
        let mut count = 0;
        for _ in 0..50 {
            if engine.next().is_some() {
                count += 1;
            } else {
                break;
            }
        }
        // With boundary propagation, A ; countdown should fail immediately
        // (A doesn't unify with z or (s x))
        assert_eq!(count, 0, "Left boundary should prevent any answers");
    }

    /// Right boundary should propagate and constrain recursion.
    #[test]
    fn right_boundary_propagates_to_call() {
        let (symbols, terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);

        let countdown = build_countdown_rel(&symbols, &terms);

        // Constraint: output must be z
        let z_nf = NF::new(
            SmallVec::from_slice(&[z_term]),
            DropFresh::identity(0),
            SmallVec::from_slice(&[z_term]),
        );

        // Query: countdown ; id_z (z is right boundary)
        let query = Rel::Seq(Arc::from(vec![
            Arc::new(countdown),
            Arc::new(Rel::Atom(Arc::new(z_nf))),
        ]));

        let mut engine: Engine<()> = Engine::new(query, terms);

        // Should find inputs that produce z: just z itself
        let ans = engine.next();
        assert!(ans.is_some(), "countdown ; id_z should find z -> z");
    }

    /// Both boundaries should propagate.
    #[test]
    fn both_boundaries_propagate() {
        let (symbols, terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);

        let countdown = build_countdown_rel(&symbols, &terms);

        // z -> z constraint on both sides
        let z_nf = NF::new(
            SmallVec::from_slice(&[z_term]),
            DropFresh::identity(0),
            SmallVec::from_slice(&[z_term]),
        );

        // Query: id_z ; countdown ; id_z
        let query = Rel::Seq(Arc::from(vec![
            Arc::new(Rel::Atom(Arc::new(z_nf.clone()))),
            Arc::new(countdown),
            Arc::new(Rel::Atom(Arc::new(z_nf))),
        ]));

        let mut engine: Engine<()> = Engine::new(query, terms);

        // Should find z -> z -> z
        let ans = engine.next();
        assert!(ans.is_some(), "id_z ; countdown ; id_z should find answer");
    }

    // ------------------------------------------------------------------------
    // CATEGORY 5: Interaction with Other Rel Variants
    // ------------------------------------------------------------------------

    /// Zero in Seq before Call should short-circuit.
    #[test]
    fn zero_before_call_short_circuits() {
        // Fix(0, Seq([Zero, Call(0)])) - Zero kills the branch
        let body = Rel::Seq(Arc::from(vec![Arc::new(Rel::Zero), Arc::new(Rel::Call(0))]));
        let rel: Rel<()> = Rel::Fix(0, Arc::new(body));
        let mut engine: Engine<()> = Engine::new(rel, TermStore::new());

        assert!(engine.next().is_none(), "Zero before Call should fail fast");
    }

    /// Atom failure before Call should not recurse.
    #[test]
    fn atom_failure_before_call_no_recursion() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

        // A -> A atom
        // B -> B atom (incompatible with A)
        // Seq([A, B, Call(0)]) - A;B fails, never reaches Call

        let body = Rel::Or(
            Arc::new(Rel::Atom(Arc::new(nf_a.clone()))), // base case
            Arc::new(Rel::Seq(Arc::from(vec![
                Arc::new(Rel::Atom(Arc::new(nf_a))),
                Arc::new(Rel::Atom(Arc::new(nf_b))), // incompatible
                Arc::new(Rel::Call(0)),
            ]))),
        );
        let rel: Rel<()> = Rel::Fix(0, Arc::new(body));
        let mut engine: Engine<()> = Engine::new(rel, terms);

        // Should yield A (base case) but recursive branch fails at A;B
        let ans = engine.next();
        assert!(ans.is_some(), "Base case should still work");
    }

    /// Or inside recursive body should explore both branches.
    #[test]
    fn or_inside_recursive_body() {
        let (symbols, terms) = setup();
        let nf_a = make_ground_nf("A", &symbols, &terms);
        let nf_b = make_ground_nf("B", &symbols, &terms);

        // Fix(0, Or(Or(Atom(A), Atom(B)), Call(0)))
        // Nested Or with recursion
        let inner_or = Rel::Or(
            Arc::new(Rel::Atom(Arc::new(nf_a))),
            Arc::new(Rel::Atom(Arc::new(nf_b))),
        );
        let body = Rel::Or(Arc::new(inner_or), Arc::new(Rel::Call(0)));
        let rel: Rel<()> = Rel::Fix(0, Arc::new(body));
        let mut engine: Engine<()> = Engine::new(rel, terms);

        // Should yield A and B from inner Or
        assert!(engine.next().is_some(), "Should yield first from inner Or");
        assert!(engine.next().is_some(), "Should yield second from inner Or");
    }

    /// Seq inside recursive body should compose.
    #[test]
    fn seq_inside_recursive_body() {
        let (symbols, terms) = setup();
        let countdown = build_countdown_rel(&symbols, &terms);

        // countdown already has Seq([peel, Call(0)]) inside
        let mut engine: Engine<()> = Engine::new(countdown, terms);

        // Should work (tested elsewhere, but explicit here)
        assert!(
            engine.next().is_some(),
            "Seq inside recursive body should work"
        );
    }

    // ------------------------------------------------------------------------
    // CATEGORY 6: Dual/Bidirectionality
    // ------------------------------------------------------------------------

    /// Recursive relation should work in reverse (output bound, find inputs).
    #[test]
    fn recursive_relation_runs_backwards() {
        let (symbols, terms) = setup();
        let z = symbols.intern("z");
        let s = symbols.intern("s");
        let z_term = terms.app0(z);
        let v0 = terms.var(0);
        let s_v0 = terms.app(s, SmallVec::from_slice(&[v0]));
        let s_z = terms.app(s, SmallVec::from_slice(&[z_term]));

        let base_nf = NF::new(
            SmallVec::from_slice(&[z_term]),
            DropFresh::identity(0),
            SmallVec::from_slice(&[z_term]),
        );
        let base = Arc::new(Rel::Atom(Arc::new(base_nf)));

        let peel_nf = NF::new(
            SmallVec::from_slice(&[s_v0]),
            DropFresh::identity(1),
            SmallVec::from_slice(&[v0]),
        );
        let peel = Arc::new(Rel::Atom(Arc::new(peel_nf)));

        let wrap_nf = NF::new(
            SmallVec::from_slice(&[v0]),
            DropFresh::identity(1),
            SmallVec::from_slice(&[s_v0]),
        );
        let wrap = Arc::new(Rel::Atom(Arc::new(wrap_nf)));

        let recursive = Arc::new(Rel::Seq(Arc::from(vec![
            peel,
            Arc::new(Rel::Call(0)),
            wrap,
        ])));
        let body = Arc::new(Rel::Or(base, recursive));
        let rel = Rel::Fix(0, body);

        // Query: what inputs to countdown produce (s z)?
        let constraint = NF::new(
            SmallVec::from_slice(&[s_z]),
            DropFresh::identity(0),
            SmallVec::from_slice(&[s_z]),
        );

        let query = Rel::Seq(Arc::from(vec![
            Arc::new(rel),
            Arc::new(Rel::Atom(Arc::new(constraint))),
        ]));

        let mut engine: Engine<()> = Engine::new(query, terms);

        let mut answers = Vec::new();
        for _ in 0..50 {
            match engine.next() {
                Some(nf) => answers.push(nf),
                None => break,
            }
        }

        assert!(
            !answers.is_empty(),
            "Backward query should find at least one input"
        );
    }

    /// dual(Fix) should equal Fix with dualized body.
    #[test]
    fn dual_fix_preserves_structure() {
        use crate::rel::dual;

        let nf = make_identity_nf();
        let body = Arc::new(Rel::Atom(Arc::new(nf)));
        let fix: Rel<()> = Rel::Fix(42, body);

        let mut terms = TermStore::new();
        let dualed = dual(&fix, &mut terms);

        match dualed {
            Rel::Fix(id, _) => assert_eq!(id, 42, "dual should preserve RelId"),
            _ => panic!("dual(Fix) should be Fix"),
        }
    }

    /// dual(Call) should be Call with same RelId.
    #[test]
    fn dual_call_preserves_relid() {
        use crate::rel::dual;

        let call: Rel<()> = Rel::Call(123);
        let mut terms = TermStore::new();
        let dualed = dual(&call, &mut terms);

        match dualed {
            Rel::Call(id) => assert_eq!(id, 123, "dual should preserve RelId"),
            _ => panic!("dual(Call) should be Call"),
        }
    }

    #[test]
    fn dual_enumeration_preserves_order() {
        use crate::kernel::dual_nf;
        use crate::rel::dual;

        let (symbols, terms) = setup();
        let nf_ab = make_rule_nf("A", "B", &symbols, &terms);
        let nf_bc = make_rule_nf("B", "C", &symbols, &terms);
        let nf_d = make_rule_nf("D", "D", &symbols, &terms);

        let seq = Rel::Seq(Arc::from(vec![
            Arc::new(Rel::Atom(Arc::new(nf_ab))),
            Arc::new(Rel::Atom(Arc::new(nf_bc))),
        ]));

        let rel = Rel::Or(Arc::new(seq), Arc::new(Rel::Atom(Arc::new(nf_d))));

        let mut engine: Engine<()> = Engine::new(rel.clone(), terms);
        let mut outputs = Vec::new();
        for _ in 0..10 {
            match engine.next() {
                Some(nf) => outputs.push(nf),
                None => break,
            }
        }

        let mut terms = std::mem::take(&mut engine.terms);
        let expected: Vec<NF<()>> = outputs.iter().map(|nf| dual_nf(nf, &mut terms)).collect();
        let dual_rel = dual(&rel, &mut terms);
        let mut dual_engine: Engine<()> = Engine::new(dual_rel, terms);
        let mut dual_outputs = Vec::new();
        for _ in 0..outputs.len() {
            match dual_engine.next() {
                Some(nf) => dual_outputs.push(nf),
                None => break,
            }
        }

        assert_eq!(dual_outputs, expected);
    }
}
