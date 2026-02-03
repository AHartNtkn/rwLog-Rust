//! Public API for the dataflow runtime.
//!
//! The Engine provides an iterator-like interface for evaluating
//! relational queries with fuel-bounded execution.

use crate::constraint::ConstraintOps;
use crate::nf::NF;
use crate::rel::{Rel, RelId};
use crate::runtime::compile::{compile_program, compile_rel};
use crate::runtime::goal::Goal;
use crate::runtime::node::NodeId;
use crate::runtime::scheduler::Runtime;
use crate::symbol::SymbolStore;
use crate::term::TermStore;
use std::collections::HashMap;

/// Error returned when evaluation runs out of fuel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutOfFuel {
    /// Fuel that was allocated.
    pub fuel: usize,
    /// Number of answers produced before running out.
    pub answers_produced: usize,
}

impl std::fmt::Display for OutOfFuel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Out of fuel: {} allocated, {} answers produced",
            self.fuel, self.answers_produced
        )
    }
}

impl std::error::Error for OutOfFuel {}

/// Result type for fuel-bounded operations.
pub type FuelResult<T> = Result<T, OutOfFuel>;

/// The main evaluation engine.
///
/// Engine wraps a Runtime and provides a streaming interface for
/// pulling answers from a compiled query.
pub struct Engine<C> {
    /// The underlying runtime.
    runtime: Runtime<C>,
    /// Root node ID (the query).
    root: NodeId,
    /// Cursor into root's output vector.
    root_cursor: usize,
    /// Term store (shared ownership for borrowing).
    terms: TermStore,
    /// Total answers returned so far.
    answers_returned: usize,
}

impl<C: ConstraintOps> Engine<C> {
    /// Create a new engine from a compiled runtime and root node.
    pub fn new(runtime: Runtime<C>, root: NodeId, terms: TermStore) -> Self {
        Self {
            runtime,
            root,
            root_cursor: 0,
            terms,
            answers_returned: 0,
        }
    }

    /// Create an engine from a Rel expression.
    ///
    /// Note: The `terms` parameter must be the same TermStore used to create
    /// the NFs in the Rel expression. TermIds are only valid within their
    /// originating TermStore.
    pub fn from_rel(rel: &Rel<C>, mut terms: TermStore) -> Option<Self> {
        let mut runtime = Runtime::new();
        let mut env = HashMap::new();

        let root = compile_rel(rel, &mut env, &mut runtime, &mut terms)?;
        runtime.activate(root);

        Some(Self::new(runtime, root, terms))
    }

    /// Create an engine from definitions and a query.
    ///
    /// Note: The `terms` parameter must be the same TermStore used to create
    /// the NFs in the definitions and query. TermIds are only valid within
    /// their originating TermStore.
    pub fn from_program(
        defs: &[(RelId, Rel<C>)],
        query: &Rel<C>,
        mut terms: TermStore,
    ) -> Option<Self> {
        let mut runtime = Runtime::new();

        let root = compile_program(defs, query, &mut runtime, &mut terms)?;
        runtime.activate(root);

        Some(Self::new(runtime, root, terms))
    }

    /// Get the next answer with a fuel budget.
    ///
    /// Returns:
    /// - `Ok(Some(nf))` - next answer
    /// - `Ok(None)` - query exhausted (no more answers possible)
    /// - `Err(OutOfFuel)` - ran out of fuel, but more work may be possible
    pub fn next_with_fuel(&mut self, fuel: usize) -> FuelResult<Option<NF<C>>> {
        // Check if we already have an unread answer
        let root_len = self
            .runtime
            .get_node(self.root)
            .map(|n| n.state.out_vec.len())
            .unwrap_or(0);

        if self.root_cursor < root_len {
            let answer = self
                .runtime
                .get_node(self.root)
                .and_then(|n| n.state.out_vec.get(self.root_cursor))
                .cloned();
            self.root_cursor += 1;
            self.answers_returned += 1;
            return Ok(answer);
        }

        // Need to run the scheduler to get more answers
        self.runtime.activate(self.root);

        // Add unconstrained goal if needed
        let has_goals = self
            .runtime
            .get_node(self.root)
            .map(|n| !n.state.demand_goals.is_empty())
            .unwrap_or(false);
        if !has_goals {
            self.runtime
                .add_demand(self.root, Goal::unconstrained(), &mut self.terms);
        }

        // Run with fuel, stopping when we get a new answer
        let initial_cursor = self.root_cursor;
        let stop_when = |rt: &Runtime<C>| {
            rt.get_node(self.root)
                .map(|n| n.state.out_vec.len())
                .unwrap_or(0)
                > initial_cursor
        };

        let remaining = self
            .runtime
            .run_with_fuel(fuel, stop_when, &mut self.terms);

        // Check if we got an answer
        let root_len = self
            .runtime
            .get_node(self.root)
            .map(|n| n.state.out_vec.len())
            .unwrap_or(0);

        if self.root_cursor < root_len {
            let answer = self
                .runtime
                .get_node(self.root)
                .and_then(|n| n.state.out_vec.get(self.root_cursor))
                .cloned();
            self.root_cursor += 1;
            self.answers_returned += 1;
            return Ok(answer);
        }

        // No new answer - check if we're exhausted or out of fuel
        if self.runtime.worklist.is_empty() {
            // Exhausted
            Ok(None)
        } else if remaining == 0 {
            // Out of fuel
            Err(OutOfFuel {
                fuel,
                answers_produced: self.answers_returned,
            })
        } else {
            // Worklist is not empty but we made no progress - likely exhausted
            Ok(None)
        }
    }

    /// Get all answers up to a limit, with a fuel budget per answer.
    pub fn collect_with_fuel(
        &mut self,
        max_answers: usize,
        fuel_per_answer: usize,
    ) -> FuelResult<Vec<NF<C>>> {
        let mut results = Vec::new();

        for _ in 0..max_answers {
            match self.next_with_fuel(fuel_per_answer) {
                Ok(Some(nf)) => results.push(nf),
                Ok(None) => break,
                Err(e) => {
                    if results.is_empty() {
                        return Err(e);
                    }
                    // Got some results before running out of fuel
                    break;
                }
            }
        }

        Ok(results)
    }

    /// Get access to the term store.
    pub fn terms(&self) -> &TermStore {
        &self.terms
    }

    /// Get mutable access to the term store.
    pub fn terms_mut(&mut self) -> &mut TermStore {
        &mut self.terms
    }

    /// Get the number of answers returned so far.
    pub fn answers_returned(&self) -> usize {
        self.answers_returned
    }

    /// Get access to the underlying runtime (for inspection).
    pub fn runtime(&self) -> &Runtime<C> {
        &self.runtime
    }

    /// Consume the engine and return the TermStore.
    pub fn into_terms(self) -> TermStore {
        self.terms
    }

    /// Format an NF as a readable string.
    pub fn format_nf(&self, nf: &NF<C>, symbols: &SymbolStore) -> Result<String, String> {
        let match_str = self.format_boundary(&nf.match_boundary, symbols)?;
        let build_str = self.format_boundary(&nf.build_boundary, symbols)?;
        Ok(format!("{} -> {}", match_str, build_str))
    }

    /// Format a boundary (list of term IDs) as a string.
    fn format_boundary(
        &self,
        boundary: &[crate::term::TermId],
        symbols: &SymbolStore,
    ) -> Result<String, String> {
        if boundary.is_empty() {
            return Ok("()".to_string());
        }
        if boundary.len() == 1 {
            return self.format_term(boundary[0], symbols);
        }
        let parts: Result<Vec<String>, String> = boundary
            .iter()
            .map(|&t| self.format_term(t, symbols))
            .collect();
        Ok(format!("({})", parts?.join(", ")))
    }

    /// Format a single term as a string.
    fn format_term(
        &self,
        term_id: crate::term::TermId,
        symbols: &SymbolStore,
    ) -> Result<String, String> {
        match self.terms.resolve(term_id) {
            None => Err(format!("Invalid term ID: {:?}", term_id)),
            Some(term) => match term {
                crate::term::Term::Var(idx) => Ok(format!("${}", idx)),
                crate::term::Term::App(func, children) => {
                    let func_name = symbols.resolve(func).unwrap_or("?");
                    if children.is_empty() {
                        Ok(func_name.to_string())
                    } else {
                        let args: Result<Vec<String>, String> = children
                            .iter()
                            .map(|&c| self.format_term(c, symbols))
                            .collect();
                        Ok(format!("({} {})", func_name, args?.join(" ")))
                    }
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime::compile::{atom, call, fix, or, seq};
    use smallvec::smallvec;

    fn setup() -> SymbolStore {
        SymbolStore::new()
    }

    // ========================================================================
    // BASIC ENGINE TESTS
    // ========================================================================

    #[test]
    fn engine_single_atom() {
        let symbols = setup();
        let terms = TermStore::new();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        let rel: Rel<()> = atom(nf);
        let mut engine = Engine::from_rel(&rel, terms).unwrap();

        // First answer
        let result = engine.next_with_fuel(100).unwrap();
        assert!(result.is_some());

        // Second call should return None (exhausted)
        let result = engine.next_with_fuel(100).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn engine_or_two_atoms() {
        let symbols = setup();
        let terms = TermStore::new();
        let z = symbols.intern("z");
        let s = symbols.intern("s");
        let z_term = terms.app0(z);
        let s_z = terms.app1(s, z_term);

        let nf1: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);
        let nf2: NF<()> = NF::new(smallvec![s_z], smallvec![s_z]);

        let rel: Rel<()> = or(atom(nf1), atom(nf2));
        let mut engine = Engine::from_rel(&rel, terms).unwrap();

        // Should get two answers
        let answers = engine.collect_with_fuel(10, 100).unwrap();
        assert_eq!(answers.len(), 2);
    }

    #[test]
    fn engine_compose_basic() {
        let symbols = setup();
        let terms = TermStore::new();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);

        // z -> z composed with z -> z should give z -> z
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        let rel: Rel<()> = seq(vec![atom(nf.clone()), atom(nf)]);
        let mut engine = Engine::from_rel(&rel, terms).unwrap();

        let result = engine.next_with_fuel(100).unwrap();
        assert!(result.is_some());
    }

    #[test]
    fn engine_out_of_fuel() {
        let symbols = setup();
        let terms = TermStore::new();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        // Create a recursive relation that generates infinite answers
        // fix(0, Or(atom, Seq(atom, call(0))))
        let rel: Rel<()> = fix(0, or(atom(nf.clone()), seq(vec![atom(nf), call(0)])));
        let mut engine = Engine::from_rel(&rel, terms).unwrap();

        // Get first answer (should succeed with low fuel)
        let result = engine.next_with_fuel(100);
        assert!(result.is_ok());

        // Try to get many more with very low fuel
        // This might run out of fuel
        let _ = engine.collect_with_fuel(100, 10);
    }

    // ========================================================================
    // PEANO ADDITION TEST
    // ========================================================================

    #[test]
    fn engine_peano_add_generates_stream() {
        let symbols = setup();
        let terms = TermStore::new();

        // Constructors
        let z = symbols.intern("z");
        let s = symbols.intern("s");
        let cons = symbols.intern("cons");

        // Terms
        let z_term = terms.app0(z);
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // Base case: (cons z x) -> x
        let cons_z_x = terms.app2(cons, z_term, v0);
        let nf_base: NF<()> = NF::new(smallvec![cons_z_x], smallvec![v0]);

        // Recursive step:
        // pre: (cons (s n) x) -> (cons n x)
        let s_v0 = terms.app1(s, v0);
        let cons_sn_x = terms.app2(cons, s_v0, v1);
        let cons_n_x = terms.app2(cons, v0, v1);
        let nf_pre: NF<()> = NF::new(smallvec![cons_sn_x], smallvec![cons_n_x]);

        // post: x -> (s x)
        let nf_post: NF<()> = NF::new(smallvec![v0], smallvec![s_v0]);

        // add = Fix(0, Or(base, Seq(pre, call(0), post)))
        let add: Rel<()> = fix(
            0,
            or(atom(nf_base), seq(vec![atom(nf_pre), call(0), atom(nf_post)])),
        );

        let mut engine = Engine::from_rel(&add, terms).unwrap();

        // Get first few answers
        let answers = engine.collect_with_fuel(3, 5000).unwrap();

        // Should get at least the base case
        assert!(!answers.is_empty(), "Should produce at least one answer");
    }

    // ========================================================================
    // PROGRAM API TEST
    // ========================================================================

    #[test]
    fn engine_from_program() {
        let symbols = setup();
        let terms = TermStore::new();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        // Define: 0 -> atom
        let defs: Vec<(RelId, Rel<()>)> = vec![(0, atom(nf))];

        // Query: call(0)
        let query: Rel<()> = call(0);

        let mut engine = Engine::from_program(&defs, &query, terms).unwrap();

        let result = engine.next_with_fuel(100).unwrap();
        assert!(result.is_some());
    }

    // ========================================================================
    // RECURSIVE PEEL TEST - MIMICS REPL USAGE
    // ========================================================================

    #[test]
    fn engine_recursive_peel_direct_call() {
        let symbols = setup();
        let terms = TermStore::new();

        // Constructors
        let z = symbols.intern("z");
        let s = symbols.intern("s");

        // Terms
        let z_term = terms.app0(z);
        let v0 = terms.var(0);

        // Base case: z -> z
        let nf_base: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        // Recursive: (s $0) -> $0 ; peel
        let s_v0 = terms.app1(s, v0);
        let nf_step: NF<()> = NF::new(smallvec![s_v0], smallvec![v0]);

        // peel = Or(base, Seq(step, call(0)))
        // RelId 0 = peel
        let peel_body: Rel<()> = or(atom(nf_base), seq(vec![atom(nf_step), call(0)]));

        // Defs: peel_id -> body
        let defs: Vec<(RelId, Rel<()>)> = vec![(0, peel_body)];

        // Query: just call(0) - should give peel's outputs directly
        let query: Rel<()> = call(0);

        let mut engine = Engine::from_program(&defs, &query, terms).unwrap();

        eprintln!("Starting engine test for direct peel call");

        // Get first answer - should be z -> z (base case)
        let result = engine.next_with_fuel(1000);
        eprintln!("Result 1: {:?}", result);
        assert!(result.is_ok(), "First result should be ok");
        let first = result.unwrap();
        assert!(first.is_some(), "Should get at least the base case z -> z");
        eprintln!("Got first answer");

        // Get more answers
        for i in 2..=5 {
            let result = engine.next_with_fuel(1000);
            eprintln!("Result {}: {:?}", i, result);
            if let Ok(None) = result {
                eprintln!("Exhausted at answer {}", i);
                break;
            }
        }
    }

    #[test]
    fn engine_recursive_peel_via_program() {
        let symbols = setup();
        let terms = TermStore::new();

        // Constructors
        let z = symbols.intern("z");
        let s = symbols.intern("s");

        // Terms
        let z_term = terms.app0(z);
        let v0 = terms.var(0);

        // Base case: z -> z
        let nf_base: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        // Recursive: (s $0) -> $0 ; peel
        let s_v0 = terms.app1(s, v0);
        let nf_step: NF<()> = NF::new(smallvec![s_v0], smallvec![v0]);

        // peel = Or(base, Seq(step, call(0)))
        // RelId 0 = peel
        let peel_body: Rel<()> = or(atom(nf_base), seq(vec![atom(nf_step), call(0)]));

        // Defs: peel_id -> body
        let defs: Vec<(RelId, Rel<()>)> = vec![(0, peel_body)];

        // Query: @(s (s z)) ; peel
        // = Seq(Atom((s (s z)) -> (s (s z))), Call(0))
        let s_s_z = terms.app1(s, terms.app1(s, z_term));
        let nf_query: NF<()> = NF::new(smallvec![s_s_z], smallvec![s_s_z]);
        let query: Rel<()> = seq(vec![atom(nf_query), call(0)]);

        let mut engine = Engine::from_program(&defs, &query, terms).unwrap();

        // Debug: print node structure
        eprintln!("\n=== Node Structure ===");
        for (i, node) in engine.runtime.nodes.iter().enumerate() {
            eprintln!("Node {}: {:?}", i, node.kind);
        }
        eprintln!("Root: {:?}", engine.root);
        eprintln!("======================\n");

        // Activate root and add initial goal (matching what next_with_fuel does)
        engine.runtime.activate(engine.root);
        engine
            .runtime
            .add_demand(engine.root, Goal::unconstrained(), &mut engine.terms);

        // Step by step with debug - use run_with_fuel(1, ...) for single steps
        for step in 0..50 {
            // Show state before step
            eprintln!("\n--- Step {} ---", step);
            eprintln!("Worklist: {:?}", engine.runtime.worklist);
            for (i, node) in engine.runtime.nodes.iter().enumerate() {
                let state_goals: Vec<_> = node.state.demand_goals.iter().collect();
                // Also show Table/Call specific goals
                let kind_goals = match &node.kind {
                    crate::runtime::node::NodeKind::Table { goals, .. } => {
                        format!("table_goals={}", goals.len())
                    }
                    crate::runtime::node::NodeKind::Call {
                        registered_goals, ..
                    } => format!("registered={}", registered_goals.len()),
                    _ => String::new(),
                };
                eprintln!(
                    "  Node {}: demand_goals={}, outputs={}, exhausted={}, need={} {}",
                    i,
                    state_goals.len(),
                    node.state.out_vec.len(),
                    node.state.exhausted,
                    node.state.need,
                    kind_goals
                );
            }

            if engine.runtime.worklist.is_empty() {
                eprintln!("Worklist empty, stopping.");
                break;
            }

            // Do one step
            let root = engine.root;
            let root_cursor = engine.root_cursor;
            engine.runtime.run_with_fuel(
                1,
                |rt| {
                    rt.get_node(root)
                        .map(|n| n.state.out_vec.len())
                        .unwrap_or(0)
                        > root_cursor
                },
                &mut engine.terms,
            );

            // Check if we got an answer
            let root_len = engine
                .runtime
                .get_node(engine.root)
                .map(|n| n.state.out_vec.len())
                .unwrap_or(0);
            if engine.root_cursor < root_len {
                eprintln!("GOT AN ANSWER at step {}!", step);
                break;
            }
        }

        // Should get an answer: (s (s z)) -> z
        let first = engine.next_with_fuel(100);
        assert!(first.is_ok(), "Should not run out of fuel: {:?}", first);
        assert!(first.as_ref().unwrap().is_some(), "Should get one answer");

        // Verify the answer has the right shape
        let nf = first.unwrap().unwrap();
        // match_boundary should be s(s(z)), build_boundary should be z
        assert_eq!(nf.match_boundary.len(), 1);
        assert_eq!(nf.build_boundary.len(), 1);
    }

    /// Test that a recursive relation exhausts properly when only base case matches.
    /// This is the engine-level equivalent of repl::tests::recursive_base_case_only_then_next
    ///
    /// listlen = Or(nil->z, Seq(cons h t -> t, call(listlen), n -> s n))
    /// Query: @nil ; listlen
    /// Expected: One answer (nil -> z), then exhausted
    #[test]
    fn engine_recursive_base_case_exhausts() {
        let symbols = setup();
        let terms = TermStore::new();

        // Constructors
        let nil = symbols.intern("nil");
        let cons = symbols.intern("cons");
        let z = symbols.intern("z");
        let s = symbols.intern("s");

        // Terms
        let nil_term = terms.app0(nil);
        let z_term = terms.app0(z);
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // Base case: nil -> z
        let nf_base: NF<()> = NF::new(smallvec![nil_term], smallvec![z_term]);

        // Recursive step 1: (cons $h $t) -> $t
        let cons_h_t = terms.app2(cons, v0, v1);
        let nf_step1: NF<()> = NF::new(smallvec![cons_h_t], smallvec![v1]);

        // Recursive step 2: $n -> (s $n)
        let s_v0 = terms.app1(s, v0);
        let nf_step2: NF<()> = NF::new(smallvec![v0], smallvec![s_v0]);

        // listlen = Or(base, Seq(step1, call(0), step2))
        let listlen_body: Rel<()> = or(
            atom(nf_base),
            seq(vec![atom(nf_step1), call(0), atom(nf_step2)]),
        );

        let defs: Vec<(RelId, Rel<()>)> = vec![(0, listlen_body)];

        // Query: @nil ; listlen
        let nf_query: NF<()> = NF::new(smallvec![nil_term], smallvec![nil_term]);
        let query: Rel<()> = seq(vec![atom(nf_query), call(0)]);

        let mut engine = Engine::from_program(&defs, &query, terms).unwrap();

        // First answer should be nil -> z
        let result1 = engine.next_with_fuel(1000);
        assert!(result1.is_ok(), "First query should not run out of fuel");
        let answer1 = result1.unwrap();
        assert!(answer1.is_some(), "Should produce first answer (nil -> z)");

        // Second query should exhaust (return None), not hang
        let result2 = engine.next_with_fuel(1000);
        assert!(result2.is_ok(), "Second query should not run out of fuel");
        let answer2 = result2.unwrap();
        assert!(answer2.is_none(), "Should be exhausted after base case, got: {:?}", answer2);
    }
}
