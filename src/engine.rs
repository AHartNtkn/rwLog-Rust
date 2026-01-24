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
#[path = "tests/engine.rs"]
mod tests;
