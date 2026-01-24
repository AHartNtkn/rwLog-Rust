//! Node - Search tree nodes for the evaluation engine.
//!
//! The Node enum represents the search tree structure.
//! Or nodes use rotation interleaving for fair search.
//! Work nodes embed active computations (Seq, And, Fix).

use crate::constraint::ConstraintOps;
use crate::nf::NF;
use crate::term::TermStore;
use crate::work::{Work, WorkStep};

/// Search tree node.
///
/// Represents a point in the search space:
/// - `Fail`: Dead end, no more answers
/// - `Or(left, right)`: Disjunction with rotation interleaving
/// - `Emit(nf, rest)`: Yield an answer, continue with rest
/// - `Work(work)`: Active computation (Seq, And, Fix)
#[derive(Clone, Debug)]
pub enum Node<C: ConstraintOps> {
    /// Failed/exhausted branch - no more answers.
    Fail,
    /// Disjunction: search left first, then rotate.
    /// Rotation: Or(left', right) -> Or(right, left')
    Or(Box<Node<C>>, Box<Node<C>>),
    /// Emit an answer and continue with the rest.
    Emit(NF<C>, Box<Node<C>>),
    /// Active work - computations that may emit, split, or complete.
    Work(Box<Work<C>>),
}

/// Result of stepping a Node one notch.
#[derive(Clone, Debug)]
pub enum NodeStep<C: ConstraintOps> {
    /// Produced an answer and the remaining node.
    Emit(NF<C>, Node<C>),
    /// No answer yet, but node updated (rotation or work progress).
    Continue(Node<C>),
    /// Exhausted - no more answers.
    Exhausted,
}

/// Step a node once using Or rotation and Work stepping.
pub fn step_node<C: ConstraintOps>(node: Node<C>, terms: &mut TermStore) -> NodeStep<C> {
    match node {
        Node::Fail => NodeStep::Exhausted,

        Node::Emit(nf, rest) => NodeStep::Emit(nf, *rest),

        Node::Or(left, right) => {
            let left_node = *left;
            match step_node(left_node, terms) {
                NodeStep::Emit(nf, new_left) => {
                    NodeStep::Emit(nf, Node::Or(right, Box::new(new_left)))
                }
                NodeStep::Exhausted => NodeStep::Continue(*right),
                NodeStep::Continue(new_left) => {
                    NodeStep::Continue(Node::Or(right, Box::new(new_left)))
                }
            }
        }

        Node::Work(mut work) => match work.step(terms) {
            WorkStep::Done => NodeStep::Continue(Node::Fail),
            WorkStep::Emit(nf, next_work) => NodeStep::Emit(nf, Node::Work(next_work)),
            WorkStep::Split(left_node, right_node) => {
                NodeStep::Continue(Node::Or(left_node, right_node))
            }
            WorkStep::More(next_work) => NodeStep::Continue(Node::Work(next_work)),
        },
    }
}


#[cfg(test)]
mod tests;
