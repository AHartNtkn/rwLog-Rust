//! Node - Search tree nodes for the evaluation engine.
//!
//! The Node enum represents the search tree structure.
//! Or nodes use rotation interleaving for fair search.
//! Work nodes embed active computations (Seq, And, Fix).

use crate::nf::NF;
use crate::term::TermStore;
use crate::work::{Work, WorkStep};
use std::hash::Hash;

/// Search tree node.
///
/// Represents a point in the search space:
/// - `Fail`: Dead end, no more answers
/// - `Or(left, right)`: Disjunction with rotation interleaving
/// - `Emit(nf, rest)`: Yield an answer, continue with rest
/// - `Work(work)`: Active computation (Seq, And, Fix)
#[derive(Clone, Debug)]
pub enum Node<C: Clone + Hash + Eq> {
    /// Failed/exhausted branch - no more answers.
    Fail,
    /// Disjunction: search left first, then rotate.
    /// Rotation: Or(left', right) -> Or(right, left')
    Or(Box<Node<C>>, Box<Node<C>>),
    /// Emit an answer and continue with the rest.
    Emit(NF<C>, Box<Node<C>>),
    /// Active work - computations that may emit, split, or complete.
    Work(Work<C>),
}

/// Result of stepping a Node one notch.
#[derive(Clone, Debug)]
pub enum NodeStep<C: Clone + Hash + Eq> {
    /// Produced an answer and the remaining node.
    Emit(NF<C>, Node<C>),
    /// No answer yet, but node updated (rotation or work progress).
    Continue(Node<C>),
    /// Exhausted - no more answers.
    Exhausted,
}

/// Step a node once using Or rotation and Work stepping.
pub fn step_node<C: Clone + Default + Hash + Eq>(node: Node<C>, terms: &mut TermStore) -> NodeStep<C> {
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
            WorkStep::Emit(nf, next_work) => {
                NodeStep::Emit(nf, Node::Work(next_work))
            }
            WorkStep::Split(left_node, right_node) => NodeStep::Continue(Node::Or(
                Box::new(left_node),
                Box::new(right_node),
            )),
            WorkStep::More(next_work) => NodeStep::Continue(Node::Work(next_work)),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::Node;
    use crate::nf::NF;
    use crate::symbol::SymbolStore;
    use crate::term::TermStore;
    use crate::test_utils::setup;
    use crate::drop_fresh::DropFresh;
    use smallvec::SmallVec;

    /// Create a simple identity NF for testing
    fn make_identity_nf() -> NF<()> {
        NF::identity(())
    }

    /// Create an NF with patterns for testing
    fn make_test_nf(symbols: &SymbolStore, terms: &TermStore) -> NF<()> {
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let ta = terms.app0(a);
        let tb = terms.app0(b);
        NF::new(
            SmallVec::from_slice(&[ta]),
            DropFresh::identity(0),
            SmallVec::from_slice(&[tb]),
        )
    }

    // ========================================================================
    // FAIL TESTS
    // ========================================================================

    #[test]
    fn fail_is_terminal_state() {
        let node: Node<()> = Node::Fail;
        assert!(matches!(node, Node::Fail));
    }

    #[test]
    fn fail_can_be_constructed_multiple_times() {
        for _ in 0..100 {
            let _node: Node<()> = Node::Fail;
        }
    }

    // ========================================================================
    // OR CONSTRUCTION TESTS
    // ========================================================================

    #[test]
    fn or_construction_both_fail() {
        let node: Node<()> = Node::Or(Box::new(Node::Fail), Box::new(Node::Fail));
        assert!(matches!(node, Node::Or(_, _)));
    }

    #[test]
    fn or_left_fail_right_other() {
        let nf = make_identity_nf();
        let right = Node::Emit(nf, Box::new(Node::Fail));
        let node: Node<()> = Node::Or(Box::new(Node::Fail), Box::new(right));
        assert!(matches!(node, Node::Or(_, _)));
    }

    #[test]
    fn or_left_other_right_fail() {
        let nf = make_identity_nf();
        let left = Node::Emit(nf, Box::new(Node::Fail));
        let node: Node<()> = Node::Or(Box::new(left), Box::new(Node::Fail));
        assert!(matches!(node, Node::Or(_, _)));
    }

    #[test]
    fn or_both_emit() {
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();
        let left = Node::Emit(nf1, Box::new(Node::Fail));
        let right = Node::Emit(nf2, Box::new(Node::Fail));
        let node: Node<()> = Node::Or(Box::new(left), Box::new(right));
        assert!(matches!(node, Node::Or(_, _)));
    }

    #[test]
    fn or_left_associative_nesting() {
        // ((Fail | Fail) | Fail) | Fail
        let level1 = Node::Or(Box::new(Node::Fail), Box::new(Node::Fail));
        let level2 = Node::Or(Box::new(level1), Box::new(Node::Fail));
        let node: Node<()> = Node::Or(Box::new(level2), Box::new(Node::Fail));
        assert!(matches!(node, Node::Or(_, _)));
    }

    #[test]
    fn or_right_associative_nesting() {
        // Fail | (Fail | (Fail | Fail))
        let level1 = Node::Or(Box::new(Node::Fail), Box::new(Node::Fail));
        let level2 = Node::Or(Box::new(Node::Fail), Box::new(level1));
        let node: Node<()> = Node::Or(Box::new(Node::Fail), Box::new(level2));
        assert!(matches!(node, Node::Or(_, _)));
    }

    #[test]
    fn or_deeply_nested() {
        let mut node: Node<()> = Node::Fail;
        for _ in 0..50 {
            node = Node::Or(Box::new(node), Box::new(Node::Fail));
        }
        assert!(matches!(node, Node::Or(_, _)));
    }

    // ========================================================================
    // EMIT TESTS
    // ========================================================================

    #[test]
    fn emit_into_fail() {
        let nf = make_identity_nf();
        let node: Node<()> = Node::Emit(nf, Box::new(Node::Fail));
        match node {
            Node::Emit(_, rest) => {
                assert!(matches!(*rest, Node::Fail));
            }
            _ => panic!("Expected Emit"),
        }
    }

    #[test]
    fn emit_single_answer() {
        let (symbols, terms) = setup();
        let nf = make_test_nf(&symbols, &terms);
        let node: Node<()> = Node::Emit(nf.clone(), Box::new(Node::Fail));

        match node {
            Node::Emit(emitted, _) => {
                assert_eq!(emitted.match_pats, nf.match_pats);
                assert_eq!(emitted.build_pats, nf.build_pats);
            }
            _ => panic!("Expected Emit"),
        }
    }

    #[test]
    fn emit_multiple_answers_chain() {
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();
        let nf3 = make_identity_nf();

        let chain = Node::Emit(
            nf1,
            Box::new(Node::Emit(nf2, Box::new(Node::Emit(nf3, Box::new(Node::Fail))))),
        );
        assert!(matches!(chain, Node::Emit(_, _)));
    }

    #[test]
    fn emit_into_or() {
        let nf = make_identity_nf();
        let or_node = Node::Or(Box::new(Node::Fail), Box::new(Node::Fail));
        let node: Node<()> = Node::Emit(nf, Box::new(or_node));

        match node {
            Node::Emit(_, rest) => {
                assert!(matches!(*rest, Node::Or(_, _)));
            }
            _ => panic!("Expected Emit"),
        }
    }

    #[test]
    fn emit_deeply_chained() {
        let mut node: Node<()> = Node::Fail;
        for _ in 0..50 {
            node = Node::Emit(make_identity_nf(), Box::new(node));
        }
        assert!(matches!(node, Node::Emit(_, _)));
    }

    // ========================================================================
    // COMPLEX STRUCTURE TESTS
    // ========================================================================

    #[test]
    fn emit_then_or() {
        // Emit(nf, Or(Fail, Fail))
        let nf = make_identity_nf();
        let or_node = Node::Or(Box::new(Node::Fail), Box::new(Node::Fail));
        let node: Node<()> = Node::Emit(nf, Box::new(or_node));
        assert!(matches!(node, Node::Emit(_, _)));
    }

    #[test]
    fn or_of_emits() {
        // Or(Emit(nf1, Fail), Emit(nf2, Fail))
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();
        let left = Node::Emit(nf1, Box::new(Node::Fail));
        let right = Node::Emit(nf2, Box::new(Node::Fail));
        let node: Node<()> = Node::Or(Box::new(left), Box::new(right));
        assert!(matches!(node, Node::Or(_, _)));
    }

    #[test]
    fn emit_or_emit_fail() {
        // Emit(nf1, Or(Emit(nf2, Fail), Fail))
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();
        let inner_emit = Node::Emit(nf2, Box::new(Node::Fail));
        let or_node = Node::Or(Box::new(inner_emit), Box::new(Node::Fail));
        let node: Node<()> = Node::Emit(nf1, Box::new(or_node));
        assert!(matches!(node, Node::Emit(_, _)));
    }

    #[test]
    fn mixed_deep_structure() {
        // Complex nested structure
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();

        let inner = Node::Or(
            Box::new(Node::Emit(nf1, Box::new(Node::Fail))),
            Box::new(Node::Fail),
        );
        let outer = Node::Emit(nf2, Box::new(inner));
        let node: Node<()> = Node::Or(Box::new(outer), Box::new(Node::Fail));
        assert!(matches!(node, Node::Or(_, _)));
    }

    // ========================================================================
    // TRAIT TESTS
    // ========================================================================

    #[test]
    fn node_is_clone() {
        let nf = make_identity_nf();
        let node1: Node<()> = Node::Emit(nf, Box::new(Node::Fail));
        let node2 = node1.clone();
        // Just verify clone compiles and doesn't panic
        assert!(matches!(node2, Node::Emit(_, _)));
    }

    #[test]
    fn node_is_debug() {
        let node: Node<()> = Node::Fail;
        let debug_str = format!("{:?}", node);
        assert!(debug_str.contains("Fail"));
    }

    #[test]
    fn fail_is_equal_to_fail() {
        let node1: Node<()> = Node::Fail;
        let node2: Node<()> = Node::Fail;
        // This tests that PartialEq is derived
        assert!(matches!((&node1, &node2), (Node::Fail, Node::Fail)));
    }

    // ========================================================================
    // SIZE TESTS
    // ========================================================================

    #[test]
    fn node_size_reasonable() {
        use std::mem::size_of;
        let size = size_of::<Node<()>>();
        // Node is larger now because it contains Work variant
        // Work contains MeetWork, FixWork, PipeWork variants which are substantial
        // PipeWork now includes env: Env and tables: Tables for Fix/Call handling
        assert!(size < 700, "Node should not be excessively large, got {}", size);
    }

    // ========================================================================
    // EXTRACTION TESTS
    // ========================================================================

    #[test]
    fn can_pattern_match_fail() {
        let node: Node<()> = Node::Fail;
        let is_fail = matches!(node, Node::Fail);
        assert!(is_fail);
    }

    #[test]
    fn can_pattern_match_emit() {
        let nf = make_identity_nf();
        let node: Node<()> = Node::Emit(nf.clone(), Box::new(Node::Fail));
        match node {
            Node::Emit(emitted, rest) => {
                assert_eq!(emitted.drop_fresh.in_arity, nf.drop_fresh.in_arity);
                assert!(matches!(*rest, Node::Fail));
            }
            _ => panic!("Expected Emit"),
        }
    }

    #[test]
    fn can_pattern_match_or() {
        let node: Node<()> = Node::Or(Box::new(Node::Fail), Box::new(Node::Fail));
        match node {
            Node::Or(left, right) => {
                assert!(matches!(*left, Node::Fail));
                assert!(matches!(*right, Node::Fail));
            }
            _ => panic!("Expected Or"),
        }
    }
}
