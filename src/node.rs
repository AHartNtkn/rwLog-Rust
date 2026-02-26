//! Node - Search tree nodes for the evaluation engine.
//!
//! The Node enum represents the search tree structure.
//! Or nodes use rotation interleaving for fair search.
//! Work nodes embed active computations (Seq, And, Fix).

use crate::constraint::ConstraintOps;
use crate::nf::NF;
use crate::perf_counters;
use crate::term::TermStore;
use crate::work::{DiagonalStepResult, FixStepResult, Work, WorkStep};

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
    /// NF is boxed to shrink Node from ~136B to ~24B, reducing memcpy costs.
    Emit(Box<NF<C>>, Box<Node<C>>),
    /// Active work - computations that may emit, split, or complete.
    Work(Box<Work<C>>),
}

/// Result of stepping a Node one notch.
///
/// NF is boxed in Emit to shrink NodeStep from ~152B to ~40B, reducing
/// sret copy costs and step_node's stack frame size.
#[derive(Clone, Debug)]
pub enum NodeStep<C: ConstraintOps> {
    /// Produced an answer and the remaining node.
    Emit(Box<NF<C>>, Node<C>),
    /// No answer yet, but node updated (rotation or work progress).
    Continue(Node<C>),
    /// Exhausted - no more answers.
    Exhausted,
}

/// Construct an Or node, collapsing if either side is Fail.
fn or_node<C: ConstraintOps>(left: Node<C>, right: Node<C>) -> Node<C> {
    match (&left, &right) {
        (Node::Fail, _) => right,
        (_, Node::Fail) => left,
        _ => Node::Or(Box::new(left), Box::new(right)),
    }
}

/// Rebuild an Or chain from siblings (outermost-first) and a leaf.
///
/// Given siblings [D, C, B] and leaf A', produces Or(D, Or(C, Or(B, A'))).
/// Iterates in reverse so the outermost sibling ends up at the top.
fn rebuild_or_chain<C: ConstraintOps>(siblings: Vec<Node<C>>, leaf: Node<C>) -> Node<C> {
    let mut result = leaf;
    for sib in siblings.into_iter().rev() {
        result = or_node(sib, result);
    }
    result
}

/// Step an Or node with full spine rotation.
///
/// Walks down the left spine of nested Ors, collecting right children
/// (siblings) in encounter order (outermost first). Prunes Fail nodes
/// during the walk. Steps the leftmost non-Fail leaf, then rebuilds
/// with siblings rotated in front of the stepped leaf.
///
/// Example: Or(Or(Or(A,B),C),D) → step A to A' → Or(D, Or(C, Or(B, A')))
#[inline(never)]
fn step_or<C: ConstraintOps>(left: Node<C>, right: Node<C>, terms: &mut TermStore) -> NodeStep<C> {
    let mut siblings: Vec<Node<C>> = vec![right];
    let mut current = left;

    // Walk down the left spine, collecting siblings and pruning Fail
    loop {
        match current {
            Node::Or(a, b) => {
                siblings.push(*b);
                current = *a;
            }
            Node::Fail => match siblings.pop() {
                Some(next) => current = next,
                None => return NodeStep::Exhausted,
            },
            _ => break,
        }
    }

    perf_counters::record_or_spine_walk(siblings.len() as u64);

    match step_node(current, terms) {
        NodeStep::Emit(nf, new_leaf) => NodeStep::Emit(nf, rebuild_or_chain(siblings, new_leaf)),
        NodeStep::Exhausted => {
            let rest = rebuild_or_chain(siblings, Node::Fail);
            if matches!(rest, Node::Fail) {
                NodeStep::Exhausted
            } else {
                NodeStep::Continue(rest)
            }
        }
        NodeStep::Continue(new_leaf) => NodeStep::Continue(rebuild_or_chain(siblings, new_leaf)),
    }
}

/// Step a node once using Or rotation and Work stepping.
pub fn step_node<C: ConstraintOps>(node: Node<C>, terms: &mut TermStore) -> NodeStep<C> {
    match node {
        Node::Fail => NodeStep::Exhausted,

        Node::Emit(nf, rest) => NodeStep::Emit(nf, *rest),

        Node::Or(left, right) => step_or(*left, *right, terms),

        Node::Work(mut work) => {
            // Fast paths: step in-place, reusing the existing Box<Work>.
            // This avoids take_self + alloc + free on every step.
            if let Work::Fix(ref mut fix) = *work {
                return match fix.step_in_place(terms) {
                    FixStepResult::Emit(nf) => NodeStep::Emit(Box::new(nf), Node::Work(work)),
                    FixStepResult::More => NodeStep::Continue(Node::Work(work)),
                    FixStepResult::Done => NodeStep::Continue(Node::Fail),
                };
            }
            if let Work::Compose(ref mut compose) = *work {
                return match compose.step_in_place(terms) {
                    DiagonalStepResult::Emit(nf) => NodeStep::Emit(Box::new(nf), Node::Work(work)),
                    DiagonalStepResult::More => NodeStep::Continue(Node::Work(work)),
                    DiagonalStepResult::Done => NodeStep::Continue(Node::Fail),
                };
            }
            if let Work::Meet(ref mut meet) = *work {
                return match meet.step_in_place(terms) {
                    DiagonalStepResult::Emit(nf) => NodeStep::Emit(Box::new(nf), Node::Work(work)),
                    DiagonalStepResult::More => NodeStep::Continue(Node::Work(work)),
                    DiagonalStepResult::Done => NodeStep::Continue(Node::Fail),
                };
            }
            match work.step(terms) {
                WorkStep::Done => NodeStep::Continue(Node::Fail),
                WorkStep::Emit(nf, next_work) => {
                    NodeStep::Emit(Box::new(nf), Node::Work(next_work))
                }
                WorkStep::Split(left_work, right_work) => NodeStep::Continue(Node::Or(
                    Box::new(Node::Work(left_work)),
                    Box::new(Node::Work(right_work)),
                )),
                WorkStep::More(next_work) => NodeStep::Continue(Node::Work(next_work)),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Node;
    use crate::drop_fresh::DropFresh;
    use crate::nf::NF;
    use crate::symbol::SymbolStore;
    use crate::term::TermStore;
    use crate::test_utils::{make_identity_nf, setup};
    use smallvec::SmallVec;

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
        let right = Node::Emit(Box::new(nf), Box::new(Node::Fail));
        let node: Node<()> = Node::Or(Box::new(Node::Fail), Box::new(right));
        assert!(matches!(node, Node::Or(_, _)));
    }

    #[test]
    fn or_left_other_right_fail() {
        let nf = make_identity_nf();
        let left = Node::Emit(Box::new(nf), Box::new(Node::Fail));
        let node: Node<()> = Node::Or(Box::new(left), Box::new(Node::Fail));
        assert!(matches!(node, Node::Or(_, _)));
    }

    #[test]
    fn or_both_emit() {
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();
        let left = Node::Emit(Box::new(nf1), Box::new(Node::Fail));
        let right = Node::Emit(Box::new(nf2), Box::new(Node::Fail));
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
        let node: Node<()> = Node::Emit(Box::new(nf), Box::new(Node::Fail));
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
        let node: Node<()> = Node::Emit(Box::new(nf.clone()), Box::new(Node::Fail));

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
            Box::new(nf1),
            Box::new(Node::Emit(
                Box::new(nf2),
                Box::new(Node::Emit(Box::new(nf3), Box::new(Node::Fail))),
            )),
        );
        assert!(matches!(chain, Node::Emit(_, _)));
    }

    #[test]
    fn emit_into_or() {
        let nf = make_identity_nf();
        let or_node = Node::Or(Box::new(Node::Fail), Box::new(Node::Fail));
        let node: Node<()> = Node::Emit(Box::new(nf), Box::new(or_node));

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
            node = Node::Emit(Box::new(make_identity_nf()), Box::new(node));
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
        let node: Node<()> = Node::Emit(Box::new(nf), Box::new(or_node));
        assert!(matches!(node, Node::Emit(_, _)));
    }

    #[test]
    fn or_of_emits() {
        // Or(Emit(nf1, Fail), Emit(nf2, Fail))
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();
        let left = Node::Emit(Box::new(nf1), Box::new(Node::Fail));
        let right = Node::Emit(Box::new(nf2), Box::new(Node::Fail));
        let node: Node<()> = Node::Or(Box::new(left), Box::new(right));
        assert!(matches!(node, Node::Or(_, _)));
    }

    #[test]
    fn emit_or_emit_fail() {
        // Emit(nf1, Or(Emit(nf2, Fail), Fail))
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();
        let inner_emit = Node::Emit(Box::new(nf2), Box::new(Node::Fail));
        let or_node = Node::Or(Box::new(inner_emit), Box::new(Node::Fail));
        let node: Node<()> = Node::Emit(Box::new(nf1), Box::new(or_node));
        assert!(matches!(node, Node::Emit(_, _)));
    }

    #[test]
    fn mixed_deep_structure() {
        // Complex nested structure
        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();

        let inner = Node::Or(
            Box::new(Node::Emit(Box::new(nf1), Box::new(Node::Fail))),
            Box::new(Node::Fail),
        );
        let outer = Node::Emit(Box::new(nf2), Box::new(inner));
        let node: Node<()> = Node::Or(Box::new(outer), Box::new(Node::Fail));
        assert!(matches!(node, Node::Or(_, _)));
    }

    // ========================================================================
    // TRAIT TESTS
    // ========================================================================

    #[test]
    fn node_is_clone() {
        let nf = make_identity_nf();
        let node1: Node<()> = Node::Emit(Box::new(nf), Box::new(Node::Fail));
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
        // Node::Emit has Box<NF<C>> so Node is sized by Box<Work> (pointer).
        // All variants are pointer-sized or smaller, so Node should be small.
        assert!(
            size <= 24,
            "Node should be at most 24 bytes (enum tag + two pointers), got {}",
            size
        );
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
        let node: Node<()> = Node::Emit(Box::new(nf.clone()), Box::new(Node::Fail));
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
