//! Rel IR - Relation expressions for the direction-agnostic evaluation model.
//!
//! Rel replaces the old Goal enum with a more principled representation
//! that supports structural dual operations.

use crate::constraint::ConstraintOps;
use crate::kernel::dual_nf;
use crate::nf::NF;
use crate::term::TermStore;
use std::sync::Arc;

/// Identifier for recursive relation bindings (Fix/Call).
pub type RelId = u32;

/// Relation expression - the IR for evaluation.
///
/// Each variant represents a different way to combine relations:
/// - `Zero`: empty relation (always fails)
/// - `Atom(nf)`: single span (atomic relation from NF)
/// - `Or(a, b)`: union/disjunction
/// - `And(a, b)`: intersection/conjunction
/// - `Seq(xs)`: n-ary sequential composition
/// - `Fix(id, body)`: recursive binding (μ binder)
/// - `Call(id)`: recursive reference
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Rel<C> {
    /// Empty relation - always fails.
    Zero,
    /// Atomic relation from a single NF span.
    Atom(Arc<NF<C>>),
    /// Union (disjunction) of two relations.
    Or(Arc<Rel<C>>, Arc<Rel<C>>),
    /// Intersection (conjunction) of two relations.
    And(Arc<Rel<C>>, Arc<Rel<C>>),
    /// Sequential composition of relations.
    Seq(Arc<[Arc<Rel<C>>]>),
    /// Recursive binding: Fix(id, body) binds `id` to be used in `body`.
    Fix(RelId, Arc<Rel<C>>),
    /// Recursive reference to a Fix-bound relation.
    Call(RelId),
}

/// Compute the structural dual of a relation.
///
/// The dual of a relation R is its converse relation R^(-1).
/// If R relates input to output, dual(R) relates output to input.
///
/// Properties:
/// - dual(dual(r)) == r (involution)
/// - dual(Zero) = Zero
/// - dual(Atom(nf)) = Atom(dual_nf(nf, terms))
/// - dual(Or(a,b)) = Or(dual(a), dual(b)) (no swap)
/// - dual(And(a,b)) = And(dual(a), dual(b)) (no swap)
/// - dual(Seq([x0..xn])) = Seq([dual(xn)..dual(x0)]) (REVERSE and dual)
/// - dual(Fix(id, body)) = Fix(id, dual(body))
/// - dual(Call(id)) = Call(id)
pub fn dual<C: ConstraintOps>(rel: &Rel<C>, terms: &TermStore) -> Rel<C> {
    match rel {
        Rel::Zero => Rel::Zero,

        Rel::Atom(nf) => Rel::Atom(Arc::new(dual_nf(nf, terms))),

        Rel::Or(a, b) => Rel::Or(Arc::new(dual(a, terms)), Arc::new(dual(b, terms))),

        Rel::And(a, b) => Rel::And(Arc::new(dual(a, terms)), Arc::new(dual(b, terms))),

        Rel::Seq(xs) => {
            // CRITICAL: Reverse the sequence AND dual each element
            let dualed: Vec<Arc<Rel<C>>> = xs
                .iter()
                .rev() // Reverse order
                .map(|x| Arc::new(dual(x, terms))) // Dual each element
                .collect();
            Rel::Seq(Arc::from(dualed))
        }

        Rel::Fix(id, body) => Rel::Fix(*id, Arc::new(dual(body, terms))),

        Rel::Call(id) => Rel::Call(*id),
    }
}

#[cfg(test)]
mod tests {
    use super::{Rel, RelId};
    use crate::constraint::ConstraintOps;
    use crate::drop_fresh::DropFresh;
    use crate::nf::NF;
    use crate::symbol::SymbolStore;
    use crate::term::TermStore;
    use crate::test_utils::{make_rule_nf, setup};
    use smallvec::SmallVec;
    use std::sync::Arc;

    fn dual<C: ConstraintOps>(rel: &Rel<C>, terms: &TermStore) -> Rel<C> {
        super::dual(rel, terms)
    }

    /// Create an NF with variables: F(x) -> G(x)
    fn make_var_nf(symbols: &SymbolStore, terms: &TermStore) -> NF<()> {
        let f = symbols.intern("F");
        let g = symbols.intern("G");
        let v0 = terms.var(0);
        let f_x = terms.app1(f, v0);
        let g_x = terms.app1(g, v0);
        NF::new(
            SmallVec::from_slice(&[f_x]),
            DropFresh::identity(1),
            SmallVec::from_slice(&[g_x]),
        )
    }

    /// Create distinguishable Rels for testing order
    fn make_labeled_atom(label: &str, symbols: &SymbolStore, terms: &TermStore) -> Rel<()> {
        let sym = symbols.intern(label);
        let t = terms.app0(sym);
        let nf = NF::new(
            SmallVec::from_slice(&[t]),
            DropFresh::identity(0),
            SmallVec::from_slice(&[t]),
        );
        Rel::Atom(Arc::new(nf))
    }

    /// Helper to check if two Rels are structurally equal (for testing)
    fn structurally_equal<C: Clone + PartialEq>(a: &Rel<C>, b: &Rel<C>) -> bool {
        match (a, b) {
            (Rel::Zero, Rel::Zero) => true,
            (Rel::Atom(nf1), Rel::Atom(nf2)) => {
                nf1.match_pats == nf2.match_pats
                    && nf1.build_pats == nf2.build_pats
                    && nf1.drop_fresh.in_arity == nf2.drop_fresh.in_arity
                    && nf1.drop_fresh.out_arity == nf2.drop_fresh.out_arity
                    && nf1.drop_fresh.map == nf2.drop_fresh.map
            }
            (Rel::Or(a1, b1), Rel::Or(a2, b2)) => {
                structurally_equal(a1, a2) && structurally_equal(b1, b2)
            }
            (Rel::And(a1, b1), Rel::And(a2, b2)) => {
                structurally_equal(a1, a2) && structurally_equal(b1, b2)
            }
            (Rel::Seq(xs1), Rel::Seq(xs2)) => {
                xs1.len() == xs2.len()
                    && xs1
                        .iter()
                        .zip(xs2.iter())
                        .all(|(x1, x2)| structurally_equal(x1, x2))
            }
            (Rel::Fix(id1, body1), Rel::Fix(id2, body2)) => {
                id1 == id2 && structurally_equal(body1, body2)
            }
            (Rel::Call(id1), Rel::Call(id2)) => id1 == id2,
            _ => false,
        }
    }

    // ========================================================================
    // ZERO TESTS
    // ========================================================================

    #[test]
    fn dual_zero_is_zero() {
        let r: Rel<()> = Rel::Zero;
        let terms = TermStore::new();
        let d = dual(&r, &terms);
        assert!(matches!(d, Rel::Zero));
    }

    #[test]
    fn dual_dual_zero_equals_zero() {
        let r: Rel<()> = Rel::Zero;
        let terms = TermStore::new();
        let d1 = dual(&r, &terms);
        let d2 = dual(&d1, &terms);
        assert!(matches!(d2, Rel::Zero));
    }

    // ========================================================================
    // ATOM TESTS
    // ========================================================================

    #[test]
    fn dual_atom_duals_inner_nf() {
        let (symbols, terms) = setup();
        let nf = make_rule_nf("A", "B", &symbols, &terms);
        let r = Rel::Atom(Arc::new(nf.clone()));
        let d = dual(&r, &terms);

        match d {
            Rel::Atom(dualed_nf) => {
                // The dual NF should have swapped patterns
                // Original: A -> B, Dual: B -> A
                assert_eq!(dualed_nf.match_pats, nf.build_pats);
                assert_eq!(dualed_nf.build_pats, nf.match_pats);
            }
            _ => panic!("Expected Atom variant"),
        }
    }

    #[test]
    fn dual_atom_with_vars_duals_correctly() {
        let (symbols, terms) = setup();
        let nf = make_var_nf(&symbols, &terms);
        let r = Rel::Atom(Arc::new(nf.clone()));
        let d = dual(&r, &terms);

        match d {
            Rel::Atom(dualed_nf) => {
                // F(x) -> G(x) becomes G(x) -> F(x)
                assert_eq!(dualed_nf.match_pats, nf.build_pats);
                assert_eq!(dualed_nf.build_pats, nf.match_pats);
                // DropFresh should also be dualized
                assert_eq!(dualed_nf.drop_fresh.in_arity, nf.drop_fresh.out_arity);
                assert_eq!(dualed_nf.drop_fresh.out_arity, nf.drop_fresh.in_arity);
            }
            _ => panic!("Expected Atom variant"),
        }
    }

    #[test]
    fn dual_dual_atom_equals_original() {
        let (symbols, terms) = setup();
        let nf = make_var_nf(&symbols, &terms);
        let r = Rel::Atom(Arc::new(nf.clone()));
        let d1 = dual(&r, &terms);
        let d2 = dual(&d1, &terms);

        assert!(
            structurally_equal(&r, &d2),
            "dual(dual(atom)) should equal atom"
        );
    }

    // ========================================================================
    // OR TESTS
    // ========================================================================

    #[test]
    fn dual_or_preserves_structure() {
        let a: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let b: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let r = Rel::Or(a, b);
        let terms = TermStore::new();
        let d = dual(&r, &terms);
        assert!(matches!(d, Rel::Or(_, _)));
    }

    #[test]
    fn dual_or_duals_both_children() {
        let (symbols, terms) = setup();
        let nf_a = make_rule_nf("A", "B", &symbols, &terms);
        let nf_b = make_var_nf(&symbols, &terms);

        let a = Arc::new(Rel::Atom(Arc::new(nf_a)));
        let b = Arc::new(Rel::Atom(Arc::new(nf_b)));
        let r = Rel::Or(a, b);
        let d = dual(&r, &terms);

        match d {
            Rel::Or(da, db) => {
                // Both children should be Atoms with dualed NFs
                assert!(matches!(da.as_ref(), Rel::Atom(_)));
                assert!(matches!(db.as_ref(), Rel::Atom(_)));
            }
            _ => panic!("Expected Or variant"),
        }
    }

    #[test]
    fn dual_or_does_not_swap_children() {
        let (symbols, terms) = setup();
        let a = Arc::new(make_labeled_atom("Left", &symbols, &terms));
        let b = Arc::new(make_labeled_atom("Right", &symbols, &terms));
        let r = Rel::Or(a, b);
        let d = dual(&r, &terms);

        match d {
            Rel::Or(da, db) => {
                // Left should still be on left after dual
                // (Or does NOT swap, unlike Seq which reverses)
                let expected_left = make_labeled_atom("Left", &symbols, &terms);
                let expected_right = make_labeled_atom("Right", &symbols, &terms);
                let dual_left = dual(da.as_ref(), &terms);
                let dual_right = dual(db.as_ref(), &terms);
                assert!(
                    structurally_equal(&dual_left, &expected_left),
                    "Left child should remain left"
                );
                assert!(
                    structurally_equal(&dual_right, &expected_right),
                    "Right child should remain right"
                );
            }
            _ => panic!("Expected Or variant"),
        }
    }

    #[test]
    fn dual_dual_or_equals_original() {
        let a: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let b: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let r = Rel::Or(a, b);
        let terms = TermStore::new();
        let d1 = dual(&r, &terms);
        let d2 = dual(&d1, &terms);
        assert!(structurally_equal(&r, &d2));
    }

    // ========================================================================
    // AND TESTS
    // ========================================================================

    #[test]
    fn dual_and_preserves_structure() {
        let a: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let b: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let r = Rel::And(a, b);
        let terms = TermStore::new();
        let d = dual(&r, &terms);
        assert!(matches!(d, Rel::And(_, _)));
    }

    #[test]
    fn dual_and_duals_both_children() {
        let (symbols, terms) = setup();
        let nf_a = make_rule_nf("A", "B", &symbols, &terms);
        let nf_b = make_var_nf(&symbols, &terms);

        let a = Arc::new(Rel::Atom(Arc::new(nf_a)));
        let b = Arc::new(Rel::Atom(Arc::new(nf_b)));
        let r = Rel::And(a, b);
        let d = dual(&r, &terms);

        match d {
            Rel::And(da, db) => {
                assert!(matches!(da.as_ref(), Rel::Atom(_)));
                assert!(matches!(db.as_ref(), Rel::Atom(_)));
            }
            _ => panic!("Expected And variant"),
        }
    }

    #[test]
    fn dual_and_does_not_swap_children() {
        let (symbols, terms) = setup();
        let a = Arc::new(make_labeled_atom("First", &symbols, &terms));
        let b = Arc::new(make_labeled_atom("Second", &symbols, &terms));
        let r = Rel::And(a, b);
        let d = dual(&r, &terms);

        match d {
            Rel::And(da, db) => {
                let expected_first = make_labeled_atom("First", &symbols, &terms);
                let expected_second = make_labeled_atom("Second", &symbols, &terms);
                let dual_first = dual(da.as_ref(), &terms);
                let dual_second = dual(db.as_ref(), &terms);
                assert!(
                    structurally_equal(&dual_first, &expected_first),
                    "First child should remain first"
                );
                assert!(
                    structurally_equal(&dual_second, &expected_second),
                    "Second child should remain second"
                );
            }
            _ => panic!("Expected And variant"),
        }
    }

    #[test]
    fn dual_dual_and_equals_original() {
        let a: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let b: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let r = Rel::And(a, b);
        let terms = TermStore::new();
        let d1 = dual(&r, &terms);
        let d2 = dual(&d1, &terms);
        assert!(structurally_equal(&r, &d2));
    }

    // ========================================================================
    // SEQ TESTS - CRITICAL: MUST REVERSE ORDER
    // ========================================================================

    #[test]
    fn dual_seq_empty() {
        let r: Rel<()> = Rel::Seq(Arc::from(Vec::<Arc<Rel<()>>>::new()));
        let terms = TermStore::new();
        let d = dual(&r, &terms);
        match d {
            Rel::Seq(xs) => assert!(xs.is_empty(), "Empty Seq should remain empty"),
            _ => panic!("Expected Seq variant"),
        }
    }

    #[test]
    fn dual_seq_single_element() {
        let x: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let r = Rel::Seq(Arc::from(vec![x]));
        let terms = TermStore::new();
        let d = dual(&r, &terms);
        match d {
            Rel::Seq(xs) => {
                assert_eq!(xs.len(), 1);
                assert!(matches!(xs[0].as_ref(), Rel::Zero));
            }
            _ => panic!("Expected Seq variant"),
        }
    }

    #[test]
    fn dual_seq_two_elements_reverses() {
        let (symbols, terms) = setup();
        let a = Arc::new(make_labeled_atom("A", &symbols, &terms));
        let b = Arc::new(make_labeled_atom("B", &symbols, &terms));
        let r = Rel::Seq(Arc::from(vec![a.clone(), b.clone()]));
        let d = dual(&r, &terms);

        match d {
            Rel::Seq(xs) => {
                assert_eq!(xs.len(), 2);
                // Order should be reversed: [dual(B), dual(A)]
                // After double-dual: [B, A]
                let dual_first = dual(xs[0].as_ref(), &terms);
                let dual_second = dual(xs[1].as_ref(), &terms);

                // The original was [A, B], dual should be [dual(B), dual(A)]
                // So dual(xs[0]) should equal B, dual(xs[1]) should equal A
                assert!(
                    structurally_equal(&dual_first, b.as_ref()),
                    "First element after dual should be dual(B)"
                );
                assert!(
                    structurally_equal(&dual_second, a.as_ref()),
                    "Second element after dual should be dual(A)"
                );
            }
            _ => panic!("Expected Seq variant"),
        }
    }

    #[test]
    fn dual_seq_three_elements_reverses() {
        let (symbols, terms) = setup();
        let a = Arc::new(make_labeled_atom("A", &symbols, &terms));
        let b = Arc::new(make_labeled_atom("B", &symbols, &terms));
        let c = Arc::new(make_labeled_atom("C", &symbols, &terms));
        let r = Rel::Seq(Arc::from(vec![a.clone(), b.clone(), c.clone()]));
        let d = dual(&r, &terms);

        match d {
            Rel::Seq(xs) => {
                assert_eq!(xs.len(), 3);
                // Original: [A, B, C]
                // Dual: [dual(C), dual(B), dual(A)]
                let dual_0 = dual(xs[0].as_ref(), &terms);
                let dual_1 = dual(xs[1].as_ref(), &terms);
                let dual_2 = dual(xs[2].as_ref(), &terms);

                assert!(structurally_equal(&dual_0, c.as_ref()));
                assert!(structurally_equal(&dual_1, b.as_ref()));
                assert!(structurally_equal(&dual_2, a.as_ref()));
            }
            _ => panic!("Expected Seq variant"),
        }
    }

    #[test]
    fn dual_seq_many_elements_reverses_all() {
        let elements: Vec<Arc<Rel<()>>> = (0..10).map(|_| Arc::new(Rel::Zero)).collect();
        let r = Rel::Seq(Arc::from(elements.clone()));
        let terms = TermStore::new();
        let d = dual(&r, &terms);

        match d {
            Rel::Seq(xs) => {
                assert_eq!(xs.len(), 10);
                // All should still be Zero (self-dual)
                for x in xs.iter() {
                    assert!(matches!(x.as_ref(), Rel::Zero));
                }
            }
            _ => panic!("Expected Seq variant"),
        }
    }

    #[test]
    fn dual_seq_nested_reverses_outer_and_duals_inner() {
        let (symbols, terms) = setup();
        let a = Arc::new(make_labeled_atom("A", &symbols, &terms));
        let b = Arc::new(make_labeled_atom("B", &symbols, &terms));
        let c = Arc::new(make_labeled_atom("C", &symbols, &terms));

        // Seq([Seq([A, B]), C])
        let inner = Arc::new(Rel::Seq(Arc::from(vec![a.clone(), b.clone()])));
        let r = Rel::Seq(Arc::from(vec![inner, c.clone()]));
        let d = dual(&r, &terms);

        match d {
            Rel::Seq(xs) => {
                assert_eq!(xs.len(), 2);
                // Outer reversed: [dual(C), dual(Seq([A,B]))]
                // dual(Seq([A,B])) = Seq([dual(B), dual(A)])
                let dual_0 = dual(xs[0].as_ref(), &terms);
                assert!(
                    structurally_equal(&dual_0, c.as_ref()),
                    "First should be dual(C)"
                );

                match xs[1].as_ref() {
                    Rel::Seq(inner_xs) => {
                        assert_eq!(inner_xs.len(), 2);
                        // Inner also reversed: [dual(B), dual(A)]
                        let inner_0 = dual(inner_xs[0].as_ref(), &terms);
                        let inner_1 = dual(inner_xs[1].as_ref(), &terms);
                        assert!(structurally_equal(&inner_0, b.as_ref()));
                        assert!(structurally_equal(&inner_1, a.as_ref()));
                    }
                    _ => panic!("Expected inner Seq"),
                }
            }
            _ => panic!("Expected Seq variant"),
        }
    }

    #[test]
    fn dual_dual_seq_equals_original() {
        let (symbols, terms) = setup();
        let a = Arc::new(make_labeled_atom("A", &symbols, &terms));
        let b = Arc::new(make_labeled_atom("B", &symbols, &terms));
        let c = Arc::new(make_labeled_atom("C", &symbols, &terms));
        let r = Rel::Seq(Arc::from(vec![a, b, c]));
        let d1 = dual(&r, &terms);
        let d2 = dual(&d1, &terms);
        assert!(
            structurally_equal(&r, &d2),
            "dual(dual(seq)) should equal seq"
        );
    }

    #[test]
    fn dual_dual_seq_empty_equals_original() {
        let r: Rel<()> = Rel::Seq(Arc::from(Vec::<Arc<Rel<()>>>::new()));
        let terms = TermStore::new();
        let d1 = dual(&r, &terms);
        let d2 = dual(&d1, &terms);
        assert!(structurally_equal(&r, &d2));
    }

    // ========================================================================
    // FIX TESTS
    // ========================================================================

    #[test]
    fn dual_fix_preserves_id() {
        let body: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let r = Rel::Fix(42, body);
        let terms = TermStore::new();
        let d = dual(&r, &terms);

        match d {
            Rel::Fix(id, _) => assert_eq!(id, 42, "Fix ID should be preserved"),
            _ => panic!("Expected Fix variant"),
        }
    }

    #[test]
    fn dual_fix_duals_body() {
        let (symbols, terms) = setup();
        let nf = make_rule_nf("A", "B", &symbols, &terms);
        let body = Arc::new(Rel::Atom(Arc::new(nf)));
        let r = Rel::Fix(7, body);
        let d = dual(&r, &terms);

        match d {
            Rel::Fix(id, dualed_body) => {
                assert_eq!(id, 7);
                assert!(matches!(dualed_body.as_ref(), Rel::Atom(_)));
            }
            _ => panic!("Expected Fix variant"),
        }
    }

    #[test]
    fn dual_fix_with_call_in_body() {
        // Fix(0, Or(base, Seq([Call(0), step])))
        let base: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let step: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let call = Arc::new(Rel::Call(0));
        let seq = Arc::new(Rel::Seq(Arc::from(vec![call, step])));
        let or = Arc::new(Rel::Or(base, seq));
        let r = Rel::Fix(0, or);
        let terms = TermStore::new();
        let d = dual(&r, &terms);

        match d {
            Rel::Fix(id, body) => {
                assert_eq!(id, 0);
                // Body should be Or(dual(base), dual(Seq([Call(0), step])))
                // = Or(Zero, Seq([dual(step), dual(Call(0))]))
                // = Or(Zero, Seq([Zero, Call(0)]))
                match body.as_ref() {
                    Rel::Or(_, seq_part) => {
                        match seq_part.as_ref() {
                            Rel::Seq(xs) => {
                                assert_eq!(xs.len(), 2);
                                // Order reversed: [dual(step), Call(0)]
                                assert!(matches!(xs[0].as_ref(), Rel::Zero));
                                assert!(matches!(xs[1].as_ref(), Rel::Call(0)));
                            }
                            _ => panic!("Expected Seq in Or"),
                        }
                    }
                    _ => panic!("Expected Or in Fix body"),
                }
            }
            _ => panic!("Expected Fix variant"),
        }
    }

    #[test]
    fn dual_nested_fix_different_ids() {
        // Fix(0, Fix(1, Seq([Call(0), Call(1)])))
        let call0: Arc<Rel<()>> = Arc::new(Rel::Call(0));
        let call1: Arc<Rel<()>> = Arc::new(Rel::Call(1));
        let seq = Arc::new(Rel::Seq(Arc::from(vec![call0, call1])));
        let inner_fix = Arc::new(Rel::Fix(1, seq));
        let r = Rel::Fix(0, inner_fix);
        let terms = TermStore::new();
        let d = dual(&r, &terms);

        match d {
            Rel::Fix(id0, body0) => {
                assert_eq!(id0, 0);
                match body0.as_ref() {
                    Rel::Fix(id1, body1) => {
                        assert_eq!(*id1, 1);
                        match body1.as_ref() {
                            Rel::Seq(xs) => {
                                // Original: [Call(0), Call(1)]
                                // Dual: [dual(Call(1)), dual(Call(0))] = [Call(1), Call(0)]
                                assert_eq!(xs.len(), 2);
                                assert!(matches!(xs[0].as_ref(), Rel::Call(1)));
                                assert!(matches!(xs[1].as_ref(), Rel::Call(0)));
                            }
                            _ => panic!("Expected Seq"),
                        }
                    }
                    _ => panic!("Expected inner Fix"),
                }
            }
            _ => panic!("Expected outer Fix"),
        }
    }

    #[test]
    fn dual_dual_fix_equals_original() {
        let body: Arc<Rel<()>> = Arc::new(Rel::Call(99));
        let r = Rel::Fix(99, body);
        let terms = TermStore::new();
        let d1 = dual(&r, &terms);
        let d2 = dual(&d1, &terms);
        assert!(structurally_equal(&r, &d2));
    }

    // ========================================================================
    // CALL TESTS
    // ========================================================================

    #[test]
    fn dual_call_unchanged() {
        let r: Rel<()> = Rel::Call(42);
        let terms = TermStore::new();
        let d = dual(&r, &terms);
        assert!(matches!(d, Rel::Call(42)));
    }

    #[test]
    fn dual_call_zero_id() {
        let r: Rel<()> = Rel::Call(0);
        let terms = TermStore::new();
        let d = dual(&r, &terms);
        assert!(matches!(d, Rel::Call(0)));
    }

    #[test]
    fn dual_call_max_id() {
        let r: Rel<()> = Rel::Call(RelId::MAX);
        let terms = TermStore::new();
        let d = dual(&r, &terms);
        assert!(matches!(d, Rel::Call(id) if id == RelId::MAX));
    }

    #[test]
    fn dual_dual_call_equals_original() {
        let r: Rel<()> = Rel::Call(123);
        let terms = TermStore::new();
        let d1 = dual(&r, &terms);
        let d2 = dual(&d1, &terms);
        assert!(structurally_equal(&r, &d2));
    }

    // ========================================================================
    // INVOLUTION TESTS (COMPREHENSIVE)
    // ========================================================================

    #[test]
    fn dual_is_involution_complex_tree() {
        let (symbols, terms) = setup();
        let a = Arc::new(make_labeled_atom("A", &symbols, &terms));
        let b = Arc::new(make_labeled_atom("B", &symbols, &terms));
        let c = Arc::new(make_labeled_atom("C", &symbols, &terms));

        // Complex: Or(And(A, B), Seq([C, Fix(0, Call(0))]))
        let and_part = Arc::new(Rel::And(a.clone(), b.clone()));
        let call = Arc::new(Rel::Call(0));
        let fix = Arc::new(Rel::Fix(0, call));
        let seq_part = Arc::new(Rel::Seq(Arc::from(vec![c.clone(), fix])));
        let r = Rel::Or(and_part, seq_part);

        let d1 = dual(&r, &terms);
        let d2 = dual(&d1, &terms);

        assert!(
            structurally_equal(&r, &d2),
            "dual(dual(complex)) should equal complex"
        );
    }

    #[test]
    fn dual_is_involution_all_variants() {
        let (symbols, terms) = setup();

        // Test each variant in isolation
        let cases: Vec<Rel<()>> = vec![
            Rel::Zero,
            Rel::Atom(Arc::new(make_rule_nf("A", "B", &symbols, &terms))),
            Rel::Or(Arc::new(Rel::Zero), Arc::new(Rel::Zero)),
            Rel::And(Arc::new(Rel::Zero), Arc::new(Rel::Zero)),
            Rel::Seq(Arc::from(vec![Arc::new(Rel::Zero), Arc::new(Rel::Zero)])),
            Rel::Fix(0, Arc::new(Rel::Zero)),
            Rel::Call(0),
        ];

        for r in cases {
            let d1 = dual(&r, &terms);
            let d2 = dual(&d1, &terms);
            assert!(structurally_equal(&r, &d2), "Involution failed for variant");
        }
    }

    // ========================================================================
    // EDGE CASES - ARC SHARING
    // ========================================================================

    #[test]
    fn dual_with_shared_arc_both_or_children() {
        let shared: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let r = Rel::Or(Arc::clone(&shared), Arc::clone(&shared));
        let terms = TermStore::new();
        let d = dual(&r, &terms);
        // Should not panic, result should be valid
        assert!(matches!(d, Rel::Or(_, _)));
    }

    #[test]
    fn dual_with_shared_arc_in_seq() {
        let shared: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let r = Rel::Seq(Arc::from(vec![
            Arc::clone(&shared),
            Arc::clone(&shared),
            Arc::clone(&shared),
        ]));
        let terms = TermStore::new();
        let d = dual(&r, &terms);
        match d {
            Rel::Seq(xs) => assert_eq!(xs.len(), 3),
            _ => panic!("Expected Seq"),
        }
    }

    // ========================================================================
    // EDGE CASES - DEEP NESTING
    // ========================================================================

    #[test]
    fn dual_deep_or_nesting() {
        let mut r: Rel<()> = Rel::Zero;
        for _ in 0..100 {
            r = Rel::Or(Arc::new(r), Arc::new(Rel::Zero));
        }
        let terms = TermStore::new();
        let d = dual(&r, &terms);
        // Should complete without stack overflow
        assert!(matches!(d, Rel::Or(_, _)));
    }

    #[test]
    fn dual_deep_seq_nesting() {
        let mut r: Rel<()> = Rel::Zero;
        for _ in 0..100 {
            r = Rel::Seq(Arc::from(vec![Arc::new(r), Arc::new(Rel::Zero)]));
        }
        let terms = TermStore::new();
        let d = dual(&r, &terms);
        assert!(matches!(d, Rel::Seq(_)));
    }

    #[test]
    fn dual_deep_fix_nesting() {
        let mut r: Rel<()> = Rel::Zero;
        for i in 0..50 {
            r = Rel::Fix(i, Arc::new(r));
        }
        let terms = TermStore::new();
        let d = dual(&r, &terms);
        assert!(matches!(d, Rel::Fix(49, _)));
    }

    #[test]
    fn dual_wide_seq() {
        let elements: Vec<Arc<Rel<()>>> = (0..1000).map(|_| Arc::new(Rel::Zero)).collect();
        let r = Rel::Seq(Arc::from(elements));
        let terms = TermStore::new();
        let d = dual(&r, &terms);
        match d {
            Rel::Seq(xs) => assert_eq!(xs.len(), 1000),
            _ => panic!("Expected Seq"),
        }
    }

    // ========================================================================
    // CONSTRUCTION TESTS
    // ========================================================================

    #[test]
    fn rel_zero_is_zero_sized() {
        // Zero variant should have no data
        let r: Rel<()> = Rel::Zero;
        assert!(matches!(r, Rel::Zero));
    }

    #[test]
    fn rel_atom_holds_nf() {
        let (symbols, terms) = setup();
        let nf = make_rule_nf("A", "B", &symbols, &terms);
        let r = Rel::Atom(Arc::new(nf));
        assert!(matches!(r, Rel::Atom(_)));
    }

    #[test]
    fn rel_or_holds_two_children() {
        let a: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let b: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let r = Rel::Or(a, b);
        assert!(matches!(r, Rel::Or(_, _)));
    }

    #[test]
    fn rel_and_holds_two_children() {
        let a: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let b: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let r = Rel::And(a, b);
        assert!(matches!(r, Rel::And(_, _)));
    }

    #[test]
    fn rel_seq_holds_slice() {
        let elements: Vec<Arc<Rel<()>>> = vec![Arc::new(Rel::Zero), Arc::new(Rel::Zero)];
        let r = Rel::Seq(Arc::from(elements));
        assert!(matches!(r, Rel::Seq(_)));
    }

    #[test]
    fn rel_fix_holds_id_and_body() {
        let body: Arc<Rel<()>> = Arc::new(Rel::Zero);
        let r = Rel::Fix(42, body);
        assert!(matches!(r, Rel::Fix(42, _)));
    }

    #[test]
    fn rel_call_holds_id() {
        let r: Rel<()> = Rel::Call(123);
        assert!(matches!(r, Rel::Call(123)));
    }
}
