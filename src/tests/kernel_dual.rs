//! Tests for kernel/dual.rs - dual_nf operation.
//!
//! The new dual_nf is trivial: it swaps match_boundary and build_boundary.
//! These tests verify the semantic properties of duality.

use crate::kernel::{compose_nf, dual_nf};
use crate::nf::NF;
use crate::test_utils::setup;
use smallvec::SmallVec;

// ========================================================================
// BASIC PROPERTIES
// ========================================================================

#[test]
fn dual_nf_empty_identity() {
    // Empty identity NF is self-dual
    let nf: NF<()> = NF::identity(());
    let dual = dual_nf(&nf);

    assert!(dual.match_boundary.is_empty());
    assert!(dual.build_boundary.is_empty());
}

#[test]
fn dual_nf_swaps_boundaries() {
    // Fundamental: dual swaps match_boundary and build_boundary
    let (symbols, terms) = setup();
    let a = symbols.intern("A");
    let b = symbols.intern("B");
    let ta = terms.app0(a);
    let tb = terms.app0(b);

    // NF: A -> B
    let nf: NF<()> = NF::new(
        SmallVec::from_slice(&[ta]),
        SmallVec::from_slice(&[tb]),
    );

    let dual = dual_nf(&nf);

    // dual: B -> A
    assert_eq!(dual.match_boundary.as_slice(), &[tb], "match should be B");
    assert_eq!(dual.build_boundary.as_slice(), &[ta], "build should be A");
}

#[test]
fn dual_nf_involution() {
    // CRITICAL: dual(dual(nf)) == nf
    let (symbols, terms) = setup();
    let a = symbols.intern("A");
    let b = symbols.intern("B");
    let ta = terms.app0(a);
    let tb = terms.app0(b);

    let nf: NF<()> = NF::new(
        SmallVec::from_slice(&[ta]),
        SmallVec::from_slice(&[tb]),
    );

    let dual1 = dual_nf(&nf);
    let dual2 = dual_nf(&dual1);

    assert_eq!(dual2.match_boundary, nf.match_boundary);
    assert_eq!(dual2.build_boundary, nf.build_boundary);
}

#[test]
fn dual_nf_identity_is_self_dual() {
    // x -> x should be self-dual
    let (_, terms) = setup();
    let v0 = terms.var(0);

    let nf: NF<()> = NF::new(
        SmallVec::from_slice(&[v0]),
        SmallVec::from_slice(&[v0]),
    );

    let dual = dual_nf(&nf);

    assert_eq!(terms.is_var(dual.match_boundary[0]), Some(0));
    assert_eq!(terms.is_var(dual.build_boundary[0]), Some(0));
}

#[test]
fn dual_nf_preserves_constraint() {
    // Constraint should be preserved through dual
    let (symbols, terms) = setup();
    let a = symbols.intern("A");
    let b = symbols.intern("B");
    let ta = terms.app0(a);
    let tb = terms.app0(b);

    let nf: NF<i32> = NF::with_constraint(
        SmallVec::from_slice(&[ta]),
        SmallVec::from_slice(&[tb]),
        42,
    );

    let dual = dual_nf(&nf);

    assert_eq!(dual.constraint, 42, "Constraint must be preserved");
}

// ========================================================================
// PATTERN EDGE CASES
// ========================================================================

#[test]
fn dual_nf_ground_patterns() {
    // No variables case
    let (symbols, terms) = setup();
    let a = symbols.intern("A");
    let b = symbols.intern("B");
    let ta = terms.app0(a);
    let tb = terms.app0(b);

    let nf: NF<()> = NF::new(
        SmallVec::from_slice(&[ta]),
        SmallVec::from_slice(&[tb]),
    );

    let dual = dual_nf(&nf);

    assert_eq!(dual.match_boundary[0], tb);
    assert_eq!(dual.build_boundary[0], ta);
}

#[test]
fn dual_nf_empty_match_boundary() {
    // Empty match boundary becomes empty build boundary
    let (_, terms) = setup();
    let v0 = terms.var(0);

    let nf: NF<()> = NF::new(
        SmallVec::new(),
        SmallVec::from_slice(&[v0]),
    );

    let dual = dual_nf(&nf);

    assert_eq!(dual.match_boundary.len(), 1);
    assert!(dual.build_boundary.is_empty());
}

#[test]
fn dual_nf_empty_build_boundary() {
    // Empty build boundary becomes empty match boundary
    let (_, terms) = setup();
    let v0 = terms.var(0);

    let nf: NF<()> = NF::new(
        SmallVec::from_slice(&[v0]),
        SmallVec::new(),
    );

    let dual = dual_nf(&nf);

    assert!(dual.match_boundary.is_empty());
    assert_eq!(dual.build_boundary.len(), 1);
}

#[test]
fn dual_nf_multiple_patterns() {
    // Multiple patterns in both match and build
    let (symbols, terms) = setup();
    let a = symbols.intern("A");
    let b = symbols.intern("B");
    let c = symbols.intern("C");
    let ta = terms.app0(a);
    let tb = terms.app0(b);
    let tc = terms.app0(c);

    let nf: NF<()> = NF::new(
        SmallVec::from_slice(&[ta, tb]),
        SmallVec::from_slice(&[tc]),
    );

    let dual = dual_nf(&nf);

    assert_eq!(dual.match_boundary.len(), 1);
    assert_eq!(dual.build_boundary.len(), 2);
    assert_eq!(dual.match_boundary[0], tc);
    assert_eq!(dual.build_boundary.as_slice(), &[ta, tb]);
}

#[test]
fn dual_nf_deeply_nested_terms() {
    // Deep nesting should work
    let (symbols, mut terms) = setup();
    let f = symbols.intern("F");
    let v0 = terms.var(0);

    // F(F(F(F(x))))
    let f1 = terms.app1(f, v0);
    let f2 = terms.app1(f, f1);
    let f3 = terms.app1(f, f2);
    let f4 = terms.app1(f, f3);

    let nf: NF<()> = NF::new(
        SmallVec::from_slice(&[f4]),
        SmallVec::from_slice(&[v0]),
    );

    let dual = dual_nf(&nf);

    assert_eq!(dual.match_boundary[0], v0);
    assert_eq!(dual.build_boundary[0], f4);
}

// ========================================================================
// COMPOSITION REVERSAL TESTS (SEMANTIC CORRECTNESS)
// ========================================================================

#[test]
fn dual_reverses_composition_ground() {
    // dual(compose(a, b)) == compose(dual(b), dual(a)) for ground terms
    let (symbols, mut terms) = setup();
    let a = symbols.intern("A");
    let b = symbols.intern("B");
    let c = symbols.intern("C");
    let ta = terms.app0(a);
    let tb = terms.app0(b);
    let tc = terms.app0(c);

    // a: A -> B
    let nf_a: NF<()> = NF::new(
        SmallVec::from_slice(&[ta]),
        SmallVec::from_slice(&[tb]),
    );
    // b: B -> C
    let nf_b: NF<()> = NF::new(
        SmallVec::from_slice(&[tb]),
        SmallVec::from_slice(&[tc]),
    );

    // compose(a, b) = A -> C
    let composed = compose_nf(&nf_a, &nf_b, &mut terms).expect("composition should succeed");
    let dual_composed = dual_nf(&composed);

    // dual(b) = C -> B, dual(a) = B -> A
    // compose(dual(b), dual(a)) = C -> A
    let dual_b = dual_nf(&nf_b);
    let dual_a = dual_nf(&nf_a);
    let composed_duals =
        compose_nf(&dual_b, &dual_a, &mut terms).expect("composition should succeed");

    assert_eq!(dual_composed.match_boundary, composed_duals.match_boundary);
    assert_eq!(dual_composed.build_boundary, composed_duals.build_boundary);
}

#[test]
fn dual_reverses_composition_with_vars() {
    // Same test but with variables
    let (symbols, mut terms) = setup();
    let f = symbols.intern("F");
    let g = symbols.intern("G");
    let h = symbols.intern("H");
    let v0 = terms.var(0);

    let f_x = terms.app1(f, v0);
    let g_x = terms.app1(g, v0);
    let h_x = terms.app1(h, v0);

    // a: F(x) -> G(x)
    let nf_a: NF<()> = NF::new(
        SmallVec::from_slice(&[f_x]),
        SmallVec::from_slice(&[g_x]),
    );
    // b: G(x) -> H(x)
    let nf_b: NF<()> = NF::new(
        SmallVec::from_slice(&[g_x]),
        SmallVec::from_slice(&[h_x]),
    );

    let composed = compose_nf(&nf_a, &nf_b, &mut terms).expect("composition should succeed");
    let dual_composed = dual_nf(&composed);

    let dual_b = dual_nf(&nf_b);
    let dual_a = dual_nf(&nf_a);
    let composed_duals =
        compose_nf(&dual_b, &dual_a, &mut terms).expect("composition should succeed");

    // Both should be H(x) -> F(x)
    let (dc_match_f, _) = terms.is_app(dual_composed.match_boundary[0]).unwrap();
    let (cd_match_f, _) = terms.is_app(composed_duals.match_boundary[0]).unwrap();
    assert_eq!(symbols.resolve(dc_match_f), Some("H"));
    assert_eq!(symbols.resolve(cd_match_f), Some("H"));

    let (dc_build_f, _) = terms.is_app(dual_composed.build_boundary[0]).unwrap();
    let (cd_build_f, _) = terms.is_app(composed_duals.build_boundary[0]).unwrap();
    assert_eq!(symbols.resolve(dc_build_f), Some("F"));
    assert_eq!(symbols.resolve(cd_build_f), Some("F"));
}

#[test]
fn dual_reverses_peel_composition() {
    // Test from spec: B(A(x),y)->B(x,y) composed with itself
    let (symbols, mut terms) = setup();
    let a = symbols.intern("A");
    let b = symbols.intern("B");
    let v0 = terms.var(0);
    let v1 = terms.var(1);

    // B(A(x), y) -> B(x, y)
    let a_x = terms.app1(a, v0);
    let lhs = terms.app2(b, a_x, v1);
    let rhs = terms.app2(b, v0, v1);

    let peel: NF<()> = NF::from_patterns(
        SmallVec::from_slice(&[lhs]),
        SmallVec::from_slice(&[rhs]),
        (),
        &mut terms,
    );

    // compose(peel, peel)
    let composed = compose_nf(&peel, &peel, &mut terms).expect("composition should succeed");
    let dual_composed = dual_nf(&composed);

    // compose(dual(peel), dual(peel))
    let dual_peel = dual_nf(&peel);
    let composed_duals =
        compose_nf(&dual_peel, &dual_peel, &mut terms).expect("composition should succeed");

    // Both should have same arities
    assert_eq!(
        dual_composed.match_boundary.len(),
        composed_duals.match_boundary.len()
    );
    assert_eq!(
        dual_composed.build_boundary.len(),
        composed_duals.build_boundary.len()
    );
}

// ========================================================================
// VARIABLE STRUCTURE TESTS
// ========================================================================

#[test]
fn dual_nf_with_complex_variable_pattern() {
    // Test with variables appearing in both boundaries
    let (symbols, terms) = setup();
    let f = symbols.intern("F");
    let g = symbols.intern("G");
    let v0 = terms.var(0);
    let v1 = terms.var(1);

    let f_term = terms.app2(f, v0, v1);
    let g_term = terms.app1(g, v0);

    // F(x,y) -> G(x)
    let nf: NF<()> = NF::new(
        SmallVec::from_slice(&[f_term]),
        SmallVec::from_slice(&[g_term]),
    );

    let dual = dual_nf(&nf);

    // Dual: G(x) -> F(x,y)
    assert_eq!(dual.match_boundary[0], g_term);
    assert_eq!(dual.build_boundary[0], f_term);
}

#[test]
fn dual_nf_asymmetric_arities() {
    // Different number of patterns in match and build
    let (symbols, terms) = setup();
    let a = symbols.intern("A");
    let b = symbols.intern("B");
    let c = symbols.intern("C");
    let ta = terms.app0(a);
    let tb = terms.app0(b);
    let tc = terms.app0(c);

    // [A, B] -> [C]
    let nf: NF<()> = NF::new(
        SmallVec::from_slice(&[ta, tb]),
        SmallVec::from_slice(&[tc]),
    );

    let dual = dual_nf(&nf);

    // [C] -> [A, B]
    assert_eq!(dual.match_arity(), 1);
    assert_eq!(dual.build_arity(), 2);
    assert_eq!(dual.match_boundary[0], tc);
    assert_eq!(dual.build_boundary.as_slice(), &[ta, tb]);

    // Involution
    let dual2 = dual_nf(&dual);
    assert_eq!(dual2.match_arity(), 2);
    assert_eq!(dual2.build_arity(), 1);
}

#[test]
fn dual_nf_involution_complex() {
    // Involution with more complex NF
    let (symbols, mut terms) = setup();
    let f = symbols.intern("F");
    let g = symbols.intern("G");
    let h = symbols.intern("H");
    let v0 = terms.var(0);
    let v1 = terms.var(1);
    let v2 = terms.var(2);

    let f_term = terms.app2(f, v0, v1);
    let g_term = terms.app1(g, v0);
    let h_term = terms.app1(h, v2);

    // [F(x,y)] -> [G(x), H(z)]
    let nf: NF<()> = NF::new(
        SmallVec::from_slice(&[f_term]),
        SmallVec::from_slice(&[g_term, h_term]),
    );

    let dual1 = dual_nf(&nf);
    let dual2 = dual_nf(&dual1);

    assert_eq!(dual2.match_boundary, nf.match_boundary);
    assert_eq!(dual2.build_boundary, nf.build_boundary);
}
