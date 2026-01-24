use super::*;
use crate::test_utils::setup;

// ========== SUBST CONSTRUCTION TESTS ==========

#[test]
fn new_subst_is_empty() {
    let subst = Subst::new();
    assert!(subst.is_empty());
    assert_eq!(subst.len(), 0);
}

#[test]
fn with_capacity_creates_empty_subst() {
    let subst = Subst::with_capacity(10);
    assert!(subst.is_empty());
    assert_eq!(subst.len(), 0);
}

#[test]
fn bind_single_variable() {
    let (_, terms) = setup();
    let v5 = terms.var(5);

    let mut subst = Subst::new();
    subst.bind(0, v5);

    assert!(!subst.is_empty());
    assert_eq!(subst.len(), 1);
    assert_eq!(subst.get(0), Some(v5));
}

#[test]
fn bind_multiple_variables() {
    let (_, terms) = setup();
    let v0 = terms.var(0);
    let v1 = terms.var(1);
    let v2 = terms.var(2);

    let mut subst = Subst::new();
    subst.bind(0, v1);
    subst.bind(1, v2);
    subst.bind(2, v0);

    assert_eq!(subst.len(), 3);
    assert_eq!(subst.get(0), Some(v1));
    assert_eq!(subst.get(1), Some(v2));
    assert_eq!(subst.get(2), Some(v0));
}

#[test]
fn bind_extends_automatically() {
    let (_, terms) = setup();
    let t = terms.var(99);

    let mut subst = Subst::new();
    subst.bind(100, t);

    assert_eq!(subst.get(100), Some(t));
    assert_eq!(subst.len(), 1);
}

#[test]
fn bind_overwrites_previous() {
    let (_, terms) = setup();
    let v1 = terms.var(1);
    let v2 = terms.var(2);

    let mut subst = Subst::new();
    subst.bind(0, v1);
    subst.bind(0, v2);

    assert_eq!(subst.get(0), Some(v2));
    assert_eq!(subst.len(), 1);
}

#[test]
fn get_unbound_returns_none() {
    let subst = Subst::new();
    assert_eq!(subst.get(0), None);
    assert_eq!(subst.get(100), None);
}

#[test]
fn is_bound_correct() {
    let (_, terms) = setup();
    let t = terms.var(5);

    let mut subst = Subst::new();
    subst.bind(0, t);

    assert!(subst.is_bound(0));
    assert!(!subst.is_bound(1));
    assert!(!subst.is_bound(100));
}

#[test]
fn iter_over_bindings() {
    let (_, terms) = setup();
    let v1 = terms.var(1);
    let v2 = terms.var(2);

    let mut subst = Subst::new();
    subst.bind(0, v1);
    subst.bind(2, v2); // skip index 1

    let bindings: Vec<_> = subst.iter().collect();
    assert_eq!(bindings.len(), 2);
    assert!(bindings.contains(&(0, v1)));
    assert!(bindings.contains(&(2, v2)));
}

// ========== APPLY_SUBST TESTS ==========

#[test]
fn apply_to_unbound_var_unchanged() {
    let (_, mut terms) = setup();
    let v0 = terms.var(0);
    let subst = Subst::new();

    let result = apply_subst(v0, &subst, &mut terms);
    assert_eq!(result, v0);
}

#[test]
fn apply_to_bound_var_replaces() {
    let (symbols, mut terms) = setup();
    let nil = symbols.intern("Nil");
    let v0 = terms.var(0);
    let nil_term = terms.app0(nil);

    let mut subst = Subst::new();
    subst.bind(0, nil_term);

    let result = apply_subst(v0, &subst, &mut terms);
    assert_eq!(result, nil_term);
}

#[test]
fn apply_to_ground_term_unchanged() {
    let (symbols, mut terms) = setup();
    let zero = symbols.intern("Zero");
    let succ = symbols.intern("Succ");
    let n0 = terms.app0(zero);
    let n1 = terms.app1(succ, n0);

    let mut subst = Subst::new();
    subst.bind(0, n0);

    let result = apply_subst(n1, &subst, &mut terms);
    assert_eq!(result, n1, "Ground term should be unchanged");
}

#[test]
fn apply_replaces_in_nested_term() {
    let (symbols, mut terms) = setup();
    let f = symbols.intern("F");
    let g = symbols.intern("G");
    let v0 = terms.var(0);
    let v1 = terms.var(1);

    // F(x, G(y))
    let g_y = terms.app1(g, v1);
    let term = terms.app2(f, v0, g_y);

    // Substitute x -> G(y)
    let mut subst = Subst::new();
    subst.bind(0, g_y);

    let result = apply_subst(term, &subst, &mut terms);

    // Should be F(G(y), G(y))
    let expected = terms.app2(f, g_y, g_y);
    assert_eq!(result, expected);
}

#[test]
fn apply_multiple_substitutions() {
    let (symbols, mut terms) = setup();
    let pair = symbols.intern("Pair");
    let v0 = terms.var(0);
    let v1 = terms.var(1);
    let v2 = terms.var(2);
    let v3 = terms.var(3);

    // Pair(x, y)
    let term = terms.app2(pair, v0, v1);

    // Substitute x -> z, y -> w
    let mut subst = Subst::new();
    subst.bind(0, v2);
    subst.bind(1, v3);

    let result = apply_subst(term, &subst, &mut terms);

    // Should be Pair(z, w)
    let expected = terms.app2(pair, v2, v3);
    assert_eq!(result, expected);
}

#[test]
fn apply_deeply_nested() {
    let (symbols, mut terms) = setup();
    let f = symbols.intern("F");
    let a = symbols.intern("A");
    let v0 = terms.var(0);

    // F(F(F(F(x))))
    let f1 = terms.app1(f, v0);
    let f2 = terms.app1(f, f1);
    let f3 = terms.app1(f, f2);
    let f4 = terms.app1(f, f3);

    // Substitute x -> A
    let a_term = terms.app0(a);
    let mut subst = Subst::new();
    subst.bind(0, a_term);

    let result = apply_subst(f4, &subst, &mut terms);

    // Should be F(F(F(F(A))))
    let e1 = terms.app1(f, a_term);
    let e2 = terms.app1(f, e1);
    let e3 = terms.app1(f, e2);
    let expected = terms.app1(f, e3);
    assert_eq!(result, expected);
}

#[test]
fn apply_chain_of_vars() {
    let (_, mut terms) = setup();
    let v0 = terms.var(0);
    let v1 = terms.var(1);
    let v2 = terms.var(2);

    // Substitute 0 -> 1, 1 -> 2
    let mut subst = Subst::new();
    subst.bind(0, v1);
    subst.bind(1, v2);

    // Apply to var(0) should follow the chain: 0 -> 1 -> 2
    let result = apply_subst(v0, &subst, &mut terms);
    assert_eq!(result, v2, "Should follow chain of substitutions");
}

#[test]
fn apply_to_wide_term() {
    let (symbols, mut terms) = setup();
    let tuple = symbols.intern("Tuple");
    let a = symbols.intern("A");
    let v0 = terms.var(0);
    let v1 = terms.var(1);
    let v2 = terms.var(2);

    // Tuple(x, y, z)
    let children: SmallVec<[TermId; 4]> = smallvec::smallvec![v0, v1, v2];
    let term = terms.app(tuple, children);

    // Substitute all with A
    let a_term = terms.app0(a);
    let mut subst = Subst::new();
    subst.bind(0, a_term);
    subst.bind(1, a_term);
    subst.bind(2, a_term);

    let result = apply_subst(term, &subst, &mut terms);

    // Should be Tuple(A, A, A)
    let expected_children: SmallVec<[TermId; 4]> = smallvec::smallvec![a_term, a_term, a_term];
    let expected = terms.app(tuple, expected_children);
    assert_eq!(result, expected);
}

#[test]
fn apply_preserves_structure() {
    let (symbols, mut terms) = setup();
    let cons = symbols.intern("Cons");
    let nil = symbols.intern("Nil");
    let v0 = terms.var(0);
    let v1 = terms.var(1);

    // Cons(x, Cons(y, Nil))
    let nil_term = terms.app0(nil);
    let inner = terms.app2(cons, v1, nil_term);
    let term = terms.app2(cons, v0, inner);

    // Empty substitution
    let subst = Subst::new();

    let result = apply_subst(term, &subst, &mut terms);
    assert_eq!(result, term, "Empty subst should preserve term exactly");
}

// ========== EDGE CASES ==========

#[test]
fn apply_subst_var_maps_to_itself() {
    let (_, mut terms) = setup();
    let v0 = terms.var(0);

    // Substitute 0 -> 0 (identity)
    let mut subst = Subst::new();
    subst.bind(0, v0);

    let result = apply_subst(v0, &subst, &mut terms);
    assert_eq!(result, v0);
}

#[test]
fn apply_nullary_app() {
    let (symbols, mut terms) = setup();
    let zero = symbols.intern("Zero");
    let term = terms.app0(zero);

    let mut subst = Subst::new();
    subst.bind(0, terms.var(1));

    let result = apply_subst(term, &subst, &mut terms);
    assert_eq!(result, term, "Nullary app unchanged");
}

#[test]
fn apply_sparse_binding() {
    let (symbols, mut terms) = setup();
    let f = symbols.intern("F");
    let a = symbols.intern("A");
    let v0 = terms.var(0);
    let v100 = terms.var(100);

    // F(x0, x100)
    let term = terms.app2(f, v0, v100);

    // Only bind var 100
    let a_term = terms.app0(a);
    let mut subst = Subst::new();
    subst.bind(100, a_term);

    let result = apply_subst(term, &subst, &mut terms);

    // Should be F(x0, A)
    let expected = terms.app2(f, v0, a_term);
    assert_eq!(result, expected);
}

// ========== HASHCONSING INTERACTION ==========

#[test]
fn apply_uses_hashconsing() {
    let (symbols, mut terms) = setup();
    let f = symbols.intern("F");
    let a = symbols.intern("A");
    let v0 = terms.var(0);

    // F(x) and F(x) separately
    let term1 = terms.app1(f, v0);
    let term2 = terms.app1(f, v0);
    assert_eq!(term1, term2, "Hashconsing should work");

    // Substitute x -> A
    let a_term = terms.app0(a);
    let mut subst = Subst::new();
    subst.bind(0, a_term);

    let result1 = apply_subst(term1, &subst, &mut terms);
    let result2 = apply_subst(term2, &subst, &mut terms);

    // Results should also be same via hashconsing
    assert_eq!(result1, result2);
}
