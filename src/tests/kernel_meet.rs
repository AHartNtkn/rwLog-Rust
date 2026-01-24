use super::*;
use crate::constraint::TypeConstraints;
use crate::drop_fresh::DropFresh;
use crate::parser::Parser;
use crate::term::TermId;
use crate::test_utils::setup;
use smallvec::SmallVec;

// ========== BASIC MEET TESTS ==========

#[test]
fn meet_identical_identity() {
    let (_, mut terms) = setup();
    let v0 = terms.var(0);

    // Identity NF: x -> x
    let identity: NF<()> = NF::new(
        smallvec::smallvec![v0],
        DropFresh::identity(1),
        smallvec::smallvec![v0],
    );

    let result = meet_nf(&identity, &identity, &mut terms);
    assert!(result.is_some());
    let met = result.unwrap();

    // Meet of identity with itself is identity
    assert_eq!(met.match_pats.len(), 1);
    assert_eq!(met.build_pats.len(), 1);
}

#[test]
fn meet_applies_matching_to_constraints() {
    let mut parser = Parser::with_chr();
    let theory = r#"
theory neq_only {
  constraint neq/2
  (neq $x $x) <=> fail.
}
"#;
    parser.parse_theory_def(theory).expect("parse theory");
    let left = parser
        .parse_rule("$x { (neq $x z) } -> $x")
        .expect("parse left rule");
    let right = parser.parse_rule("z -> z").expect("parse right rule");
    let mut terms = parser.take_terms();

    let met = meet_nf(&left, &right, &mut terms);
    assert!(
        met.is_none(),
        "Expected meet to fail after constraint substitution"
    );
}

#[test]
fn meet_identical_ground_rules() {
    let (symbols, mut terms) = setup();
    let a = symbols.intern("A");
    let b = symbols.intern("B");

    let a_term = terms.app0(a);
    let b_term = terms.app0(b);

    // Rule: A -> B
    let rule: NF<()> = NF::new(
        smallvec::smallvec![a_term],
        DropFresh::identity(0),
        smallvec::smallvec![b_term],
    );

    let result = meet_nf(&rule, &rule, &mut terms);
    assert!(result.is_some());
    let met = result.unwrap();

    assert_eq!(met.match_pats[0], a_term);
    assert_eq!(met.build_pats[0], b_term);
}

#[test]
fn meet_specializes_var() {
    let (symbols, mut terms) = setup();
    let f = symbols.intern("F");
    let v0 = terms.var(0);

    // Rule a: x -> x (identity)
    let identity: NF<()> = NF::new(
        smallvec::smallvec![v0],
        DropFresh::identity(1),
        smallvec::smallvec![v0],
    );

    // Rule b: F(x) -> F(x) (identity on F terms)
    let f_x = terms.app1(f, v0);
    let f_rule: NF<()> = NF::new(
        smallvec::smallvec![f_x],
        DropFresh::identity(1),
        smallvec::smallvec![f_x],
    );

    let result = meet_nf(&identity, &f_rule, &mut terms);
    assert!(result.is_some());
    let met = result.unwrap();

    // Meet should specialize to F(x) -> F(x)
    let (match_func, _) = terms.is_app(met.match_pats[0]).unwrap();
    assert_eq!(symbols.resolve(match_func), Some("F"));
}

#[test]
fn meet_unifies_fresh_outputs() {
    let (symbols, mut terms) = setup();
    let f = symbols.intern("f");
    let b = symbols.intern("b");
    let l = symbols.intern("l");
    let c = symbols.intern("c");
    let zero = symbols.intern("0");

    let l_term = terms.app0(l);
    let zero_term = terms.app0(zero);
    let c0 = terms.app(c, smallvec::smallvec![zero_term]);
    let b_l = terms.app(b, smallvec::smallvec![l_term]);
    let b_b_l = terms.app(b, smallvec::smallvec![b_l]);
    let inner = terms.app(f, smallvec::smallvec![b_b_l, l_term]);
    let input = terms.app(f, smallvec::smallvec![inner, c0]);

    let inner_out = terms.app(f, smallvec::smallvec![l_term, c0]);
    let out1 = terms.app(f, smallvec::smallvec![inner_out, terms.var(0)]);
    let out2 = {
        let b_c0 = terms.app(b, smallvec::smallvec![c0]);
        terms.app(f, smallvec::smallvec![terms.var(0), b_c0])
    };

    let nf1 = NF::factor(input, out1, (), &mut terms);
    let nf2 = NF::factor(input, out2, (), &mut terms);

    let met = meet_nf(&nf1, &nf2, &mut terms).expect("meet should succeed");

    let expected_out = {
        let inner_expected = terms.app(f, smallvec::smallvec![l_term, c0]);
        let b_c0 = terms.app(b, smallvec::smallvec![c0]);
        terms.app(f, smallvec::smallvec![inner_expected, b_c0])
    };

    assert_eq!(met.match_pats[0], input);
    assert_eq!(met.build_pats[0], expected_out);
}

#[test]
fn meet_fails_incompatible_ground() {
    let (symbols, mut terms) = setup();
    let a = symbols.intern("A");
    let b = symbols.intern("B");
    let c = symbols.intern("C");

    let a_term = terms.app0(a);
    let b_term = terms.app0(b);
    let c_term = terms.app0(c);

    // Rule a: A -> B
    let rule_a: NF<()> = NF::new(
        smallvec::smallvec![a_term],
        DropFresh::identity(0),
        smallvec::smallvec![b_term],
    );

    // Rule b: C -> B (different match pattern)
    let rule_b: NF<()> = NF::new(
        smallvec::smallvec![c_term],
        DropFresh::identity(0),
        smallvec::smallvec![b_term],
    );

    let result = meet_nf(&rule_a, &rule_b, &mut terms);
    assert!(result.is_none(), "A and C don't match, meet should fail");
}

#[test]
fn meet_fails_incompatible_output() {
    let (symbols, mut terms) = setup();
    let a = symbols.intern("A");
    let b = symbols.intern("B");
    let c = symbols.intern("C");

    let a_term = terms.app0(a);
    let b_term = terms.app0(b);
    let c_term = terms.app0(c);

    // Rule a: A -> B
    let rule_a: NF<()> = NF::new(
        smallvec::smallvec![a_term],
        DropFresh::identity(0),
        smallvec::smallvec![b_term],
    );

    // Rule b: A -> C (same match, different build)
    let rule_b: NF<()> = NF::new(
        smallvec::smallvec![a_term],
        DropFresh::identity(0),
        smallvec::smallvec![c_term],
    );

    let result = meet_nf(&rule_a, &rule_b, &mut terms);
    assert!(result.is_none(), "B and C don't match, meet should fail");
}

#[test]
fn meet_unifies_compatible_patterns() {
    let (symbols, mut terms) = setup();
    let f = symbols.intern("F");
    let g = symbols.intern("G");
    let a = symbols.intern("A");
    let v0 = terms.var(0);
    let a_term = terms.app0(a);
    let f_x = terms.app1(f, v0);
    let f_a = terms.app1(f, a_term);
    let g_x = terms.app1(g, v0);
    let g_a = terms.app1(g, a_term);

    // Rule a: F(x) -> G(x)
    let rule_a: NF<()> = NF::new(
        smallvec::smallvec![f_x],
        DropFresh::identity(1),
        smallvec::smallvec![g_x],
    );

    // Rule b: F(A) -> G(A)
    let rule_b: NF<()> = NF::new(
        smallvec::smallvec![f_a],
        DropFresh::identity(0),
        smallvec::smallvec![g_a],
    );

    let result = meet_nf(&rule_a, &rule_b, &mut terms);
    assert!(result.is_some());
    let met = result.unwrap();

    // Meet should be F(A) -> G(A)
    assert_eq!(met.match_pats[0], f_a);
    assert_eq!(met.build_pats[0], g_a);
}

#[test]
fn meet_nested_patterns() {
    let (symbols, mut terms) = setup();
    let f = symbols.intern("F");
    let g = symbols.intern("G");
    let v0 = terms.var(0);
    // Rule a: F(x) -> G(x)
    let f_x = terms.app1(f, v0);
    let g_x = terms.app1(g, v0);
    let rule_a: NF<()> = NF::new(
        smallvec::smallvec![f_x],
        DropFresh::identity(1),
        smallvec::smallvec![g_x],
    );

    // Rule b: F(G(y)) -> G(G(y))
    let g_y = terms.app1(g, v0);
    let f_g_y = terms.app1(f, g_y);
    let g_g_y = terms.app1(g, g_y);
    let rule_b: NF<()> = NF::new(
        smallvec::smallvec![f_g_y],
        DropFresh::identity(1),
        smallvec::smallvec![g_g_y],
    );

    let result = meet_nf(&rule_a, &rule_b, &mut terms);
    assert!(result.is_some());
    let met = result.unwrap();

    // Meet should specialize to F(G(y)) -> G(G(y))
    let (match_f, match_c) = terms.is_app(met.match_pats[0]).unwrap();
    assert_eq!(symbols.resolve(match_f), Some("F"));
    let (inner_f, _) = terms.is_app(match_c[0]).unwrap();
    assert_eq!(symbols.resolve(inner_f), Some("G"));
}

#[test]
fn meet_symmetric() {
    let (symbols, mut terms) = setup();
    let f = symbols.intern("F");
    let a = symbols.intern("A");
    let v0 = terms.var(0);

    let a_term = terms.app0(a);
    let f_x = terms.app1(f, v0);
    let f_a = terms.app1(f, a_term);

    // Rule a: F(x) -> F(x)
    let rule_a: NF<()> = NF::new(
        smallvec::smallvec![f_x],
        DropFresh::identity(1),
        smallvec::smallvec![f_x],
    );

    // Rule b: F(A) -> F(A)
    let rule_b: NF<()> = NF::new(
        smallvec::smallvec![f_a],
        DropFresh::identity(0),
        smallvec::smallvec![f_a],
    );

    // meet(a, b) should equal meet(b, a)
    let result_ab = meet_nf(&rule_a, &rule_b, &mut terms);
    let result_ba = meet_nf(&rule_b, &rule_a, &mut terms);

    assert!(result_ab.is_some());
    assert!(result_ba.is_some());

    // Both should produce F(A) -> F(A)
    let met_ab = result_ab.unwrap();
    let met_ba = result_ba.unwrap();

    assert_eq!(met_ab.match_pats[0], met_ba.match_pats[0]);
    assert_eq!(met_ab.build_pats[0], met_ba.build_pats[0]);
}

#[test]
fn meet_empty_patterns() {
    let (_, mut terms) = setup();

    let empty: NF<()> = NF::new(SmallVec::new(), DropFresh::identity(0), SmallVec::new());

    let result = meet_nf(&empty, &empty, &mut terms);
    assert!(result.is_some());
}

#[test]
fn meet_with_different_vars() {
    let (symbols, mut terms) = setup();
    let pair = symbols.intern("Pair");
    let v0 = terms.var(0);
    let v1 = terms.var(1);

    // Rule a: Pair(x, y) -> Pair(x, y)
    let pair_xy = terms.app2(pair, v0, v1);
    let rule_a: NF<()> = NF::new(
        smallvec::smallvec![pair_xy],
        DropFresh::identity(2),
        smallvec::smallvec![pair_xy],
    );

    // Rule b: Pair(x, x) -> Pair(x, x) (diagonal)
    let pair_xx = terms.app2(pair, v0, v0);
    let rule_b: NF<()> = NF::new(
        smallvec::smallvec![pair_xx],
        DropFresh::identity(1),
        smallvec::smallvec![pair_xx],
    );

    let result = meet_nf(&rule_a, &rule_b, &mut terms);
    assert!(result.is_some());
    let met = result.unwrap();

    // Meet should specialize to Pair(x, x) -> Pair(x, x)
    let (_, match_c) = terms.is_app(met.match_pats[0]).unwrap();
    assert_eq!(match_c[0], match_c[1], "Both args should be the same var");
}

// ========== EDGE CASES ==========

#[test]
fn meet_var_with_complex_term() {
    let (symbols, mut terms) = setup();
    let f = symbols.intern("F");
    let g = symbols.intern("G");
    let v0 = terms.var(0);

    // Rule a: x -> x
    let identity: NF<()> = NF::new(
        smallvec::smallvec![v0],
        DropFresh::identity(1),
        smallvec::smallvec![v0],
    );

    // Rule b: F(G(x)) -> F(G(x))
    let g_x = terms.app1(g, v0);
    let f_g_x = terms.app1(f, g_x);
    let complex: NF<()> = NF::new(
        smallvec::smallvec![f_g_x],
        DropFresh::identity(1),
        smallvec::smallvec![f_g_x],
    );

    let result = meet_nf(&identity, &complex, &mut terms);
    assert!(result.is_some());
    let met = result.unwrap();

    // Should specialize to F(G(x)) -> F(G(x))
    let (f_id, f_c) = terms.is_app(met.match_pats[0]).unwrap();
    assert_eq!(symbols.resolve(f_id), Some("F"));
    let (g_id, _) = terms.is_app(f_c[0]).unwrap();
    assert_eq!(symbols.resolve(g_id), Some("G"));
}

#[test]
fn meet_fails_occurs_check() {
    let (symbols, mut terms) = setup();
    let f = symbols.intern("F");
    let v0 = terms.var(0);

    // Rule a: x -> F(x)
    let f_x = terms.app1(f, v0);
    let rule_a: NF<()> = NF::new(
        smallvec::smallvec![v0],
        DropFresh::identity(1),
        smallvec::smallvec![f_x],
    );

    // Rule b: F(x) -> x
    let rule_b: NF<()> = NF::new(
        smallvec::smallvec![f_x],
        DropFresh::identity(1),
        smallvec::smallvec![v0],
    );

    // The meet would require x = F(x), which fails occurs check.
    let result = meet_nf(&rule_a, &rule_b, &mut terms);
    assert!(result.is_none(), "Occurs check should reject x = F(x)");
}

#[test]
fn meet_multiple_var_constraints() {
    let (symbols, mut terms) = setup();
    let triple = symbols.intern("Triple");
    let v0 = terms.var(0);
    let v1 = terms.var(1);
    let v2 = terms.var(2);

    // Rule a: Triple(x, y, z) -> Triple(x, y, z)
    let triple_xyz: SmallVec<[TermId; 4]> = smallvec::smallvec![v0, v1, v2];
    let t_xyz = terms.app(triple, triple_xyz.clone());
    let rule_a: NF<()> = NF::new(
        smallvec::smallvec![t_xyz],
        DropFresh::identity(3),
        smallvec::smallvec![t_xyz],
    );

    // Rule b: Triple(x, x, y) -> Triple(x, x, y) (first two equal)
    let triple_xxy: SmallVec<[TermId; 4]> = smallvec::smallvec![v0, v0, v1];
    let t_xxy = terms.app(triple, triple_xxy);
    let rule_b: NF<()> = NF::new(
        smallvec::smallvec![t_xxy],
        DropFresh::identity(2),
        smallvec::smallvec![t_xxy],
    );

    let result = meet_nf(&rule_a, &rule_b, &mut terms);
    assert!(result.is_some());
    let met = result.unwrap();

    // Should specialize to Triple(x, x, y) pattern
    let (_, c) = terms.is_app(met.match_pats[0]).unwrap();
    assert_eq!(c[0], c[1], "First two should be same var");
}

// ========== REAL LOGIC PROGRAMMING EXAMPLES ==========

#[test]
fn meet_append_rules() {
    let (symbols, mut terms) = setup();
    let _cons = symbols.intern("Cons");
    let nil = symbols.intern("Nil");
    let append = symbols.intern("Append");
    let v0 = terms.var(0);
    let v1 = terms.var(1);
    let v2 = terms.var(2);

    let nil_term = terms.app0(nil);

    // Base case: Append(Nil, ys, ys)
    let base_args: SmallVec<[TermId; 4]> = smallvec::smallvec![nil_term, v1, v1];
    let base_term = terms.app(append, base_args);
    let base_rule: NF<()> = NF::new(
        smallvec::smallvec![base_term],
        DropFresh::identity(1),
        smallvec::smallvec![base_term],
    );

    // General query: Append(xs, ys, zs)
    let query_args: SmallVec<[TermId; 4]> = smallvec::smallvec![v0, v1, v2];
    let query_term = terms.app(append, query_args);
    let query: NF<()> = NF::new(
        smallvec::smallvec![query_term],
        DropFresh::identity(3),
        smallvec::smallvec![query_term],
    );

    let result = meet_nf(&query, &base_rule, &mut terms);
    assert!(result.is_some());
    let met = result.unwrap();

    // Should produce Append(Nil, ys, ys)
    let (f, c) = terms.is_app(met.match_pats[0]).unwrap();
    assert_eq!(symbols.resolve(f), Some("Append"));
    assert_eq!(c[0], nil_term); // First arg is Nil
    assert_eq!(c[1], c[2]); // Second and third args are same var
}

// ========== MULTI-PATTERN (TENSOR) MEET TESTS ==========

#[test]
fn meet_multi_pattern_identity() {
    let (_, mut terms) = setup();
    let v0 = terms.var(0);
    let v1 = terms.var(1);

    let rule: NF<()> = NF::new(
        smallvec::smallvec![v0, v1],
        DropFresh::identity(2),
        smallvec::smallvec![v0, v1],
    );

    let result = meet_nf(&rule, &rule, &mut terms);
    assert!(result.is_some());
    let met = result.unwrap();

    assert_eq!(met.match_pats.len(), 2);
    assert_eq!(met.build_pats.len(), 2);
    assert_eq!(met.match_pats[0], met.build_pats[0]);
    assert_eq!(met.match_pats[1], met.build_pats[1]);
}

#[test]
fn meet_multi_pattern_match_mismatch_fails() {
    let (symbols, mut terms) = setup();
    let a = symbols.intern("A");
    let b = symbols.intern("B");
    let v0 = terms.var(0);

    let a_term = terms.app0(a);
    let b_term = terms.app0(b);

    let rule_a: NF<()> = NF::new(
        smallvec::smallvec![a_term, v0],
        DropFresh::identity(1),
        smallvec::smallvec![a_term, v0],
    );

    let rule_b: NF<()> = NF::new(
        smallvec::smallvec![b_term, v0],
        DropFresh::identity(1),
        smallvec::smallvec![b_term, v0],
    );

    let result = meet_nf(&rule_a, &rule_b, &mut terms);
    assert!(result.is_none(), "Different match patterns should not meet");
}

#[test]
fn meet_multi_pattern_build_mismatch_fails() {
    let (symbols, mut terms) = setup();
    let a = symbols.intern("A");
    let b = symbols.intern("B");
    let v0 = terms.var(0);
    let v1 = terms.var(1);

    let a_term = terms.app0(a);
    let b_term = terms.app0(b);

    let rule_a: NF<()> = NF::new(
        smallvec::smallvec![v0, v1],
        DropFresh::identity(2),
        smallvec::smallvec![a_term, v0],
    );

    let rule_b: NF<()> = NF::new(
        smallvec::smallvec![v0, v1],
        DropFresh::identity(2),
        smallvec::smallvec![b_term, v0],
    );

    let result = meet_nf(&rule_a, &rule_b, &mut terms);
    assert!(result.is_none(), "Different build patterns should not meet");
}

#[test]
fn meet_multi_pattern_enforces_shared_variables() {
    let (_, mut terms) = setup();
    let v0 = terms.var(0);
    let v1 = terms.var(1);

    let rule_general: NF<()> = NF::new(
        smallvec::smallvec![v0, v1],
        DropFresh::identity(2),
        smallvec::smallvec![v0, v1],
    );

    let rule_same: NF<()> = NF::new(
        smallvec::smallvec![v0, v0],
        DropFresh::identity(1),
        smallvec::smallvec![v0, v0],
    );

    let result = meet_nf(&rule_general, &rule_same, &mut terms);
    assert!(result.is_some());
    let met = result.unwrap();

    assert_eq!(met.match_pats.len(), 2);
    let left = met.match_pats[0];
    let right = met.match_pats[1];
    assert_eq!(
        terms.is_var(left),
        terms.is_var(right),
        "Meet should enforce equality across positions"
    );
}

#[test]
fn meet_multi_pattern_wiring_induces_equality() {
    let (_, mut terms) = setup();
    let v0 = terms.var(0);
    let v1 = terms.var(1);

    let map_left = smallvec::smallvec![(1, 0)];
    let map_right = smallvec::smallvec![(0, 0)];

    let wire_left = DropFresh::new(2, 1, map_left, ()).unwrap();
    let wire_right = DropFresh::new(2, 1, map_right, ()).unwrap();

    let rule_left: NF<()> = NF::new(
        smallvec::smallvec![v0, v1],
        wire_left,
        smallvec::smallvec![v0],
    );

    let rule_right: NF<()> = NF::new(
        smallvec::smallvec![v0, v1],
        wire_right,
        smallvec::smallvec![v0],
    );

    let result = meet_nf(&rule_left, &rule_right, &mut terms);
    assert!(result.is_some(), "Wiring intersection should be non-empty");
    let met = result.unwrap();

    assert_eq!(met.match_pats.len(), 2);
    assert_eq!(
        terms.is_var(met.match_pats[0]),
        terms.is_var(met.match_pats[1]),
        "Wiring meet should force inputs equal"
    );
}

#[test]
fn meet_multi_pattern_arity_mismatch_fails() {
    let (_, mut terms) = setup();
    let v0 = terms.var(0);
    let v1 = terms.var(1);

    let rule_a: NF<()> = NF::new(
        smallvec::smallvec![v0, v1],
        DropFresh::identity(2),
        smallvec::smallvec![v0, v1],
    );

    let rule_b: NF<()> = NF::new(
        smallvec::smallvec![v0],
        DropFresh::identity(1),
        smallvec::smallvec![v0],
    );

    let result = meet_nf(&rule_a, &rule_b, &mut terms);
    assert!(result.is_none(), "Arity mismatch should fail");
}

#[test]
fn meet_multi_pattern_combines_constraints() {
    let (_, mut terms) = setup();
    let v0 = terms.var(0);
    let v1 = terms.var(1);

    let mut c_left = TypeConstraints::new();
    c_left.add(v0, 10);

    let mut c_right = TypeConstraints::new();
    c_right.add(v1, 20);

    let left = NF::new(
        smallvec::smallvec![v0, v1],
        DropFresh::identity_with_constraint(2, c_left),
        smallvec::smallvec![v0, v1],
    );

    let right = NF::new(
        smallvec::smallvec![v0, v1],
        DropFresh::identity_with_constraint(2, c_right),
        smallvec::smallvec![v0, v1],
    );

    let result = meet_nf(&left, &right, &mut terms);
    assert!(result.is_some());
    let met = result.unwrap();

    assert_eq!(met.drop_fresh.constraint.get_type(v0), Some(10));
    assert_eq!(met.drop_fresh.constraint.get_type(v1), Some(20));
}

#[test]
fn meet_multi_pattern_conflicting_constraints_fail() {
    let (_, mut terms) = setup();
    let v0 = terms.var(0);
    let v1 = terms.var(1);

    let mut c_left = TypeConstraints::new();
    c_left.add(v0, 10);

    let mut c_right = TypeConstraints::new();
    c_right.add(v0, 20);

    let left = NF::new(
        smallvec::smallvec![v0, v1],
        DropFresh::identity_with_constraint(2, c_left),
        smallvec::smallvec![v0, v1],
    );

    let right = NF::new(
        smallvec::smallvec![v0, v1],
        DropFresh::identity_with_constraint(2, c_right),
        smallvec::smallvec![v0, v1],
    );

    let result = meet_nf(&left, &right, &mut terms);
    assert!(
        result.is_none(),
        "Conflicting constraints should make meet fail"
    );
}
