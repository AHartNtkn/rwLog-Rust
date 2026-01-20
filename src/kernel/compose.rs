use crate::constraint::ConstraintOps;
use crate::nf::{collect_tensor, factor_tensor, NF};
use crate::term::TermStore;
#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};

use super::util::{
    apply_subst_list, max_var_index_terms, remap_constraint_vars, shift_vars_list, unify_term_lists,
};

/// Compose two NFs in sequence: a ; b
///
/// This computes the composition where:
/// - First, a's match patterns are matched against input
/// - Variables are routed through a's DropFresh
/// - a's build patterns are constructed
/// - b's match patterns are matched against a's output
/// - Variables are routed through b's DropFresh
/// - b's build patterns are constructed
///
/// Returns None if composition fails (unification failure at interface).
pub fn compose_nf<C: ConstraintOps>(a: &NF<C>, b: &NF<C>, terms: &mut TermStore) -> Option<NF<C>> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!(
        "compose_nf",
        a_match_arity = a.match_pats.len(),
        a_build_arity = a.build_pats.len(),
        b_match_arity = b.match_pats.len(),
        b_build_arity = b.build_pats.len(),
        a_drop_fresh_in = a.drop_fresh.in_arity,
        a_drop_fresh_out = a.drop_fresh.out_arity,
        b_drop_fresh_in = b.drop_fresh.in_arity,
        b_drop_fresh_out = b.drop_fresh.out_arity,
    )
    .entered();

    if a.build_pats.len() != b.match_pats.len() {
        #[cfg(feature = "tracing")]
        trace!(
            a_build = a.build_pats.len(),
            b_match = b.match_pats.len(),
            "arity_mismatch"
        );
        return None; // Arity mismatch
    }

    let rw1 = collect_tensor(a, terms);
    let mut rw2 = collect_tensor(b, terms);
    let b_max_var = max_var_index_terms(&rw2.lhs, terms).max(max_var_index_terms(&rw2.rhs, terms));

    let b_var_offset = max_var_index_terms(&rw1.lhs, terms)
        .max(max_var_index_terms(&rw1.rhs, terms))
        .map(|v| v + 1)
        .unwrap_or(0);

    if b_var_offset != 0 {
        rw2.lhs = shift_vars_list(&rw2.lhs, b_var_offset, terms);
        rw2.rhs = shift_vars_list(&rw2.rhs, b_var_offset, terms);
    }

    #[cfg(feature = "tracing")]
    trace!(
        a_rhs = ?rw1.rhs,
        b_lhs_shifted = ?rw2.lhs,
        b_var_offset,
        "unifying_interface"
    );

    let mgu = match unify_term_lists(&rw1.rhs, &rw2.lhs, terms) {
        Some(mgu) => {
            #[cfg(feature = "tracing")]
            trace!(mgu_size = mgu.len(), "unification_success");
            mgu
        }
        None => {
            #[cfg(feature = "tracing")]
            trace!("unification_failed");
            return None;
        }
    };

    let mut new_match = apply_subst_list(&rw1.lhs, &mgu, terms);
    let mut new_build = apply_subst_list(&rw2.rhs, &mgu, terms);

    let b_constraint =
        remap_constraint_vars(&b.drop_fresh.constraint, b_max_var, b_var_offset, terms);

    let combined = match a.drop_fresh.constraint.combine(&b_constraint) {
        Some(c) => c,
        None => {
            #[cfg(feature = "tracing")]
            trace!("compose_constraint_conflict");
            return None;
        }
    };
    let combined = combined.apply_subst(&mgu, terms);

    let (normalized, subst_opt) = match combined.normalize(terms) {
        Some(result) => result,
        None => {
            #[cfg(feature = "tracing")]
            trace!("compose_constraint_unsat");
            return None;
        }
    };
    if let Some(subst) = subst_opt {
        new_match = apply_subst_list(&new_match, &subst, terms);
        new_build = apply_subst_list(&new_build, &subst, terms);
    }

    Some(factor_tensor(new_match, new_build, normalized, terms))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::drop_fresh::DropFresh;
    use crate::parser::Parser;
    use crate::test_utils::setup;
    use smallvec::SmallVec;

    // ========== BASIC COMPOSITION TESTS ==========

    #[test]
    fn compose_identity_identity() {
        let (_, mut terms) = setup();
        let v0 = terms.var(0);

        // Identity NF: x -> x
        let identity: NF<()> = NF::new(
            smallvec::smallvec![v0],
            DropFresh::identity(1),
            smallvec::smallvec![v0],
        );

        let result = compose_nf(&identity, &identity, &mut terms);
        assert!(result.is_some());
        let composed = result.unwrap();

        // Identity composed with identity is identity
        assert_eq!(composed.match_pats.len(), 1);
        assert_eq!(composed.build_pats.len(), 1);
        assert!(composed.drop_fresh.is_identity());
    }

    #[test]
    fn compose_applies_mgu_to_constraints() {
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

        let composed = compose_nf(&left, &right, &mut terms);
        assert!(
            composed.is_none(),
            "Expected composition to fail after constraint substitution"
        );
    }

    #[test]
    fn compose_preserves_constraint_var_binding() {
        let mut parser = Parser::with_chr();
        let theory = r#"
theory no_c {
  constraint no_c/1
}
"#;
        parser.parse_theory_def(theory).expect("parse theory");
        let left = parser
            .parse_rule("$x { (no_c $x) } -> $x")
            .expect("parse left rule");
        let right = parser
            .parse_rule("$x -> (f $x (c z))")
            .expect("parse right rule");
        let mut terms = parser.take_terms();

        let composed = compose_nf(&left, &right, &mut terms).expect("compose should succeed");
        let state = &composed.drop_fresh.constraint;
        let pred = state
            .program
            .pred_id("no_c")
            .expect("expected no_c predicate");
        let alive: Vec<_> = state.store.inst.iter().filter(|inst| inst.alive).collect();
        assert_eq!(alive.len(), 1, "expected one no_c constraint");
        let inst = alive[0];
        assert_eq!(inst.pred, pred, "expected no_c constraint");
        assert_eq!(inst.args.len(), 1, "no_c should have one arg");
        assert!(
            terms.is_var(inst.args[0]).is_some(),
            "no_c arg should remain a variable"
        );
    }

    #[test]
    fn compose_ground_rules() {
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

        // Rule b: B -> C
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![b_term],
            DropFresh::identity(0),
            smallvec::smallvec![c_term],
        );

        let result = compose_nf(&rule_a, &rule_b, &mut terms);
        assert!(result.is_some());
        let composed = result.unwrap();

        // A -> B ; B -> C = A -> C
        assert_eq!(composed.match_pats[0], a_term);
        assert_eq!(composed.build_pats[0], c_term);
    }

    #[test]
    fn compose_fails_on_mismatch() {
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

        // Rule b: C -> A (doesn't match B)
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![c_term],
            DropFresh::identity(0),
            smallvec::smallvec![a_term],
        );

        let result = compose_nf(&rule_a, &rule_b, &mut terms);
        assert!(result.is_none(), "B != C so composition should fail");
    }

    #[test]
    fn compose_with_variables() {
        let (symbols, mut terms) = setup();
        let f = symbols.intern("F");
        let g = symbols.intern("G");
        let v0 = terms.var(0);

        // Rule a: F(x) -> x (unwrap F)
        let f_x = terms.app1(f, v0);
        let rule_a: NF<()> = NF::new(
            smallvec::smallvec![f_x],
            DropFresh::identity(1),
            smallvec::smallvec![v0],
        );

        // Rule b: x -> G(x) (wrap in G)
        let g_x = terms.app1(g, v0);
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![v0],
            DropFresh::identity(1),
            smallvec::smallvec![g_x],
        );

        let result = compose_nf(&rule_a, &rule_b, &mut terms);
        assert!(result.is_some());
        let composed = result.unwrap();

        // F(x) -> x ; x -> G(x) = F(x) -> G(x)
        // Match pattern should be F(_)
        let (match_f, _match_children) = terms.is_app(composed.match_pats[0]).unwrap();
        assert_eq!(symbols.resolve(match_f), Some("F"));

        // Build pattern should be G(_)
        let (build_f, _) = terms.is_app(composed.build_pats[0]).unwrap();
        assert_eq!(symbols.resolve(build_f), Some("G"));
    }

    #[test]
    fn compose_peeling() {
        let (symbols, mut terms) = setup();
        let s = symbols.intern("S");
        let v0 = terms.var(0);

        // Rule: S(x) -> x (peel one S)
        let s_x = terms.app1(s, v0);
        let peel: NF<()> = NF::new(
            smallvec::smallvec![s_x],
            DropFresh::identity(1),
            smallvec::smallvec![v0],
        );

        // Compose peel ; peel = S(S(x)) -> x
        let result = compose_nf(&peel, &peel, &mut terms);
        assert!(result.is_some());
        let composed = result.unwrap();

        // Match pattern should be S(S(x))
        let (f1, c1) = terms.is_app(composed.match_pats[0]).unwrap();
        assert_eq!(symbols.resolve(f1), Some("S"));
        let (f2, _) = terms.is_app(c1[0]).unwrap();
        assert_eq!(symbols.resolve(f2), Some("S"));

        // Build pattern should be just x
        assert!(terms.is_var(composed.build_pats[0]).is_some());
    }

    #[test]
    fn compose_wrapping() {
        let (symbols, mut terms) = setup();
        let s = symbols.intern("S");
        let v0 = terms.var(0);

        // Rule: x -> S(x) (add one S)
        let s_x = terms.app1(s, v0);
        let wrap: NF<()> = NF::new(
            smallvec::smallvec![v0],
            DropFresh::identity(1),
            smallvec::smallvec![s_x],
        );

        // Compose wrap ; wrap = x -> S(S(x))
        let result = compose_nf(&wrap, &wrap, &mut terms);
        assert!(result.is_some());
        let composed = result.unwrap();

        // Match pattern should be just x
        assert!(terms.is_var(composed.match_pats[0]).is_some());

        // Build pattern should be S(S(x))
        let (f1, c1) = terms.is_app(composed.build_pats[0]).unwrap();
        assert_eq!(symbols.resolve(f1), Some("S"));
        let (f2, _) = terms.is_app(c1[0]).unwrap();
        assert_eq!(symbols.resolve(f2), Some("S"));
    }

    #[test]
    fn compose_variable_passing() {
        let (symbols, mut terms) = setup();
        let pair = symbols.intern("Pair");
        let fst = symbols.intern("Fst");
        let _snd = symbols.intern("Snd");
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // Rule a: Pair(x, y) -> Fst(x) (extract first)
        let pair_xy = terms.app2(pair, v0, v1);
        let fst_x = terms.app1(fst, v0);
        let rule_a: NF<()> = NF::new(
            smallvec::smallvec![pair_xy],
            DropFresh {
                in_arity: 2,
                out_arity: 1,
                map: smallvec::smallvec![(0, 0)],
                constraint: (),
            },
            smallvec::smallvec![fst_x],
        );

        // Rule b: Fst(x) -> x (unwrap Fst)
        let v0_b = terms.var(0);
        let fst_x_b = terms.app1(fst, v0_b);
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![fst_x_b],
            DropFresh::identity(1),
            smallvec::smallvec![v0_b],
        );

        let result = compose_nf(&rule_a, &rule_b, &mut terms);
        assert!(result.is_some());
        let composed = result.unwrap();

        // Pair(x, y) -> Fst(x) ; Fst(x) -> x = Pair(x, y) -> x
        let (match_f, _) = terms.is_app(composed.match_pats[0]).unwrap();
        assert_eq!(symbols.resolve(match_f), Some("Pair"));

        // Build should be a variable
        assert!(terms.is_var(composed.build_pats[0]).is_some());
    }

    // ========== EDGE CASES ==========

    #[test]
    fn compose_ground_with_var_match() {
        let (symbols, mut terms) = setup();
        let a = symbols.intern("A");
        let f = symbols.intern("F");
        let v0 = terms.var(0);

        let a_term = terms.app0(a);
        let f_a = terms.app1(f, a_term);

        // Rule a: A -> A (identity on A)
        let rule_a: NF<()> = NF::new(
            smallvec::smallvec![a_term],
            DropFresh::identity(0),
            smallvec::smallvec![a_term],
        );

        // Rule b: x -> F(x) (wrap anything)
        let f_x = terms.app1(f, v0);
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![v0],
            DropFresh::identity(1),
            smallvec::smallvec![f_x],
        );

        let result = compose_nf(&rule_a, &rule_b, &mut terms);
        assert!(result.is_some());
        let composed = result.unwrap();

        // A -> A ; x -> F(x) = A -> F(A)
        assert_eq!(composed.match_pats[0], a_term);
        assert_eq!(composed.build_pats[0], f_a);
    }

    #[test]
    fn compose_empty_patterns() {
        let (_, mut terms) = setup();

        // Empty NFs with just DropFresh maps
        let nf_a: NF<()> = NF::new(SmallVec::new(), DropFresh::identity(0), SmallVec::new());

        let nf_b: NF<()> = NF::new(SmallVec::new(), DropFresh::identity(0), SmallVec::new());

        let result = compose_nf(&nf_a, &nf_b, &mut terms);
        assert!(result.is_some());
    }

    #[test]
    fn compose_nested_constructors() {
        let (symbols, mut terms) = setup();
        let f = symbols.intern("F");
        let g = symbols.intern("G");
        let h = symbols.intern("H");
        let v0 = terms.var(0);

        // Rule a: F(G(x)) -> G(x) (strip F)
        let g_x = terms.app1(g, v0);
        let f_g_x = terms.app1(f, g_x);
        let rule_a: NF<()> = NF::new(
            smallvec::smallvec![f_g_x],
            DropFresh::identity(1),
            smallvec::smallvec![g_x],
        );

        // Rule b: G(x) -> H(x) (replace G with H)
        let h_x = terms.app1(h, v0);
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![g_x],
            DropFresh::identity(1),
            smallvec::smallvec![h_x],
        );

        let result = compose_nf(&rule_a, &rule_b, &mut terms);
        assert!(result.is_some());
        let composed = result.unwrap();

        // F(G(x)) -> G(x) ; G(x) -> H(x) = F(G(x)) -> H(x)
        let (match_f, match_c) = terms.is_app(composed.match_pats[0]).unwrap();
        assert_eq!(symbols.resolve(match_f), Some("F"));
        let (inner_f, _) = terms.is_app(match_c[0]).unwrap();
        assert_eq!(symbols.resolve(inner_f), Some("G"));

        let (build_f, _) = terms.is_app(composed.build_pats[0]).unwrap();
        assert_eq!(symbols.resolve(build_f), Some("H"));
    }

    // ========== WORKED EXAMPLE FROM SPEC ==========

    #[test]
    fn compose_peel_twice_example() {
        // From spec: B(A(x),y)->B(x,y) composed with itself
        // Should produce B(A(A(x)),y)->B(x,y)
        let (symbols, mut terms) = setup();
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // Rule: B(A(x), y) -> B(x, y)
        let a_x = terms.app1(a, v0);
        let lhs = terms.app2(b, a_x, v1);
        let rhs = terms.app2(b, v0, v1);

        let peel: NF<()> = NF::factor(lhs, rhs, (), &mut terms);

        // Compose peel ; peel
        let result = compose_nf(&peel, &peel, &mut terms);
        assert!(result.is_some(), "Composition should succeed");
        let composed = result.unwrap();

        // Match should be B(A(A(x)), y)
        let (match_f, match_c) = terms.is_app(composed.match_pats[0]).unwrap();
        assert_eq!(symbols.resolve(match_f), Some("B"));

        // First arg should be A(A(x))
        let (a1_f, a1_c) = terms.is_app(match_c[0]).unwrap();
        assert_eq!(symbols.resolve(a1_f), Some("A"));
        let (a2_f, _) = terms.is_app(a1_c[0]).unwrap();
        assert_eq!(symbols.resolve(a2_f), Some("A"));

        // Build should be B(x, y)
        let (build_f, build_c) = terms.is_app(composed.build_pats[0]).unwrap();
        assert_eq!(symbols.resolve(build_f), Some("B"));
        assert!(terms.is_var(build_c[0]).is_some());
        assert!(terms.is_var(build_c[1]).is_some());
    }

    // ========== BACKWARD QUERY SYMMETRY TESTS ==========
    // These tests verify that compose_nf works correctly for backward queries
    // where a relation's output is constrained by a ground term.

    #[test]
    fn compose_backward_query_ground_constraint() {
        // Simulates: add_base_case ; identity_on_z
        // add base case: (cons z $0) -> $0
        // identity on z: z -> z
        // Expected: (cons z z) -> z
        let (symbols, mut terms) = setup();
        let cons_sym = symbols.intern("cons");
        let z_sym = symbols.intern("z");

        let z = terms.app0(z_sym);
        let v0 = terms.var(0);

        // add base case: (cons z $0) -> $0
        let cons_z_v0 = terms.app2(cons_sym, z, v0);
        let add_base: NF<()> = NF::factor(cons_z_v0, v0, (), &mut terms);

        // identity on z: z -> z (ground term)
        let identity_z: NF<()> = NF::factor(z, z, (), &mut terms);

        // Compose: add_base ; identity_z
        let result = compose_nf(&add_base, &identity_z, &mut terms);

        assert!(
            result.is_some(),
            "Composition should succeed: variable $0 should unify with ground z"
        );

        let composed = result.unwrap();

        // Match should be (cons z z) - the variable $0 should be bound to z
        let (match_f, match_c) = terms.is_app(composed.match_pats[0]).unwrap();
        assert_eq!(symbols.resolve(match_f), Some("cons"));
        assert_eq!(match_c[0], z, "First arg should be z");
        assert_eq!(match_c[1], z, "Second arg should be z (variable bound)");

        // Build should be z
        assert_eq!(composed.build_pats[0], z, "Output should be z");
    }

    #[test]
    fn compose_backward_query_ground_constraint_s_z() {
        // Simulates backward query for sum = 1
        // Two cases that should match:
        // 1. add base: (cons z $0) -> $0  with identity on (s z)
        //    => (cons z (s z)) -> (s z)  [0 + 1 = 1]
        let (symbols, mut terms) = setup();
        let cons_sym = symbols.intern("cons");
        let z_sym = symbols.intern("z");
        let s_sym = symbols.intern("s");

        let z = terms.app0(z_sym);
        let s_z = terms.app1(s_sym, z);
        let v0 = terms.var(0);

        // add base case: (cons z $0) -> $0
        let cons_z_v0 = terms.app2(cons_sym, z, v0);
        let add_base: NF<()> = NF::factor(cons_z_v0, v0, (), &mut terms);

        // identity on (s z): (s z) -> (s z)
        let identity_s_z: NF<()> = NF::factor(s_z, s_z, (), &mut terms);

        // Compose: add_base ; identity_s_z
        let result = compose_nf(&add_base, &identity_s_z, &mut terms);

        assert!(
            result.is_some(),
            "Composition should succeed: variable $0 should unify with (s z)"
        );

        let composed = result.unwrap();

        // Match should be (cons z (s z))
        let (match_f, match_c) = terms.is_app(composed.match_pats[0]).unwrap();
        assert_eq!(symbols.resolve(match_f), Some("cons"));
        assert_eq!(match_c[0], z, "First arg should be z");
        // Second arg should be (s z)
        let (s_f, s_c) = terms.is_app(match_c[1]).unwrap();
        assert_eq!(symbols.resolve(s_f), Some("s"));
        assert_eq!(s_c[0], z, "Arg of s should be z");

        // Build should be (s z)
        assert_eq!(composed.build_pats[0], s_z, "Output should be (s z)");
    }

    #[test]
    fn compose_var_with_ground_unifies() {
        // Most basic case: $0 -> $0 composed with z -> z should give z -> z
        let (symbols, mut terms) = setup();
        let z_sym = symbols.intern("z");
        let z = terms.app0(z_sym);
        let v0 = terms.var(0);

        // identity relation: $0 -> $0
        let identity_var: NF<()> = NF::factor(v0, v0, (), &mut terms);

        // identity on z: z -> z
        let identity_z: NF<()> = NF::factor(z, z, (), &mut terms);

        // Compose: ($0 -> $0) ; (z -> z) should give z -> z
        let result = compose_nf(&identity_var, &identity_z, &mut terms);

        assert!(result.is_some(), "Variable should unify with ground term");
        let composed = result.unwrap();

        assert_eq!(composed.match_pats[0], z, "Match should be z");
        assert_eq!(composed.build_pats[0], z, "Build should be z");
    }

    #[test]
    fn compose_introduces_fresh_var_then_projects() {
        let (symbols, mut terms) = setup();
        let f = symbols.intern("f");
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        let f_v0_v1 = terms.app(f, smallvec::smallvec![v0, v1]);
        let rule_intro = NF::factor(v0, f_v0_v1, (), &mut terms);
        let rule_proj = NF::factor(f_v0_v1, v0, (), &mut terms);

        let composed =
            compose_nf(&rule_intro, &rule_proj, &mut terms).expect("composition should succeed");

        assert_eq!(composed.match_pats.len(), 1);
        assert_eq!(composed.build_pats.len(), 1);
        assert_eq!(
            composed.match_pats[0], composed.build_pats[0],
            "Composition should be identity"
        );
        assert!(composed.drop_fresh.is_identity());
    }

    #[test]
    fn compose_ground_identity_with_rule_instantiates_vars() {
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

        let lhs = terms.app(
            f,
            smallvec::smallvec![
                terms.app(
                    f,
                    smallvec::smallvec![
                        terms.app(b, smallvec::smallvec![terms.var(0)]),
                        terms.var(1)
                    ]
                ),
                terms.var(2)
            ],
        );
        let rhs = terms.app(f, smallvec::smallvec![terms.var(0), terms.var(2)]);
        let rule = NF::factor(lhs, rhs, (), &mut terms);
        let identity = NF::factor(input, input, (), &mut terms);

        let composed = compose_nf(&identity, &rule, &mut terms).expect("compose should succeed");

        let expected_out = terms.app(f, smallvec::smallvec![b_l, c0]);
        assert_eq!(composed.match_pats[0], input);
        assert_eq!(composed.build_pats[0], expected_out);
    }
}
