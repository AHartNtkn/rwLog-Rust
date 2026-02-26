use crate::constraint::ConstraintOps;
use crate::nf::{collect_tensor, factor_tensor_with_subst, SubstParams, NF};
use crate::perf_counters;
use crate::term::{Term, TermStore};
#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};
use std::hash::{Hash, Hasher};

use super::util::{
    build_remap_map, match_term_lists_shifted_combined,
    match_term_lists_shifted_with_left_renaming_combined, pre_create_shifted_vars,
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
/// Returns None if composition fails (matching failure at interface).
pub fn compose_nf<C: ConstraintOps>(a: &NF<C>, b: &NF<C>, terms: &mut TermStore) -> Option<NF<C>> {
    if perf_counters::is_enabled() {
        let mut h = rustc_hash::FxHasher::default();
        a.hash(&mut h);
        b.hash(&mut h);
        perf_counters::record_compose_pair_hash(h.finish());
    }
    let result = compose_nf_impl(a, b, terms);
    perf_counters::record_compose_result(result.is_some());
    result
}

fn compose_nf_impl<C: ConstraintOps>(a: &NF<C>, b: &NF<C>, terms: &mut TermStore) -> Option<NF<C>> {
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

    // Root functor precheck: if the first build pattern of `a` and the first match
    // pattern of `b` are both App nodes with different root functors, composition
    // must fail (match_term_lists_shifted would fail at the first term). This avoids
    // the cost of collect_tensor, pre_create_shifted_vars, and match_term_lists_shifted
    // for incompatible pairs. Uses get_unlocked for zero-overhead access.
    if !a.build_pats.is_empty() {
        let a_root = match terms.get_unlocked(a.build_pats[0]) {
            Some(Term::App(f, _)) => Some(*f),
            _ => None, // Variable-rooted or missing: skip precheck
        };
        let b_root = match terms.get_unlocked(b.match_pats[0]) {
            Some(Term::App(f, _)) => Some(*f),
            _ => None, // Variable-rooted or missing: skip precheck
        };
        if let (Some(af), Some(bf)) = (a_root, b_root) {
            if af != bf {
                return None;
            }
        }
    }

    // Compute max var indices from NF metadata in O(1), avoiding term tree walks.
    let b_max_var = b.rwt_max_var();
    let b_var_offset = a.rwt_max_var().map(|v| v + 1).unwrap_or(0);

    // Pre-create shifted variable TermIds for virtual shifting (avoids physical tree rewriting).
    let shifted_vars = pre_create_shifted_vars(b_max_var, b_var_offset, terms);

    #[cfg(feature = "tracing")]
    trace!(
        a_build = ?a.build_pats,
        b_match = ?b.match_pats,
        b_var_offset,
        "matching_interface"
    );

    // Match a's build patterns against b's match patterns using inline renaming.
    // This avoids the tree walk of collect_tensor(a) for the 99%+ of compose
    // attempts that fail matching. The a-side variables are renamed inline via
    // the cached_rhs_map instead of eagerly applying apply_var_renaming_list.
    // b's match_pats are used directly (no renaming needed, same as rw2.lhs).
    //
    // We return the combined substitution directly (no split_match_subst),
    // avoiding the cost of walking all bindings and calling apply_subst on each.
    // The combined subst has left-side vars at indices < b_var_offset and
    // right-side vars at indices >= b_var_offset. Consumers resolve chains
    // lazily through apply_subst's natural chain following.
    let combined_subst = match if a.cached_rhs_identity {
        match_term_lists_shifted_combined(
            &a.build_pats,
            &b.match_pats,
            b_var_offset,
            &shifted_vars,
            terms,
        )
    } else {
        match_term_lists_shifted_with_left_renaming_combined(
            &a.build_pats,
            &b.match_pats,
            &a.cached_rhs_map,
            &a.cached_rhs_map_opt,
            b_var_offset,
            &shifted_vars,
            terms,
        )
    } {
        Some(subst) => {
            #[cfg(feature = "tracing")]
            trace!(bindings = subst.len(), "matching_success");
            subst
        }
        None => {
            #[cfg(feature = "tracing")]
            trace!("matching_failed");
            return None;
        }
    };

    // Apply the combined subst directly to constraints. Each constraint's args
    // only reference variables from their own side, so the extra bindings for
    // the other side are simply never accessed. Chain resolution through
    // apply_subst naturally follows cross-side bindings when needed.
    let a_constraint = a.drop_fresh.constraint.apply_subst(&combined_subst, terms);
    let b_constraint =
        match build_remap_map(&b.drop_fresh.constraint, b_max_var, b_var_offset, terms) {
            Some(map) => {
                b.drop_fresh
                    .constraint
                    .remap_and_apply_subst(&map, &combined_subst, terms)
            }
            None => b.drop_fresh.constraint.apply_subst(&combined_subst, terms),
        };

    let combined_constraint = match a_constraint.combine_owned(b_constraint) {
        Some(c) => c,
        None => {
            #[cfg(feature = "tracing")]
            trace!("compose_constraint_conflict");
            return None;
        }
    };

    let (normalized, subst_opt) = match combined_constraint.normalize_owned(terms) {
        Some(result) => result,
        None => {
            #[cfg(feature = "tracing")]
            trace!("compose_constraint_unsat");
            return None;
        }
    };
    // Success path: compute the RHS of b via collect_tensor (only for successes).
    // a's LHS is just a.match_pats (no renaming needed).
    // b's RHS needs the rhs_map applied via collect_tensor.
    let rw2 = collect_tensor(b, terms);

    // Use fused factor_tensor_with_subst to avoid creating intermediate
    // substituted terms. The original patterns (a.match_pats, rw2.rhs) are passed
    // directly along with the substitutions, and factor_tensor_with_subst
    // resolves variables through the substitutions during its collect+renumber
    // passes, eliminating the need for apply_subst_list + apply_subst_shifted_list.
    //
    // Both lhs and rhs use the same combined_subst. The lhs patterns only
    // contain left-side vars (< b_var_offset), and the rhs patterns only
    // contain right-side vars (>= b_var_offset), so each side naturally
    // resolves only its own bindings through the combined subst.
    let rhs_shifted = b_var_offset > 0 && !shifted_vars.is_empty();
    let lhs_params = SubstParams {
        subst: &combined_subst,
        subst2: subst_opt.as_ref(),
        shifted: false,
        shifted_vars: &[],
    };
    let rhs_params = SubstParams {
        subst: &combined_subst,
        subst2: subst_opt.as_ref(),
        shifted: rhs_shifted,
        shifted_vars: &shifted_vars,
    };
    let result = factor_tensor_with_subst(
        &a.match_pats,
        &lhs_params,
        &rw2.rhs,
        &rhs_params,
        normalized,
        terms,
    );
    Some(result)
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
    fn compose_applies_match_subst_to_constraints() {
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
    fn compose_preserves_constraint_only_vars() {
        let mut parser = Parser::with_chr();
        let theory = r#"
theory t {
  constraint p/1
}
"#;
        parser.parse_theory_def(theory).expect("parse theory");
        let identity = parser.parse_rule("$x -> $x").expect("parse identity");
        let constrained = parser
            .parse_rule("$x { (p $y) } -> $x")
            .expect("parse constrained rule");
        let expected = parser
            .parse_rule("$x { (p $y) } -> $x")
            .expect("parse expected rule");
        let mut terms = parser.take_terms();

        let composed = compose_nf(&identity, &constrained, &mut terms)
            .expect("compose identity with constrained rule");
        assert!(
            composed == expected,
            "Constraint-only variables must remain fresh under composition"
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
        let store = state.store();
        let alive: Vec<_> = store.inst.iter().filter(|inst| inst.alive).collect();
        assert_eq!(alive.len(), 1, "expected one no_c constraint");
        let inst = alive[0];
        let inst_args = store.args(inst);
        assert_eq!(inst.pred, pred, "expected no_c constraint");
        assert_eq!(inst_args.len(), 1, "no_c should have one arg");
        assert!(
            terms.is_var(inst_args[0]).is_some(),
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
            "Composition should succeed: variable $0 should match with ground z"
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
            "Composition should succeed: variable $0 should match with (s z)"
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
    fn compose_var_with_ground_matches() {
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

        assert!(result.is_some(), "Variable should match with ground term");
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
