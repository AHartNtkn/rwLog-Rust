use crate::nf::{apply_var_renaming, collect_vars_ordered, NF};
use crate::subst::apply_subst;
use crate::term::{Term, TermId, TermStore};
use crate::unify::unify;
use crate::wire::Wire;
use smallvec::SmallVec;

#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};

/// Compute the meet (intersection) of two NFs.
///
/// The meet represents the relation that satisfies BOTH a AND b.
/// For inputs, this means the input must match both a's and b's match patterns.
/// For outputs, this means the output must satisfy both a's and b's build patterns.
///
/// Returns None if the meet is empty (patterns are incompatible).
pub fn meet_nf<C: Default + Clone>(
    a: &NF<C>,
    b: &NF<C>,
    terms: &mut TermStore,
) -> Option<NF<C>> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!(
        "meet_nf",
        a_match_arity = a.match_pats.len(),
        a_build_arity = a.build_pats.len(),
        b_match_arity = b.match_pats.len(),
        b_build_arity = b.build_pats.len(),
    )
    .entered();

    // For the meet, we need to unify direct-rule forms so that wires are honored.
    if a.match_pats.len() != b.match_pats.len() || a.build_pats.len() != b.build_pats.len() {
        #[cfg(feature = "tracing")]
        trace!("meet_arity_mismatch");
        return None;
    }

    if a.match_pats.is_empty() && a.build_pats.is_empty() {
        return Some(NF::new(
            SmallVec::new(),
            Wire::identity(0),
            SmallVec::new(),
        ));
    }

    let (a_lhs, a_rhs) = direct_rule_terms(a, terms)?;
    let (b_lhs, b_rhs) = direct_rule_terms(b, terms)?;

    let b_var_offset = max_var_index(a_lhs, terms)
        .max(max_var_index(a_rhs, terms))
        .map(|v| v + 1)
        .unwrap_or(0);

    let b_lhs_shifted = shift_vars(b_lhs, b_var_offset, terms);
    let b_rhs_shifted = shift_vars(b_rhs, b_var_offset, terms);

    let mgu_match = match unify(a_lhs, b_lhs_shifted, terms) {
        Some(mgu) => mgu,
        None => {
            #[cfg(feature = "tracing")]
            trace!("meet_match_unify_failed");
            return None;
        }
    };

    let unified_lhs = apply_subst(a_lhs, &mgu_match, terms);
    let a_rhs_subst = apply_subst(a_rhs, &mgu_match, terms);
    let b_rhs_subst = apply_subst(b_rhs_shifted, &mgu_match, terms);

    let mgu_build = match unify(a_rhs_subst, b_rhs_subst, terms) {
        Some(mgu) => mgu,
        None => {
            #[cfg(feature = "tracing")]
            trace!("meet_build_unify_failed");
            return None;
        }
    };

    let final_lhs = apply_subst(unified_lhs, &mgu_build, terms);
    let final_rhs = apply_subst(a_rhs_subst, &mgu_build, terms);

    #[cfg(feature = "tracing")]
    trace!("meet_success");

    Some(NF::factor(final_lhs, final_rhs, C::default(), terms))
}

fn direct_rule_terms<C: Clone>(nf: &NF<C>, terms: &mut TermStore) -> Option<(TermId, TermId)> {
    if nf.match_pats.len() != 1 || nf.build_pats.len() != 1 {
        return None;
    }

    let lhs = nf.match_pats[0];
    let rhs = nf.build_pats[0];
    let out_arity = nf.wire.out_arity as usize;
    let in_arity = nf.wire.in_arity as u32;

    let mut rhs_map: Vec<Option<u32>> = vec![None; out_arity];
    for (i, j) in nf.wire.map.iter().copied() {
        if let Some(slot) = rhs_map.get_mut(j as usize) {
            *slot = Some(i);
        }
    }

    let mut next_var = in_arity;
    for slot in rhs_map.iter_mut() {
        if slot.is_none() {
            *slot = Some(next_var);
            next_var += 1;
        }
    }

    let rhs_direct = apply_var_renaming(rhs, &rhs_map, terms);
    Some((lhs, rhs_direct))
}

fn max_var_index(term: TermId, terms: &mut TermStore) -> Option<u32> {
    collect_vars_ordered(term, terms).into_iter().max()
}

/// Shift all variables in a term by a given offset.
fn shift_vars(term: TermId, offset: u32, terms: &mut TermStore) -> TermId {
    if offset == 0 {
        return term;
    }
    shift_vars_helper(term, offset, terms)
}

fn shift_vars_helper(term: TermId, offset: u32, terms: &mut TermStore) -> TermId {
    match terms.resolve(term) {
        Some(Term::Var(idx)) => terms.var(idx + offset),
        Some(Term::App(func, children)) => {
            let new_children: SmallVec<[TermId; 4]> = children
                .iter()
                .map(|&c| shift_vars_helper(c, offset, terms))
                .collect();
            terms.app(func, new_children)
        }
        None => term,
    }
}

/// Renumber variables in a term to consecutive indices 0..n-1.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::SymbolStore;

    fn setup() -> (SymbolStore, TermStore) {
        (SymbolStore::new(), TermStore::new())
    }

    // ========== BASIC MEET TESTS ==========

    #[test]
    fn meet_identical_identity() {
        let (_, mut terms) = setup();
        let v0 = terms.var(0);

        // Identity NF: x -> x
        let identity: NF<()> = NF::new(
            smallvec::smallvec![v0],
            Wire::identity(1),
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
    fn meet_identical_ground_rules() {
        let (symbols, mut terms) = setup();
        let a = symbols.intern("A");
        let b = symbols.intern("B");

        let a_term = terms.app0(a);
        let b_term = terms.app0(b);

        // Rule: A -> B
        let rule: NF<()> = NF::new(
            smallvec::smallvec![a_term],
            Wire::identity(0),
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
            Wire::identity(1),
            smallvec::smallvec![v0],
        );

        // Rule b: F(x) -> F(x) (identity on F terms)
        let f_x = terms.app1(f, v0);
        let f_rule: NF<()> = NF::new(
            smallvec::smallvec![f_x],
            Wire::identity(1),
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
            Wire::identity(0),
            smallvec::smallvec![b_term],
        );

        // Rule b: C -> B (different match pattern)
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![c_term],
            Wire::identity(0),
            smallvec::smallvec![b_term],
        );

        let result = meet_nf(&rule_a, &rule_b, &mut terms);
        assert!(result.is_none(), "A and C don't unify, meet should fail");
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
            Wire::identity(0),
            smallvec::smallvec![b_term],
        );

        // Rule b: A -> C (same match, different build)
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![a_term],
            Wire::identity(0),
            smallvec::smallvec![c_term],
        );

        let result = meet_nf(&rule_a, &rule_b, &mut terms);
        assert!(result.is_none(), "B and C don't unify, meet should fail");
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
            Wire::identity(1),
            smallvec::smallvec![g_x],
        );

        // Rule b: F(A) -> G(A)
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![f_a],
            Wire::identity(0),
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
            Wire::identity(1),
            smallvec::smallvec![g_x],
        );

        // Rule b: F(G(y)) -> G(G(y))
        let g_y = terms.app1(g, v0);
        let f_g_y = terms.app1(f, g_y);
        let g_g_y = terms.app1(g, g_y);
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![f_g_y],
            Wire::identity(1),
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
            Wire::identity(1),
            smallvec::smallvec![f_x],
        );

        // Rule b: F(A) -> F(A)
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![f_a],
            Wire::identity(0),
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

        let empty: NF<()> = NF::new(
            SmallVec::new(),
            Wire::identity(0),
            SmallVec::new(),
        );

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
            Wire::identity(2),
            smallvec::smallvec![pair_xy],
        );

        // Rule b: Pair(x, x) -> Pair(x, x) (diagonal)
        let pair_xx = terms.app2(pair, v0, v0);
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![pair_xx],
            Wire::identity(1),
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
            Wire::identity(1),
            smallvec::smallvec![v0],
        );

        // Rule b: F(G(x)) -> F(G(x))
        let g_x = terms.app1(g, v0);
        let f_g_x = terms.app1(f, g_x);
        let complex: NF<()> = NF::new(
            smallvec::smallvec![f_g_x],
            Wire::identity(1),
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
            Wire::identity(1),
            smallvec::smallvec![f_x],
        );

        // Rule b: F(x) -> x
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![f_x],
            Wire::identity(1),
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
            Wire::identity(3),
            smallvec::smallvec![t_xyz],
        );

        // Rule b: Triple(x, x, y) -> Triple(x, x, y) (first two equal)
        let triple_xxy: SmallVec<[TermId; 4]> = smallvec::smallvec![v0, v0, v1];
        let t_xxy = terms.app(triple, triple_xxy);
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![t_xxy],
            Wire::identity(2),
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
            Wire::identity(1),
            smallvec::smallvec![base_term],
        );

        // General query: Append(xs, ys, zs)
        let query_args: SmallVec<[TermId; 4]> = smallvec::smallvec![v0, v1, v2];
        let query_term = terms.app(append, query_args);
        let query: NF<()> = NF::new(
            smallvec::smallvec![query_term],
            Wire::identity(3),
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
}
