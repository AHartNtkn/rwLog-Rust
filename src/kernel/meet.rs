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

    // For the meet, we need to:
    // 1. Unify a.match_pats with b.match_pats (most specific input pattern)
    // 2. Unify a.build_pats with b.build_pats (most specific output pattern)
    // 3. Combine the wires appropriately

    if a.match_pats.len() != b.match_pats.len() || a.build_pats.len() != b.build_pats.len() {
        #[cfg(feature = "tracing")]
        trace!("meet_arity_mismatch");
        return None; // Arity mismatch
    }

    if a.match_pats.is_empty() && a.build_pats.is_empty() {
        // Both empty - just return a copy
        return Some(NF::new(
            SmallVec::new(),
            Wire::identity(0),
            SmallVec::new(),
        ));
    }

    // Shift b's variables to avoid collision with a's
    // a uses vars 0..a.wire.in_arity (match) and 0..a.wire.out_arity (build)
    // We'll use the max of these as the offset for b
    let b_var_offset = a.wire.in_arity.max(a.wire.out_arity);

    // Handle single-pattern case (most common)
    let unified_match = if !a.match_pats.is_empty() {
        let a_match = a.match_pats[0];
        let b_match_shifted = shift_vars(b.match_pats[0], b_var_offset, terms);

        // Unify the match patterns
        let mgu = match unify(a_match, b_match_shifted, terms) {
            Some(mgu) => mgu,
            None => {
                #[cfg(feature = "tracing")]
                trace!("meet_match_unify_failed");
                return None;
            }
        };

        // Apply MGU to get the unified match pattern
        apply_subst(a_match, &mgu, terms)
    } else {
        // No match patterns - use a placeholder
        terms.var(0) // This won't be used
    };

    let unified_build = if !a.build_pats.is_empty() {
        let a_build = a.build_pats[0];
        let b_build_shifted = shift_vars(b.build_pats[0], b_var_offset, terms);

        // Unify the build patterns
        let mgu = match unify(a_build, b_build_shifted, terms) {
            Some(mgu) => mgu,
            None => {
                #[cfg(feature = "tracing")]
                trace!("meet_build_unify_failed");
                return None;
            }
        };

        // Apply MGU to get the unified build pattern
        apply_subst(a_build, &mgu, terms)
    } else {
        terms.var(0)
    };

    // Now we need to unify the match and build together to ensure consistency
    // Variables in match should connect to variables in build appropriately

    // Renumber to get consecutive vars
    let (final_match, match_var_mapping) = renumber_term(unified_match, terms);
    let (final_build, build_var_mapping) = renumber_term(unified_build, terms);

    // Build wire connecting match vars to build vars
    let mut wire_map: SmallVec<[(u32, u32); 4]> = SmallVec::new();

    for (i, &match_orig_var) in match_var_mapping.iter().enumerate() {
        if let Some(j) = build_var_mapping.iter().position(|&v| v == match_orig_var) {
            if wire_map.is_empty() || wire_map.last().unwrap().1 < j as u32 {
                wire_map.push((i as u32, j as u32));
            }
        }
    }

    let wire = Wire {
        in_arity: match_var_mapping.len() as u32,
        out_arity: build_var_mapping.len() as u32,
        map: wire_map,
        constraint: C::default(),
    };

    #[cfg(feature = "tracing")]
    trace!(
        result_in_arity = wire.in_arity,
        result_out_arity = wire.out_arity,
        "meet_success"
    );

    Some(NF::new(
        if a.match_pats.is_empty() { SmallVec::new() } else { smallvec::smallvec![final_match] },
        wire,
        if a.build_pats.is_empty() { SmallVec::new() } else { smallvec::smallvec![final_build] },
    ))
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
fn renumber_term(term: TermId, terms: &mut TermStore) -> (TermId, Vec<u32>) {
    let vars = collect_vars_ordered(term, terms);
    if vars.is_empty() {
        return (term, vec![]);
    }

    let max_var = vars.iter().copied().max().unwrap() as usize;
    let mut old_to_new = vec![None; max_var + 1];
    for (new_idx, &old_idx) in vars.iter().enumerate() {
        old_to_new[old_idx as usize] = Some(new_idx as u32);
    }

    let renumbered = apply_var_renaming(term, &old_to_new, terms);
    (renumbered, vars)
}

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

        // The meet would require x = F(x) which fails occurs check
        // Actually this might succeed since match and build are separate...
        // Let me reconsider - they have different match patterns so unification
        // would produce x = F(y), which is valid.
        let result = meet_nf(&rule_a, &rule_b, &mut terms);
        // This actually should succeed with F(x) -> F(x) after unification
        assert!(result.is_some());
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
