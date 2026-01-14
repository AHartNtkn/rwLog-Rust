use crate::nf::{apply_var_renaming, collect_vars_ordered, NF};
use crate::subst::apply_subst;
use crate::term::{Term, TermId, TermStore};
#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};
use crate::unify::unify;
use crate::wire::Wire;
use smallvec::SmallVec;

/// Compose two NFs in sequence: a ; b
///
/// This computes the composition where:
/// - First, a's match patterns are matched against input
/// - Variables are routed through a's wire
/// - a's build patterns are constructed
/// - b's match patterns are matched against a's output
/// - Variables are routed through b's wire
/// - b's build patterns are constructed
///
/// Returns None if composition fails (unification failure at interface).
pub fn compose_nf<C: Default + Clone>(
    a: &NF<C>,
    b: &NF<C>,
    terms: &mut TermStore,
) -> Option<NF<C>> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!(
        "compose_nf",
        a_match_arity = a.match_pats.len(),
        a_build_arity = a.build_pats.len(),
        b_match_arity = b.match_pats.len(),
        b_build_arity = b.build_pats.len(),
        a_wire_in = a.wire.in_arity,
        a_wire_out = a.wire.out_arity,
        b_wire_in = b.wire.in_arity,
        b_wire_out = b.wire.out_arity,
    )
    .entered();

    // The key operation: unify a.build_pats with b.match_pats
    // This fuses RwR_a ; RwL_b into a single transformation.

    // For simplicity, we handle the single-pattern case.
    // Multi-pattern composition would iterate over pairs.
    if a.build_pats.len() != b.match_pats.len() {
        #[cfg(feature = "tracing")]
        trace!(
            a_build = a.build_pats.len(),
            b_match = b.match_pats.len(),
            "arity_mismatch"
        );
        return None; // Arity mismatch
    }

    if a.build_pats.is_empty() {
        // Both empty - compose the wires
        #[cfg(feature = "tracing")]
        trace!("empty_patterns_wire_compose");
        let wire = a.wire.compose(&b.wire)?;
        return Some(NF::new(
            a.match_pats.clone(),
            wire,
            b.build_pats.clone(),
        ));
    }

    // Single-pattern case (most common)
    let a_build = a.build_pats[0];
    let b_match = b.match_pats[0];

    // Rename variables in b's patterns to avoid collision with a's variables.
    // a uses vars 0..a.wire.out_arity (in build patterns)
    // b uses vars 0..b.wire.in_arity (in match patterns)
    // We'll shift b's vars by a.wire.out_arity.
    let b_var_offset = a.wire.out_arity;
    let b_match_shifted = shift_vars(b_match, b_var_offset, terms);

    #[cfg(feature = "tracing")]
    trace!(
        a_build = ?a_build,
        b_match_shifted = ?b_match_shifted,
        b_var_offset,
        "unifying_interface"
    );

    // Unify a's build pattern with b's (shifted) match pattern
    let mgu = match unify(a_build, b_match_shifted, terms) {
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

    // Apply the MGU to get the fused representation
    // The result pattern at the interface is the unified version.

    // Now we need to build the composed NF:
    // - match_pats: a's match patterns with vars substituted
    // - wire: composition that routes through both transformations
    // - build_pats: b's build patterns with vars substituted (and shifted back)

    // Apply substitution to a's match patterns
    let new_match = apply_subst(a.match_pats[0], &mgu, terms);

    // Apply substitution to b's build patterns (with shifted vars)
    let b_build_shifted = shift_vars(b.build_pats[0], b_var_offset, terms);
    let new_build = apply_subst(b_build_shifted, &mgu, terms);

    // Build the composed wire
    // This is complex: we need to track how input vars flow through to output vars.
    //
    // Input vars (from a.match) flow through:
    // 1. a.wire: some input vars map to interface vars
    // 2. Unification: interface vars get connected
    // 3. b.wire: interface vars map to output vars
    //
    // For now, let's compute the composed wire by tracing var connections.

    // Renumber the composed patterns to use fresh consecutive vars
    let (final_match, match_var_mapping) = renumber_term(new_match, terms);
    let (final_build, build_var_mapping) = renumber_term(new_build, terms);

    // Build wire connecting match vars to build vars
    // A var in match connects to a var in build if they're the same original var
    let mut wire_map: SmallVec<[(u32, u32); 4]> = SmallVec::new();

    for (i, &match_orig_var) in match_var_mapping.iter().enumerate() {
        if let Some(j) = build_var_mapping.iter().position(|&v| v == match_orig_var) {
            // Only add if it maintains monotonicity
            if wire_map.is_empty() || (wire_map.last().unwrap().1 < j as u32) {
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

    Some(NF::new(
        smallvec::smallvec![final_match],
        wire,
        smallvec::smallvec![final_build],
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
        Some(Term::Var(idx)) => {
            terms.var(idx + offset)
        }
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
/// Returns the renumbered term and the mapping from new index to original var.
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

    // ========== BASIC COMPOSITION TESTS ==========

    #[test]
    fn compose_identity_identity() {
        let (_, mut terms) = setup();
        let v0 = terms.var(0);

        // Identity NF: x -> x
        let identity: NF<()> = NF::new(
            smallvec::smallvec![v0],
            Wire::identity(1),
            smallvec::smallvec![v0],
        );

        let result = compose_nf(&identity, &identity, &mut terms);
        assert!(result.is_some());
        let composed = result.unwrap();

        // Identity composed with identity is identity
        assert_eq!(composed.match_pats.len(), 1);
        assert_eq!(composed.build_pats.len(), 1);
        assert!(composed.wire.is_identity());
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
            Wire::identity(0),
            smallvec::smallvec![b_term],
        );

        // Rule b: B -> C
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![b_term],
            Wire::identity(0),
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
            Wire::identity(0),
            smallvec::smallvec![b_term],
        );

        // Rule b: C -> A (doesn't match B)
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![c_term],
            Wire::identity(0),
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
            Wire::identity(1),
            smallvec::smallvec![v0],
        );

        // Rule b: x -> G(x) (wrap in G)
        let g_x = terms.app1(g, v0);
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![v0],
            Wire::identity(1),
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
            Wire::identity(1),
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
            Wire::identity(1),
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
            Wire {
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
            Wire::identity(1),
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
            Wire::identity(0),
            smallvec::smallvec![a_term],
        );

        // Rule b: x -> F(x) (wrap anything)
        let f_x = terms.app1(f, v0);
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![v0],
            Wire::identity(1),
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

        // Empty NFs with just wires
        let nf_a: NF<()> = NF::new(
            SmallVec::new(),
            Wire::identity(0),
            SmallVec::new(),
        );

        let nf_b: NF<()> = NF::new(
            SmallVec::new(),
            Wire::identity(0),
            SmallVec::new(),
        );

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
            Wire::identity(1),
            smallvec::smallvec![g_x],
        );

        // Rule b: G(x) -> H(x) (replace G with H)
        let h_x = terms.app1(h, v0);
        let rule_b: NF<()> = NF::new(
            smallvec::smallvec![g_x],
            Wire::identity(1),
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
}
