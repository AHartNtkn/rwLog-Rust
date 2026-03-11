mod common;

use common::*;

use proptest::prelude::*;
use rwlog::matching::match_terms_disjoint;
use rwlog::nf::apply_var_renaming;
use rwlog::subst::apply_subst;
use rwlog::symbol::SymbolStore;
use rwlog::term::{TermId, TermStore};

fn swap_vars(
    term: TermId,
    offset: u32,
    swap_a: u32,
    swap_b: u32,
    terms: &mut TermStore,
) -> TermId {
    if swap_a == swap_b {
        return term;
    }
    let max = offset + PROPTEST_MAX_VAR;
    let mut map = vec![None; max as usize + 1];
    let a = offset + swap_a;
    let b = offset + swap_b;
    map[a as usize] = Some(b);
    map[b as usize] = Some(a);
    apply_var_renaming(term, &map, terms)
}

fn matched_shape_pair(
    left: TermId,
    right: TermId,
    left_subst: &rwlog::subst::Subst,
    right_subst: &rwlog::subst::Subst,
    terms: &mut TermStore,
    symbols: &SymbolStore,
) -> (Shape, Shape) {
    let left_matched = apply_subst(left, left_subst, terms);
    let right_matched = apply_subst(right, right_subst, terms);
    pair_shape(left_matched, right_matched, terms, symbols)
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 64, .. ProptestConfig::default() })]

    #[test]
    fn match_invariant_under_rhs_renaming(
        lhs in raw_term_strategy(),
        rhs in raw_term_strategy(),
        swap_a in 0..=PROPTEST_MAX_VAR,
        swap_b in 0..=PROPTEST_MAX_VAR,
    ) {
        let symbols = SymbolStore::new();
        let mut terms = TermStore::new();
        let offset = PROPTEST_MAX_VAR + 7;

        let left = build_raw_term(&lhs, 0, &FUNCTOR_NAMES, &symbols, &terms);
        let right = build_raw_term(&rhs, offset, &FUNCTOR_NAMES, &symbols, &terms);
        let right_swapped = swap_vars(right, offset, swap_a, swap_b, &mut terms);

        let m1 = match_terms_disjoint(left, right, offset, &mut terms);
        let m2 = match_terms_disjoint(left, right_swapped, offset, &mut terms);

        assert_eq!(m1.is_some(), m2.is_some(), "renaming RHS vars should not change match existence");
        if let (Some((l1, r1)), Some((l2, r2))) = (m1, m2) {
            let shape1 = matched_shape_pair(left, right, &l1, &r1, &mut terms, &symbols);
            let shape2 = matched_shape_pair(left, right_swapped, &l2, &r2, &mut terms, &symbols);
            assert_eq!(shape1, shape2, "alpha-equivalent match expected");
        }
    }

    #[test]
    fn match_invariant_under_lhs_renaming(
        lhs in raw_term_strategy(),
        rhs in raw_term_strategy(),
        swap_a in 0..=PROPTEST_MAX_VAR,
        swap_b in 0..=PROPTEST_MAX_VAR,
    ) {
        let symbols = SymbolStore::new();
        let mut terms = TermStore::new();
        let offset = PROPTEST_MAX_VAR + 9;

        let left = build_raw_term(&lhs, 0, &FUNCTOR_NAMES, &symbols, &terms);
        let left_swapped = swap_vars(left, 0, swap_a, swap_b, &mut terms);
        let right = build_raw_term(&rhs, offset, &FUNCTOR_NAMES, &symbols, &terms);

        let m1 = match_terms_disjoint(left, right, offset, &mut terms);
        let m2 = match_terms_disjoint(left_swapped, right, offset, &mut terms);

        assert_eq!(m1.is_some(), m2.is_some(), "renaming LHS vars should not change match existence");
        if let (Some((l1, r1)), Some((l2, r2))) = (m1, m2) {
            let shape1 = matched_shape_pair(left, right, &l1, &r1, &mut terms, &symbols);
            let shape2 = matched_shape_pair(left_swapped, right, &l2, &r2, &mut terms, &symbols);
            assert_eq!(shape1, shape2, "alpha-equivalent match expected");
        }
    }
}
