mod common;

use common::*;

use proptest::prelude::*;
use rwlog::matching::match_terms_disjoint;
use rwlog::nf::apply_var_renaming;
use rwlog::subst::apply_subst;
use rwlog::symbol::SymbolStore;
use rwlog::term::{TermId, TermStore};
use smallvec::SmallVec;

const MAX_VAR: u32 = 4;
const FUNCTOR_NAMES: [&str; 5] = ["a", "b", "c", "f", "g"];

#[derive(Clone, Debug)]
enum RawTerm {
    Var(u32),
    App { f: usize, kids: Vec<RawTerm> },
}

fn raw_term_strategy() -> impl Strategy<Value = RawTerm> {
    let leaf = prop_oneof![
        (0..=MAX_VAR).prop_map(RawTerm::Var),
        Just(RawTerm::App { f: 0, kids: vec![] }),
        Just(RawTerm::App { f: 1, kids: vec![] }),
        Just(RawTerm::App { f: 2, kids: vec![] }),
    ];

    leaf.prop_recursive(3, 16, 4, |inner| {
        prop_oneof![
            inner.clone().prop_map(|t| RawTerm::App {
                f: 3,
                kids: vec![t]
            }),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| RawTerm::App {
                f: 4,
                kids: vec![a, b],
            }),
        ]
    })
}

fn build_term(raw: &RawTerm, var_offset: u32, symbols: &SymbolStore, terms: &TermStore) -> TermId {
    match raw {
        RawTerm::Var(v) => terms.var(*v + var_offset),
        RawTerm::App { f, kids } => {
            let func = symbols.intern(FUNCTOR_NAMES[*f]);
            let mut child_ids: SmallVec<[TermId; 4]> = SmallVec::new();
            for kid in kids {
                child_ids.push(build_term(kid, var_offset, symbols, terms));
            }
            terms.app(func, child_ids)
        }
    }
}

fn swap_right_vars(
    term: TermId,
    right_offset: u32,
    swap_a: u32,
    swap_b: u32,
    terms: &mut TermStore,
) -> TermId {
    if swap_a == swap_b {
        return term;
    }
    let max = right_offset + MAX_VAR;
    let mut map = vec![None; max as usize + 1];
    for i in 0..=max {
        map[i as usize] = Some(i);
    }
    let a = right_offset + swap_a;
    let b = right_offset + swap_b;
    map[a as usize] = Some(b);
    map[b as usize] = Some(a);
    apply_var_renaming(term, &map, terms)
}

fn swap_left_vars(term: TermId, swap_a: u32, swap_b: u32, terms: &mut TermStore) -> TermId {
    if swap_a == swap_b {
        return term;
    }
    let max = MAX_VAR;
    let mut map = vec![None; max as usize + 1];
    for i in 0..=max {
        map[i as usize] = Some(i);
    }
    map[swap_a as usize] = Some(swap_b);
    map[swap_b as usize] = Some(swap_a);
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
        swap_a in 0..=MAX_VAR,
        swap_b in 0..=MAX_VAR,
    ) {
        let symbols = SymbolStore::new();
        let mut terms = TermStore::new();
        let offset = MAX_VAR + 7;

        let left = build_term(&lhs, 0, &symbols, &terms);
        let right = build_term(&rhs, offset, &symbols, &terms);
        let right_swapped = swap_right_vars(right, offset, swap_a, swap_b, &mut terms);

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
        swap_a in 0..=MAX_VAR,
        swap_b in 0..=MAX_VAR,
    ) {
        let symbols = SymbolStore::new();
        let mut terms = TermStore::new();
        let offset = MAX_VAR + 9;

        let left = build_term(&lhs, 0, &symbols, &terms);
        let left_swapped = swap_left_vars(left, swap_a, swap_b, &mut terms);
        let right = build_term(&rhs, offset, &symbols, &terms);

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
