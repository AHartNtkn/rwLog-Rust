mod common;

use common::{build_raw_term, RawTerm, PROPTEST_MAX_VAR};
use proptest::prelude::*;
use rwlog::constraint::ConstraintOps;
use rwlog::kernel::{compose_nf, dual_nf, meet_nf};
use rwlog::nf::{collect_tensor, factor_tensor, NF};
use rwlog::symbol::SymbolStore;
use rwlog::term::TermStore;

const FUNCTOR_NAMES: [&str; 6] = ["a", "b", "c", "f", "g", "h"];

fn raw_term_strategy() -> impl Strategy<Value = RawTerm> {
    let leaf = prop_oneof![
        (0..=PROPTEST_MAX_VAR).prop_map(RawTerm::Var),
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
            (inner.clone(), inner).prop_map(|(a, b)| RawTerm::App {
                f: 5,
                kids: vec![a, b],
            }),
        ]
    })
}

fn build_nf(lhs: &RawTerm, rhs: &RawTerm, symbols: &SymbolStore, terms: &mut TermStore) -> NF<()> {
    let lhs_id = build_raw_term(lhs, 0, &FUNCTOR_NAMES, symbols, terms);
    let rhs_id = build_raw_term(rhs, 0, &FUNCTOR_NAMES, symbols, terms);
    NF::factor(lhs_id, rhs_id, (), terms)
}

fn canonicalize_nf<C: ConstraintOps + Clone>(nf: &NF<C>, terms: &mut TermStore) -> NF<C> {
    let direct = collect_tensor(nf, terms);
    factor_tensor(direct.lhs, direct.rhs, direct.constraint, terms)
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 256, .. ProptestConfig::default() })]

    #[test]
    fn dual_is_involution(lhs in raw_term_strategy(), rhs in raw_term_strategy()) {
        let mut terms = TermStore::new();
        let symbols = SymbolStore::new();
        let nf = build_nf(&lhs, &rhs, &symbols, &mut terms);

        let dual = dual_nf(&nf, &mut terms);
        let dual_dual = dual_nf(&dual, &mut terms);
        let canon_nf = canonicalize_nf(&nf, &mut terms);
        let canon_dual_dual = canonicalize_nf(&dual_dual, &mut terms);
        prop_assert_eq!(canon_dual_dual, canon_nf);
    }

    #[test]
    fn compose_dual_law(
        a_lhs in raw_term_strategy(),
        a_rhs in raw_term_strategy(),
        b_lhs in raw_term_strategy(),
        b_rhs in raw_term_strategy(),
    ) {
        let mut terms = TermStore::new();
        let symbols = SymbolStore::new();

        let a = build_nf(&a_lhs, &a_rhs, &symbols, &mut terms);
        let b = build_nf(&b_lhs, &b_rhs, &symbols, &mut terms);

        let composed = compose_nf(&a, &b, &mut terms);
        let dual_composed = composed
            .as_ref()
            .map(|nf| canonicalize_nf(&dual_nf(nf, &mut terms), &mut terms));

        let dual_a = canonicalize_nf(&dual_nf(&a, &mut terms), &mut terms);
        let dual_b = canonicalize_nf(&dual_nf(&b, &mut terms), &mut terms);
        let composed_duals = compose_nf(&dual_b, &dual_a, &mut terms)
            .map(|nf| canonicalize_nf(&nf, &mut terms));

        prop_assert_eq!(dual_composed.is_some(), composed_duals.is_some());
        if let (Some(left), Some(right)) = (dual_composed, composed_duals) {
            prop_assert_eq!(left, right);
        }
    }

    #[test]
    fn meet_dual_law(
        a_lhs in raw_term_strategy(),
        a_rhs in raw_term_strategy(),
        b_lhs in raw_term_strategy(),
        b_rhs in raw_term_strategy(),
    ) {
        let mut terms = TermStore::new();
        let symbols = SymbolStore::new();

        let a = build_nf(&a_lhs, &a_rhs, &symbols, &mut terms);
        let b = build_nf(&b_lhs, &b_rhs, &symbols, &mut terms);

        let met = meet_nf(&a, &b, &mut terms);
        let dual_met = met
            .as_ref()
            .map(|nf| canonicalize_nf(&dual_nf(nf, &mut terms), &mut terms));

        let dual_a = canonicalize_nf(&dual_nf(&a, &mut terms), &mut terms);
        let dual_b = canonicalize_nf(&dual_nf(&b, &mut terms), &mut terms);
        let met_duals = meet_nf(&dual_a, &dual_b, &mut terms)
            .map(|nf| canonicalize_nf(&nf, &mut terms));

        prop_assert_eq!(dual_met.is_some(), met_duals.is_some());
        if let (Some(left), Some(right)) = (dual_met, met_duals) {
            prop_assert_eq!(left, right);
        }
    }
}
