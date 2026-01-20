use proptest::prelude::*;
use rwlog::constraint::{ConstraintOps, TypeConstraints};
use rwlog::kernel::{compose_nf, dual_nf, meet_nf};
use rwlog::nf::{collect_tensor, factor_tensor, NF};
use rwlog::symbol::SymbolStore;
use rwlog::term::{TermId, TermStore};
use smallvec::SmallVec;

const MAX_VAR: u32 = 4;
const VAR_COUNT: usize = (MAX_VAR as usize) + 1;

const FUNCTOR_NAMES: [&str; 6] = ["a", "b", "c", "f", "g", "h"];

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
            (inner.clone(), inner).prop_map(|(a, b)| RawTerm::App {
                f: 5,
                kids: vec![a, b],
            }),
        ]
    })
}

prop_compose! {
    fn nf_parts_strategy()
        (
            lhs in raw_term_strategy(),
            rhs in raw_term_strategy(),
            types in prop::collection::vec(0u32..3, VAR_COUNT..=VAR_COUNT),
            flags in prop::collection::vec(any::<bool>(), VAR_COUNT..=VAR_COUNT),
        )
        -> (RawTerm, RawTerm, Vec<u32>, Vec<bool>)
    {
        (lhs, rhs, types, flags)
    }
}

fn build_term(raw: &RawTerm, symbols: &SymbolStore, terms: &TermStore) -> TermId {
    match raw {
        RawTerm::Var(v) => terms.var(*v),
        RawTerm::App { f, kids } => {
            let func = symbols.intern(FUNCTOR_NAMES[*f]);
            let mut child_ids: SmallVec<[TermId; 4]> = SmallVec::new();
            for kid in kids {
                child_ids.push(build_term(kid, symbols, terms));
            }
            terms.app(func, child_ids)
        }
    }
}

fn mark_vars(raw: &RawTerm, used: &mut [bool]) {
    match raw {
        RawTerm::Var(v) => {
            let idx = *v as usize;
            if idx < used.len() {
                used[idx] = true;
            }
        }
        RawTerm::App { kids, .. } => {
            for kid in kids {
                mark_vars(kid, used);
            }
        }
    }
}

fn build_constraint(
    used: &[bool],
    types: &[u32],
    flags: &[bool],
    terms: &TermStore,
) -> TypeConstraints {
    let mut c = TypeConstraints::new();
    for (idx, is_used) in used.iter().copied().enumerate() {
        if is_used && flags[idx] {
            c.add(terms.var(idx as u32), types[idx]);
        }
    }
    c
}

fn build_nf(
    lhs: &RawTerm,
    rhs: &RawTerm,
    types: &[u32],
    flags: &[bool],
    symbols: &SymbolStore,
    terms: &mut TermStore,
) -> NF<TypeConstraints> {
    let lhs_id = build_term(lhs, symbols, terms);
    let rhs_id = build_term(rhs, symbols, terms);
    let mut used = vec![false; VAR_COUNT];
    mark_vars(lhs, &mut used);
    mark_vars(rhs, &mut used);
    let constraint = build_constraint(&used, types, flags, terms);
    NF::factor(lhs_id, rhs_id, constraint, terms)
}

fn canonicalize_nf<C: ConstraintOps + Clone>(nf: &NF<C>, terms: &mut TermStore) -> NF<C> {
    let direct = collect_tensor(nf, terms);
    factor_tensor(direct.lhs, direct.rhs, direct.constraint, terms)
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 256, .. ProptestConfig::default() })]

    #[test]
    fn dual_is_involution(parts in nf_parts_strategy()) {
        let mut terms = TermStore::new();
        let symbols = SymbolStore::new();
        let (lhs, rhs, types, flags) = parts;
        let nf = build_nf(&lhs, &rhs, &types, &flags, &symbols, &mut terms);

        let dual = dual_nf(&nf, &mut terms);
        let dual_dual = dual_nf(&dual, &mut terms);
        let canon_nf = canonicalize_nf(&nf, &mut terms);
        let canon_dual_dual = canonicalize_nf(&dual_dual, &mut terms);
        prop_assert_eq!(canon_dual_dual, canon_nf);
    }

    #[test]
    fn compose_dual_law(
        a_parts in nf_parts_strategy(),
        b_parts in nf_parts_strategy()
    ) {
        let mut terms = TermStore::new();
        let symbols = SymbolStore::new();
        let (a_lhs, a_rhs, a_types, a_flags) = a_parts;
        let (b_lhs, b_rhs, b_types, b_flags) = b_parts;

        let a = build_nf(&a_lhs, &a_rhs, &a_types, &a_flags, &symbols, &mut terms);
        let b = build_nf(&b_lhs, &b_rhs, &b_types, &b_flags, &symbols, &mut terms);

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
        a_parts in nf_parts_strategy(),
        b_parts in nf_parts_strategy()
    ) {
        let mut terms = TermStore::new();
        let symbols = SymbolStore::new();
        let (a_lhs, a_rhs, a_types, a_flags) = a_parts;
        let (b_lhs, b_rhs, b_types, b_flags) = b_parts;

        let a = build_nf(&a_lhs, &a_rhs, &a_types, &a_flags, &symbols, &mut terms);
        let b = build_nf(&b_lhs, &b_rhs, &b_types, &b_flags, &symbols, &mut terms);

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
