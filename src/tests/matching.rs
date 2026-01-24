use crate::matching::{match_terms_disjoint, Matching};
use crate::subst::apply_subst;
use crate::term::{Term, TermId, TermStore};
use crate::test_utils::setup;
use proptest::prelude::*;
use smallvec::SmallVec;

fn max_var(term: TermId, terms: &TermStore) -> Option<u32> {
    let mut max: Option<u32> = None;
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        match terms.resolve(t) {
            Some(Term::Var(idx)) => {
                max = Some(match max {
                    Some(m) => m.max(idx),
                    None => idx,
                });
            }
            Some(Term::App(_, kids)) => {
                for kid in kids.iter() {
                    stack.push(*kid);
                }
            }
            None => {}
        }
    }
    max
}

fn right_offset_for(left: TermId, terms: &TermStore) -> u32 {
    max_var(left, terms).map(|v| v + 1).unwrap_or(0)
}

fn shift_term(term: TermId, offset: u32, terms: &TermStore) -> TermId {
    match terms.resolve(term) {
        Some(Term::Var(idx)) => terms.var(idx + offset),
        Some(Term::App(func, kids)) => {
            let shifted: SmallVec<[TermId; 4]> =
                kids.iter().map(|&c| shift_term(c, offset, terms)).collect();
            terms.app(func, shifted)
        }
        None => term,
    }
}

fn match_pair(left: TermId, right: TermId, terms: &TermStore) -> (Matching, TermId, u32) {
    let offset = right_offset_for(left, terms);
    let right_shifted = shift_term(right, offset, terms);
    let matching = match_terms_disjoint(left, right_shifted, offset, terms)
        .expect("expected matching to succeed");
    (matching, right_shifted, offset)
}

fn apply_left(matching: &Matching, term: TermId, terms: &mut TermStore) -> TermId {
    apply_subst(term, &matching.left, terms)
}

fn apply_right(matching: &Matching, term: TermId, terms: &mut TermStore) -> TermId {
    apply_subst(term, &matching.right, terms)
}

#[test]
fn matching_same_ground_term_is_identity() {
    let (symbols, terms) = setup();
    let zero = symbols.intern("Zero");
    let t = terms.app0(zero);

    let (matching, right_shifted, _) = match_pair(t, t, &terms);
    assert!(matching.left.is_empty());
    assert!(matching.right.is_empty());

    let mut terms = terms;
    let left = apply_left(&matching, t, &mut terms);
    let right = apply_right(&matching, right_shifted, &mut terms);
    assert_eq!(left, right);
}

#[test]
fn matching_var_with_ground_binds_left() {
    let (symbols, terms) = setup();
    let zero = symbols.intern("Zero");
    let v0 = terms.var(0);
    let zero_term = terms.app0(zero);

    let (matching, _, _) = match_pair(v0, zero_term, &terms);
    assert_eq!(matching.left.get(0), Some(zero_term));
    assert!(matching.right.is_empty());
}

#[test]
fn matching_ground_with_var_binds_right() {
    let (symbols, terms) = setup();
    let zero = symbols.intern("Zero");
    let v0 = terms.var(0);
    let zero_term = terms.app0(zero);

    let (matching, _right_shifted, offset) = match_pair(zero_term, v0, &terms);
    assert_eq!(matching.right.get(offset), Some(zero_term));
    assert!(matching.left.is_empty());
}

#[test]
fn matching_var_with_var_binds_right_side() {
    let (_, terms) = setup();
    let v0 = terms.var(0);
    let v1 = terms.var(1);

    let (matching, _right_shifted, offset) = match_pair(v0, v1, &terms);
    assert!(matching.left.is_empty());
    assert!(matching.right.is_bound(offset + 1));
    assert_eq!(matching.right.len(), 1);
}

#[test]
fn matching_compatible_apps_bind_left() {
    let (symbols, terms) = setup();
    let f = symbols.intern("F");
    let v0 = terms.var(0);
    let a = symbols.intern("A");
    let a_term = terms.app0(a);

    let t1 = terms.app1(f, v0);
    let t2 = terms.app1(f, a_term);

    let (matching, _right_shifted, _) = match_pair(t1, t2, &terms);
    assert_eq!(matching.left.get(0), Some(a_term));
}

#[test]
fn matching_var_names_not_shared_across_sides() {
    let (symbols, terms) = setup();
    let f = symbols.intern("F");
    let v0 = terms.var(0);
    let t1 = terms.app1(f, v0);
    let t2 = terms.app1(f, v0);

    let (matching, right_shifted, _) = match_pair(t1, t2, &terms);
    assert!(
        !(matching.left.is_empty() && matching.right.is_empty()),
        "matching must not treat shared variable indices as shared identity"
    );

    let mut terms = terms;
    let left = apply_left(&matching, t1, &mut terms);
    let right = apply_right(&matching, right_shifted, &mut terms);
    assert_eq!(left, right);
}

#[test]
fn matching_functor_mismatch_fails() {
    let (symbols, terms) = setup();
    let f = symbols.intern("F");
    let g = symbols.intern("G");
    let v0 = terms.var(0);

    let t1 = terms.app1(f, v0);
    let t2 = terms.app1(g, v0);

    let offset = right_offset_for(t1, &terms);
    let right_shifted = shift_term(t2, offset, &terms);
    assert!(match_terms_disjoint(t1, right_shifted, offset, &terms).is_none());
}

#[test]
fn matching_arity_mismatch_fails() {
    let (symbols, terms) = setup();
    let f = symbols.intern("F");
    let v0 = terms.var(0);
    let v1 = terms.var(1);

    let t1 = terms.app1(f, v0);
    let t2 = terms.app2(f, v0, v1);

    let offset = right_offset_for(t1, &terms);
    let right_shifted = shift_term(t2, offset, &terms);
    assert!(match_terms_disjoint(t1, right_shifted, offset, &terms).is_none());
}

#[test]
fn matching_applies_separate_substitutions() {
    let (symbols, terms) = setup();
    let pair = symbols.intern("Pair");
    let a = symbols.intern("A");
    let a_term = terms.app0(a);
    let x = terms.var(0);
    let y = terms.var(1);

    let left = terms.app2(pair, x, a_term);
    let right = terms.app2(pair, a_term, y);

    let (matching, _right_shifted, offset) = match_pair(left, right, &terms);
    assert_eq!(matching.left.get(0), Some(a_term));
    assert_eq!(matching.right.get(offset + 1), Some(a_term));
}

#[derive(Clone, Debug)]
enum RawTerm {
    Var(u32),
    App { f: usize, kids: Vec<RawTerm> },
}

const FUNCTORS: [&str; 3] = ["A", "B", "F"];
const MAX_VAR: u32 = 3;

fn raw_term_strategy() -> impl Strategy<Value = RawTerm> {
    let leaf = prop_oneof![
        (0..=MAX_VAR).prop_map(RawTerm::Var),
        Just(RawTerm::App { f: 0, kids: vec![] }),
        Just(RawTerm::App { f: 1, kids: vec![] }),
    ];

    leaf.prop_recursive(3, 16, 3, |inner| {
        prop_oneof![
            inner.clone().prop_map(|t| RawTerm::App { f: 2, kids: vec![t] }),
            (inner.clone(), inner).prop_map(|(a, b)| RawTerm::App {
                f: 2,
                kids: vec![a, b],
            }),
        ]
    })
}

fn build_term(raw: &RawTerm, symbols: &crate::symbol::SymbolStore, terms: &TermStore) -> TermId {
    match raw {
        RawTerm::Var(v) => terms.var(*v),
        RawTerm::App { f, kids } => {
            let func = symbols.intern(FUNCTORS[*f]);
            let mut child_ids: SmallVec<[TermId; 4]> = SmallVec::new();
            for kid in kids {
                child_ids.push(build_term(kid, symbols, terms));
            }
            terms.app(func, child_ids)
        }
    }
}

fn has_var(raw: &RawTerm) -> bool {
    match raw {
        RawTerm::Var(_) => true,
        RawTerm::App { kids, .. } => kids.iter().any(has_var),
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 128, .. ProptestConfig::default() })]

    #[test]
    fn matching_invariant_to_right_renaming(left in raw_term_strategy(), right in raw_term_strategy()) {
        let (symbols, terms) = setup();
        let left_id = build_term(&left, &symbols, &terms);
        let right_id = build_term(&right, &symbols, &terms);

        let offset = right_offset_for(left_id, &terms);
        let right_shifted = shift_term(right_id, offset, &terms);
        let success_a = match_terms_disjoint(left_id, right_shifted, offset, &terms).is_some();

        let offset_b = offset + 5;
        let right_shifted_b = shift_term(right_id, offset_b, &terms);
        let success_b = match_terms_disjoint(left_id, right_shifted_b, offset_b, &terms).is_some();

        prop_assert_eq!(success_a, success_b);
    }

    #[test]
    fn matching_identical_terms_with_vars_is_not_identity(raw in raw_term_strategy()) {
        prop_assume!(has_var(&raw));
        let (symbols, terms) = setup();
        let left_id = build_term(&raw, &symbols, &terms);
        let right_id = build_term(&raw, &symbols, &terms);

        let offset = right_offset_for(left_id, &terms);
        let right_shifted = shift_term(right_id, offset, &terms);
        let matching = match_terms_disjoint(left_id, right_shifted, offset, &terms)
            .expect("expected matching");

        prop_assert!(!(matching.left.is_empty() && matching.right.is_empty()));
    }
}
