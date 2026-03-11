mod common;

use common::*;

use rwlog::kernel::{compose_nf, dual_nf, meet_nf};
use rwlog::nf::NF;
use rwlog::symbol::SymbolStore;
use rwlog::term::TermStore;

#[test]
fn compose_nf_basic_ground_rule() {
    let symbols = SymbolStore::new();
    let mut terms = TermStore::new();
    let a = t_atom(&symbols, &terms, "a");
    let b = t_atom(&symbols, &terms, "b");
    let c = t_atom(&symbols, &terms, "c");

    let left = NF::factor(a, b, (), &mut terms);
    let right = NF::factor(b, c, (), &mut terms);
    let composed = compose_nf(&left, &right, &mut terms).expect("compose should succeed");

    assert_nf_pair_with_dual(&composed, (shape_atom("a"), shape_atom("c")), &mut terms, &symbols);
}

#[test]
fn compose_nf_non_ground_structural() {
    let symbols = SymbolStore::new();
    let mut terms = TermStore::new();
    let f = sym(&symbols, "f");
    let g = sym(&symbols, "g");
    let h = sym(&symbols, "h");
    let v0 = t_var(&terms, 0);
    let v1 = t_var(&terms, 1);

    let left = NF::factor(t_app1(&terms, f, v0), t_app1(&terms, g, v0), (), &mut terms);
    let right = NF::factor(t_app1(&terms, g, v1), t_app1(&terms, h, v1), (), &mut terms);
    let composed = compose_nf(&left, &right, &mut terms).expect("compose should succeed");

    assert_nf_pair_with_dual(
        &composed,
        (
            shape_app("f", vec![shape_var(0)]),
            shape_app("h", vec![shape_var(0)]),
        ),
        &mut terms,
        &symbols,
    );
}

#[test]
fn compose_nf_renames_apart_variables() {
    let symbols = SymbolStore::new();
    let mut terms = TermStore::new();
    let v0 = t_var(&terms, 0);
    let v1 = t_var(&terms, 1);

    let left = NF::factor(v0, v1, (), &mut terms);
    let right = NF::factor(v1, v0, (), &mut terms);
    let composed = compose_nf(&left, &right, &mut terms).expect("compose should succeed");

    assert_nf_pair_with_dual(
        &composed,
        (shape_var(0), shape_var(1)),
        &mut terms,
        &symbols,
    );
}

#[test]
fn compose_nf_invariant_under_rhs_renaming() {
    let symbols = SymbolStore::new();
    let mut terms = TermStore::new();
    let f = sym(&symbols, "f");
    let g = sym(&symbols, "g");
    let h = sym(&symbols, "h");
    let v0 = t_var(&terms, 0);
    let v1 = t_var(&terms, 1);
    let v2 = t_var(&terms, 2);

    let left = NF::factor(t_app1(&terms, f, v0), t_app1(&terms, g, v0), (), &mut terms);
    let right_a = NF::factor(t_app1(&terms, g, v1), t_app1(&terms, h, v1), (), &mut terms);
    let right_b = NF::factor(t_app1(&terms, g, v2), t_app1(&terms, h, v2), (), &mut terms);

    let composed_a = compose_nf(&left, &right_a, &mut terms).expect("compose should succeed");
    let composed_b = compose_nf(&left, &right_b, &mut terms).expect("compose should succeed");

    let pair_a = nf_pair_shape(&composed_a, &mut terms, &symbols);
    let pair_b = nf_pair_shape(&composed_b, &mut terms, &symbols);
    assert_eq!(pair_a, pair_b);

    let dual_a = dual_nf(&composed_a, &mut terms);
    let dual_b = dual_nf(&composed_b, &mut terms);
    let dual_pair_a = nf_pair_shape(&dual_a, &mut terms, &symbols);
    let dual_pair_b = nf_pair_shape(&dual_b, &mut terms, &symbols);
    assert_eq!(dual_pair_a, dual_pair_b);
}

#[test]
fn meet_nf_intersection_empty_when_outputs_conflict() {
    let symbols = SymbolStore::new();
    let mut terms = TermStore::new();
    let a = t_atom(&symbols, &terms, "a");
    let b = t_atom(&symbols, &terms, "b");
    let c = t_atom(&symbols, &terms, "c");

    let left = NF::factor(a, b, (), &mut terms);
    let right = NF::factor(a, c, (), &mut terms);
    let met = meet_nf(&left, &right, &mut terms);
    assert!(met.is_none());
}

#[test]
fn meet_nf_non_ground_structural() {
    let symbols = SymbolStore::new();
    let mut terms = TermStore::new();
    let f = sym(&symbols, "f");
    let g = sym(&symbols, "g");
    let v0 = t_var(&terms, 0);
    let v1 = t_var(&terms, 1);

    let left = NF::factor(t_app1(&terms, f, v0), t_app1(&terms, g, v0), (), &mut terms);
    let right = NF::factor(t_app1(&terms, f, v1), t_app1(&terms, g, v1), (), &mut terms);
    let met = meet_nf(&left, &right, &mut terms).expect("meet should succeed");

    assert_nf_pair_with_dual(
        &met,
        (
            shape_app("f", vec![shape_var(0)]),
            shape_app("g", vec![shape_var(0)]),
        ),
        &mut terms,
        &symbols,
    );
}

#[test]
fn meet_nf_renames_apart_variables() {
    let symbols = SymbolStore::new();
    let mut terms = TermStore::new();
    let v0 = t_var(&terms, 0);
    let v1 = t_var(&terms, 1);

    let left = NF::factor(v0, v1, (), &mut terms);
    let right = NF::factor(v1, v0, (), &mut terms);
    let met = meet_nf(&left, &right, &mut terms).expect("meet should succeed");

    assert_nf_pair_with_dual(
        &met,
        (shape_var(0), shape_var(1)),
        &mut terms,
        &symbols,
    );
}
