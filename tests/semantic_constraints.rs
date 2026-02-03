mod common;

use common::*;

use rwlog::constraint::{CombinedConstraint, TypeConstraints};
use rwlog::kernel::{compose_nf, meet_nf};
use rwlog::nf::NF;
use rwlog::symbol::SymbolStore;
use rwlog::term::TermStore;

#[test]
fn compose_substitutes_type_constraint_to_ground_term() {
    let symbols = SymbolStore::new();
    let mut terms = TermStore::new();
    let v0 = t_var(&terms, 0);
    let a = t_atom(&symbols, &terms, "a");

    let mut left_c = TypeConstraints::new();
    left_c.add(v0, 7);
    let left = NF::factor(v0, v0, left_c, &mut terms);

    let right = NF::factor(a, a, TypeConstraints::new(), &mut terms);
    let composed = compose_nf(&left, &right, &mut terms).expect("compose should succeed");

    let constraint = &composed.drop_fresh.constraint;
    assert_eq!(
        constraint.get_type(a),
        Some(7),
        "type constraint should apply to substituted ground term"
    );
}

#[test]
fn meet_combines_type_constraints_non_ground() {
    let mut terms = TermStore::new();
    let v0 = t_var(&terms, 0);

    let mut left_c = TypeConstraints::new();
    left_c.add(v0, 1);
    let left = NF::factor(v0, v0, left_c, &mut terms);

    let mut right_c = TypeConstraints::new();
    right_c.add(v0, 1);
    let right = NF::factor(v0, v0, right_c, &mut terms);

    let met = meet_nf(&left, &right, &mut terms).expect("meet should succeed");
    let constraint = &met.drop_fresh.constraint;
    assert_eq!(
        constraint.get_type(t_var(&terms, 0)),
        Some(1),
        "type constraint should be preserved on variable"
    );
}

#[test]
fn combined_constraint_survives_non_ground_compose() {
    let symbols = SymbolStore::new();
    let mut terms = TermStore::new();
    let v0 = t_var(&terms, 0);
    let a = t_atom(&symbols, &terms, "a");

    let mut left_c = CombinedConstraint::new();
    left_c.add_type(v0, 3);
    left_c.add_diseq(0, a);
    let left = NF::factor(v0, v0, left_c, &mut terms);

    let right = NF::factor(a, a, CombinedConstraint::new(), &mut terms);
    let composed = compose_nf(&left, &right, &mut terms).expect("compose should succeed");
    let constraint = &composed.drop_fresh.constraint;

    assert_eq!(constraint.types.get_type(a), Some(3));
    assert_eq!(constraint.diseqs.len(), 1);
}
