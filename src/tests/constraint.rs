use super::*;
use crate::term::TermStore;

// Helper to get term IDs for testing
fn get_term_ids() -> (
    crate::term::TermId,
    crate::term::TermId,
    crate::term::TermId,
) {
    let terms = TermStore::new();
    let t0 = terms.var(0);
    let t1 = terms.var(1);
    let t2 = terms.var(2);
    (t0, t1, t2)
}

// ========== UNIT CONSTRAINT TESTS ==========

#[test]
fn unit_constraint_is_empty() {
    let c: () = ();
    assert!(c.is_empty());
}

#[test]
fn unit_constraint_is_satisfiable() {
    let c: () = ();
    assert!(c.is_satisfiable());
}

#[test]
fn unit_constraint_combine() {
    let c1: () = ();
    let c2: () = ();
    let combined = c1.combine(&c2);
    assert_eq!(combined, Some(()));
}

#[test]
fn unit_constraint_normalize() {
    let c: () = ();
    let mut terms = TermStore::new();
    let (normalized, subst) = c.normalize(&mut terms).unwrap();
    assert_eq!(normalized, ());
    assert!(subst.is_none());
}

// ========== DISEQUALITY TESTS ==========

#[test]
fn disequality_new() {
    let (_t0, t1, _t2) = get_term_ids();
    let diseq = Disequality { var: 0, term: t1 };
    assert_eq!(diseq.var, 0);
    assert_eq!(diseq.term, t1);
}

#[test]
fn diseq_constraint_new() {
    let c = DiseqConstraint::new();
    assert!(c.is_empty());
    assert_eq!(c.len(), 0);
}

#[test]
fn diseq_constraint_add() {
    let (_t0, t1, t2) = get_term_ids();
    let mut c = DiseqConstraint::new();
    c.add(0, t1);
    c.add(1, t2);
    assert_eq!(c.len(), 2);
}

#[test]
fn diseq_constraint_no_duplicates() {
    let (_t0, t1, _t2) = get_term_ids();
    let mut c = DiseqConstraint::new();
    c.add(0, t1);
    c.add(0, t1); // Duplicate
    assert_eq!(c.len(), 1);
}

#[test]
fn diseq_constraint_is_empty() {
    let (_t0, t1, _t2) = get_term_ids();
    let c = DiseqConstraint::new();
    assert!(c.is_empty());

    let mut c2 = DiseqConstraint::new();
    c2.add(0, t1);
    assert!(!c2.is_empty());
}

#[test]
fn diseq_constraint_combine() {
    let (_t0, t1, t2) = get_term_ids();
    let mut c1 = DiseqConstraint::new();
    c1.add(0, t1);

    let mut c2 = DiseqConstraint::new();
    c2.add(1, t2);

    let combined = c1.combine(&c2).unwrap();
    assert_eq!(combined.len(), 2);
}

#[test]
fn diseq_constraint_combine_with_overlap() {
    let (_t0, t1, _t2) = get_term_ids();
    let mut c1 = DiseqConstraint::new();
    c1.add(0, t1);

    let mut c2 = DiseqConstraint::new();
    c2.add(0, t1); // Same constraint

    let combined = c1.combine(&c2).unwrap();
    assert_eq!(combined.len(), 1);
}

#[test]
fn diseq_constraint_normalize() {
    let (_t0, t1, _t2) = get_term_ids();
    let mut c = DiseqConstraint::new();
    c.add(0, t1);

    let mut terms = TermStore::new();
    let (normalized, subst) = c.normalize(&mut terms).unwrap();
    assert_eq!(normalized.len(), 1);
    assert!(subst.is_none());
}

#[test]
fn diseq_constraint_satisfiable() {
    let (_t0, t1, _t2) = get_term_ids();
    let mut c = DiseqConstraint::new();
    c.add(0, t1);
    assert!(c.is_satisfiable());
}

#[test]
fn diseq_constraint_iter() {
    let (_t0, t1, t2) = get_term_ids();
    let mut c = DiseqConstraint::new();
    c.add(0, t1);
    c.add(1, t2);

    let diseqs: Vec<_> = c.iter().collect();
    assert_eq!(diseqs.len(), 2);
}

// ========== TYPE CONSTRAINT TESTS ==========

#[test]
fn type_constraint_new() {
    let terms = TermStore::new();
    let tc = TypeConstraint {
        term: terms.var(0),
        type_id: 1,
    };
    assert_eq!(tc.term, terms.var(0));
    assert_eq!(tc.type_id, 1);
}

#[test]
fn type_constraints_new() {
    let c = TypeConstraints::new();
    assert!(c.is_empty());
    assert_eq!(c.len(), 0);
}

#[test]
fn type_constraints_add() {
    let terms = TermStore::new();
    let mut c = TypeConstraints::new();
    c.add(terms.var(0), 1);
    c.add(terms.var(1), 2);
    assert_eq!(c.len(), 2);
}

#[test]
fn type_constraints_no_duplicates() {
    let terms = TermStore::new();
    let mut c = TypeConstraints::new();
    c.add(terms.var(0), 1);
    c.add(terms.var(0), 1); // Duplicate
    assert_eq!(c.len(), 1);
}

#[test]
fn type_constraints_get_type() {
    let terms = TermStore::new();
    let mut c = TypeConstraints::new();
    c.add(terms.var(0), 42);

    assert_eq!(c.get_type(terms.var(0)), Some(42));
    assert_eq!(c.get_type(terms.var(1)), None);
}

#[test]
fn type_constraints_is_empty() {
    let c = TypeConstraints::new();
    assert!(c.is_empty());

    let terms = TermStore::new();
    let mut c2 = TypeConstraints::new();
    c2.add(terms.var(0), 1);
    assert!(!c2.is_empty());
}

#[test]
fn type_constraints_combine_success() {
    let terms = TermStore::new();
    let mut c1 = TypeConstraints::new();
    c1.add(terms.var(0), 1);

    let mut c2 = TypeConstraints::new();
    c2.add(terms.var(1), 2);

    let combined = c1.combine(&c2).unwrap();
    assert_eq!(combined.len(), 2);
}

#[test]
fn type_constraints_combine_same_type() {
    let terms = TermStore::new();
    let mut c1 = TypeConstraints::new();
    c1.add(terms.var(0), 1);

    let mut c2 = TypeConstraints::new();
    c2.add(terms.var(0), 1); // Same term, same type

    let combined = c1.combine(&c2).unwrap();
    assert_eq!(combined.len(), 1);
}

#[test]
fn type_constraints_combine_conflict() {
    let terms = TermStore::new();
    let mut c1 = TypeConstraints::new();
    c1.add(terms.var(0), 1);

    let mut c2 = TypeConstraints::new();
    c2.add(terms.var(0), 2); // Same term, different type

    let combined = c1.combine(&c2);
    assert!(combined.is_none());
}

#[test]
fn type_constraints_satisfiable() {
    let terms = TermStore::new();
    let mut c = TypeConstraints::new();
    c.add(terms.var(0), 1);
    c.add(terms.var(1), 2);
    assert!(c.is_satisfiable());
}

#[test]
fn type_constraints_normalize() {
    let terms = TermStore::new();
    let mut c = TypeConstraints::new();
    c.add(terms.var(0), 1);

    let mut terms = terms;
    let (normalized, subst) = c.normalize(&mut terms).unwrap();
    assert_eq!(normalized.len(), 1);
    assert!(subst.is_none());
}

// ========== COMBINED CONSTRAINT TESTS ==========

#[test]
fn combined_constraint_new() {
    let c = CombinedConstraint::new();
    assert!(c.is_empty());
}

#[test]
fn combined_constraint_add_diseq() {
    let (_t0, t1, _t2) = get_term_ids();
    let mut c = CombinedConstraint::new();
    c.add_diseq(0, t1);
    assert!(!c.is_empty());
    assert_eq!(c.diseqs.len(), 1);
}

#[test]
fn combined_constraint_add_type() {
    let terms = TermStore::new();
    let mut c = CombinedConstraint::new();
    c.add_type(terms.var(0), 1);
    assert!(!c.is_empty());
    assert_eq!(c.types.len(), 1);
}

#[test]
fn combined_constraint_combine() {
    let (t0, t1, t2) = get_term_ids();
    let mut c1 = CombinedConstraint::new();
    c1.add_diseq(0, t1);
    c1.add_type(t0, 10);

    let mut c2 = CombinedConstraint::new();
    c2.add_diseq(1, t2);
    c2.add_type(t2, 20);

    let combined = c1.combine(&c2).unwrap();
    assert_eq!(combined.diseqs.len(), 2);
    assert_eq!(combined.types.len(), 2);
}

#[test]
fn combined_constraint_combine_type_conflict() {
    let (t0, _t1, _t2) = get_term_ids();
    let mut c1 = CombinedConstraint::new();
    c1.add_type(t0, 1);

    let mut c2 = CombinedConstraint::new();
    c2.add_type(t0, 2); // Conflict

    let combined = c1.combine(&c2);
    assert!(combined.is_none());
}

#[test]
fn combined_constraint_is_satisfiable() {
    let (t0, t1, _t2) = get_term_ids();
    let mut c = CombinedConstraint::new();
    c.add_diseq(0, t1);
    c.add_type(t0, 10);
    assert!(c.is_satisfiable());
}

#[test]
fn combined_constraint_normalize() {
    let (t0, t1, _t2) = get_term_ids();
    let mut c = CombinedConstraint::new();
    c.add_diseq(0, t1);
    c.add_type(t0, 10);

    let mut terms = TermStore::new();
    let (normalized, subst) = c.normalize(&mut terms).unwrap();
    assert!(!normalized.is_empty());
    assert!(subst.is_none());
}

// ========== CONSTRAINT OPS TRAIT TESTS ==========

#[test]
fn constraint_ops_default() {
    let c: () = Default::default();
    assert!(c.is_empty());

    let d: DiseqConstraint = Default::default();
    assert!(d.is_empty());

    let t: TypeConstraints = Default::default();
    assert!(t.is_empty());

    let cc: CombinedConstraint = Default::default();
    assert!(cc.is_empty());
}

// ========== GENERIC USAGE TESTS ==========

fn check_constraint<C: ConstraintOps>(c: &C) -> bool {
    c.is_satisfiable() && c.is_empty()
}

#[test]
fn generic_unit_constraint() {
    let c: () = ();
    assert!(check_constraint(&c));
}

#[test]
fn generic_diseq_constraint_empty() {
    let c = DiseqConstraint::new();
    assert!(check_constraint(&c));
}

#[test]
fn generic_diseq_constraint_non_empty() {
    let (_t0, t1, _t2) = get_term_ids();
    let mut c = DiseqConstraint::new();
    c.add(0, t1);
    assert!(c.is_satisfiable());
    assert!(!c.is_empty());
}

// ========== HASH TESTS ==========

#[test]
fn diseq_constraint_hash() {
    use std::collections::HashSet;

    let (_t0, t1, _t2) = get_term_ids();
    let mut c1 = DiseqConstraint::new();
    c1.add(0, t1);

    let mut c2 = DiseqConstraint::new();
    c2.add(0, t1);

    let mut set = HashSet::new();
    set.insert(c1.clone());
    set.insert(c2); // Should be same as c1

    assert_eq!(set.len(), 1);
}

#[test]
fn type_constraints_hash() {
    use std::collections::HashSet;

    let terms = TermStore::new();
    let mut c1 = TypeConstraints::new();
    c1.add(terms.var(0), 1);

    let mut c2 = TypeConstraints::new();
    c2.add(terms.var(0), 1);

    let mut set = HashSet::new();
    set.insert(c1);
    set.insert(c2);

    assert_eq!(set.len(), 1);
}

#[test]
fn combined_constraint_hash() {
    use std::collections::HashSet;

    let (t0, t1, _t2) = get_term_ids();
    let mut c1 = CombinedConstraint::new();
    c1.add_diseq(0, t1);
    c1.add_type(t0, 10);

    let mut c2 = CombinedConstraint::new();
    c2.add_diseq(0, t1);
    c2.add_type(t0, 10);

    let mut set = HashSet::new();
    set.insert(c1);
    set.insert(c2);

    assert_eq!(set.len(), 1);
}
