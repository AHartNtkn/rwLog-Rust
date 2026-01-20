use std::hash::Hash;

use crate::nf::apply_var_renaming;
use crate::subst::Subst;
use crate::symbol::SymbolStore;
use crate::term::{Term, TermStore};

/// Trait for constraint systems that can be combined with NFs.
///
/// Constraints represent additional conditions that must be satisfied
/// beyond the structural matching of terms. Examples include:
/// - Disequality constraints (X != Y)
/// - Type constraints (X : Int)
/// - Arithmetic constraints (X > 0)
///
/// The Unit constraint (implemented by `()`) represents no constraints,
/// which is useful for pure structural rewriting.
pub trait ConstraintOps: Clone + Eq + Hash + Default + Send + Sync {
    /// Combine two constraints (conjunction).
    ///
    /// Returns None if the constraints are inconsistent.
    fn combine(&self, other: &Self) -> Option<Self>;

    /// Normalize the constraint, potentially producing substitutions.
    ///
    /// Returns the simplified constraint and any substitutions that
    /// were derived from the constraint.
    fn normalize(&self, terms: &mut TermStore) -> Option<(Self, Option<Subst>)>;

    /// Apply a substitution to the constraint.
    fn apply_subst(&self, subst: &Subst, terms: &mut TermStore) -> Self;

    /// Remap variable indices according to a renaming map.
    fn remap_vars(&self, map: &[Option<u32>], terms: &mut TermStore) -> Self;

    /// Collect variable indices referenced by this constraint.
    fn collect_vars(&self, _terms: &TermStore, _out: &mut Vec<u32>) {}

    /// Check if this is the trivial (empty) constraint.
    fn is_empty(&self) -> bool;

    /// Check if this constraint is satisfiable.
    fn is_satisfiable(&self) -> bool;
}

pub trait ConstraintDisplay {
    fn fmt_constraints(
        &self,
        _terms: &mut TermStore,
        _symbols: &SymbolStore,
    ) -> Result<Option<String>, String> {
        Ok(None)
    }
}

/// Unit constraint - represents no constraints.
///
/// This is the simplest constraint system where all constraints
/// are trivially satisfied. Useful for pure term rewriting without
/// additional constraint handling.
impl ConstraintOps for () {
    fn combine(&self, _other: &Self) -> Option<Self> {
        Some(())
    }

    fn normalize(&self, _terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
        Some(((), None))
    }

    fn apply_subst(&self, _subst: &Subst, _terms: &mut TermStore) -> Self {}

    fn remap_vars(&self, _map: &[Option<u32>], _terms: &mut TermStore) -> Self {}

    fn collect_vars(&self, _terms: &TermStore, _out: &mut Vec<u32>) {}

    fn is_empty(&self) -> bool {
        true
    }

    fn is_satisfiable(&self) -> bool {
        true
    }
}

impl ConstraintDisplay for () {}

/// A disequality constraint: X != t
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Disequality {
    /// Variable index.
    pub var: u32,
    /// Term ID that the variable must not equal.
    pub term: crate::term::TermId,
}

/// A set of disequality constraints.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct DiseqConstraint {
    /// List of disequalities.
    constraints: Vec<Disequality>,
}

impl DiseqConstraint {
    /// Create an empty disequality constraint.
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
        }
    }

    /// Add a disequality: var != term.
    pub fn add(&mut self, var: u32, term: crate::term::TermId) {
        let diseq = Disequality { var, term };
        if !self.constraints.contains(&diseq) {
            self.constraints.push(diseq);
        }
    }

    /// Get the number of constraints.
    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    /// Check if there are no constraints.
    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    /// Iterator over disequalities.
    pub fn iter(&self) -> impl Iterator<Item = &Disequality> {
        self.constraints.iter()
    }
}

impl ConstraintOps for DiseqConstraint {
    fn combine(&self, other: &Self) -> Option<Self> {
        let mut result = self.clone();
        for diseq in &other.constraints {
            if !result.constraints.contains(diseq) {
                result.constraints.push(diseq.clone());
            }
        }
        Some(result)
    }

    fn normalize(&self, _terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
        if !self.is_satisfiable() {
            return None;
        }
        Some((self.clone(), None))
    }

    fn apply_subst(&self, subst: &Subst, terms: &mut TermStore) -> Self {
        let mut out = self.clone();
        for diseq in out.constraints.iter_mut() {
            if let Some(bound) = subst.get(diseq.var) {
                if let Some(Term::Var(new_var)) = terms.resolve(bound) {
                    diseq.var = new_var;
                }
            }
            diseq.term = crate::subst::apply_subst(diseq.term, subst, terms);
        }
        out
    }

    fn remap_vars(&self, map: &[Option<u32>], terms: &mut TermStore) -> Self {
        let mut out = self.clone();
        for diseq in out.constraints.iter_mut() {
            if (diseq.var as usize) < map.len() {
                if let Some(new_var) = map[diseq.var as usize] {
                    diseq.var = new_var;
                }
            }
            diseq.term = apply_var_renaming(diseq.term, map, terms);
        }
        out
    }

    fn collect_vars(&self, terms: &TermStore, out: &mut Vec<u32>) {
        for diseq in self.constraints.iter() {
            out.push(diseq.var);
            out.extend(crate::nf::collect_vars_ordered(diseq.term, terms));
        }
    }

    fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    fn is_satisfiable(&self) -> bool {
        // Disequalities are always satisfiable unless we can prove otherwise
        // A more complete implementation would check for contradictions
        true
    }
}

impl ConstraintDisplay for DiseqConstraint {}

/// A type constraint: X : Type
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeConstraint {
    /// Term to constrain.
    pub term: crate::term::TermId,
    /// Type identifier.
    pub type_id: u32,
}

/// A set of type constraints.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct TypeConstraints {
    /// List of type constraints.
    constraints: Vec<TypeConstraint>,
}

impl TypeConstraints {
    /// Create empty type constraints.
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
        }
    }

    /// Add a type constraint: term : type_id.
    pub fn add(&mut self, term: crate::term::TermId, type_id: u32) {
        let tc = TypeConstraint { term, type_id };
        // Check for conflicting type constraint
        for existing in &self.constraints {
            if existing.term == term && existing.type_id != type_id {
                // Conflicting types - this would make it unsatisfiable
                // For now, we just don't add duplicates
                return;
            }
        }
        if !self.constraints.contains(&tc) {
            self.constraints.push(tc);
        }
    }

    /// Get the type constraint for a variable.
    pub fn get_type(&self, term: crate::term::TermId) -> Option<u32> {
        self.constraints
            .iter()
            .find(|tc| tc.term == term)
            .map(|tc| tc.type_id)
    }

    /// Get the number of constraints.
    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    /// Check if there are no constraints.
    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }
}

impl ConstraintOps for TypeConstraints {
    fn combine(&self, other: &Self) -> Option<Self> {
        let mut result = self.clone();
        for tc in &other.constraints {
            // Check for conflicting types
            if let Some(existing_type) = result.get_type(tc.term) {
                if existing_type != tc.type_id {
                    return None; // Inconsistent types
                }
            } else {
                result.constraints.push(tc.clone());
            }
        }
        Some(result)
    }

    fn normalize(&self, _terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
        if !self.is_satisfiable() {
            return None;
        }
        let mut out = self.clone();
        out.constraints
            .sort_by(|a, b| (a.term, a.type_id).cmp(&(b.term, b.type_id)));
        out.constraints
            .dedup_by(|a, b| a.term == b.term && a.type_id == b.type_id);
        Some((out, None))
    }

    fn apply_subst(&self, subst: &Subst, terms: &mut TermStore) -> Self {
        let mut out = self.clone();
        for tc in out.constraints.iter_mut() {
            tc.term = crate::subst::apply_subst(tc.term, subst, terms);
        }
        out
    }

    fn remap_vars(&self, map: &[Option<u32>], terms: &mut TermStore) -> Self {
        let mut out = self.clone();
        for tc in out.constraints.iter_mut() {
            tc.term = apply_var_renaming(tc.term, map, terms);
        }
        out.constraints
            .sort_by(|a, b| (a.term, a.type_id).cmp(&(b.term, b.type_id)));
        out.constraints
            .dedup_by(|a, b| a.term == b.term && a.type_id == b.type_id);
        out
    }

    fn collect_vars(&self, terms: &TermStore, out: &mut Vec<u32>) {
        for tc in self.constraints.iter() {
            out.extend(crate::nf::collect_vars_ordered(tc.term, terms));
        }
    }

    fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    fn is_satisfiable(&self) -> bool {
        // Check for conflicting type constraints on the same variable
        for (i, tc1) in self.constraints.iter().enumerate() {
            for tc2 in self.constraints.iter().skip(i + 1) {
                if tc1.term == tc2.term && tc1.type_id != tc2.type_id {
                    return false;
                }
            }
        }
        true
    }
}

impl ConstraintDisplay for TypeConstraints {}

/// Combined constraint holding both disequalities and types.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct CombinedConstraint {
    /// Disequality constraints.
    pub diseqs: DiseqConstraint,
    /// Type constraints.
    pub types: TypeConstraints,
}

impl CombinedConstraint {
    /// Create empty combined constraint.
    pub fn new() -> Self {
        Self {
            diseqs: DiseqConstraint::new(),
            types: TypeConstraints::new(),
        }
    }

    /// Add a disequality constraint.
    pub fn add_diseq(&mut self, var: u32, term: crate::term::TermId) {
        self.diseqs.add(var, term);
    }

    /// Add a type constraint.
    pub fn add_type(&mut self, term: crate::term::TermId, type_id: u32) {
        self.types.add(term, type_id);
    }
}

impl ConstraintOps for CombinedConstraint {
    fn combine(&self, other: &Self) -> Option<Self> {
        let diseqs = self.diseqs.combine(&other.diseqs)?;
        let types = self.types.combine(&other.types)?;
        Some(Self { diseqs, types })
    }

    fn normalize(&self, terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
        let (diseqs, _) = self.diseqs.normalize(terms)?;
        let (types, _) = self.types.normalize(terms)?;
        Some((Self { diseqs, types }, None))
    }

    fn apply_subst(&self, subst: &Subst, terms: &mut TermStore) -> Self {
        Self {
            diseqs: self.diseqs.apply_subst(subst, terms),
            types: self.types.apply_subst(subst, terms),
        }
    }

    fn remap_vars(&self, map: &[Option<u32>], terms: &mut TermStore) -> Self {
        Self {
            diseqs: self.diseqs.remap_vars(map, terms),
            types: self.types.remap_vars(map, terms),
        }
    }

    fn collect_vars(&self, terms: &TermStore, out: &mut Vec<u32>) {
        self.diseqs.collect_vars(terms, out);
        self.types.collect_vars(terms, out);
    }

    fn is_empty(&self) -> bool {
        self.diseqs.is_empty() && self.types.is_empty()
    }

    fn is_satisfiable(&self) -> bool {
        self.diseqs.is_satisfiable() && self.types.is_satisfiable()
    }
}

impl ConstraintDisplay for CombinedConstraint {}

#[cfg(test)]
mod tests {
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
}
