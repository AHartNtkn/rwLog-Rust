use std::hash::Hash;

use crate::subst::Subst;
use crate::symbol::SymbolStore;
use crate::term::TermStore;

/// Trait for constraint systems that can be combined with NFs.
///
/// Constraints represent additional conditions that must be satisfied
/// beyond the structural matching of terms.
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

    /// Normalize by consuming self, avoiding a clone.
    ///
    /// Default implementation delegates to `normalize(&self)`.
    /// Implementors should override when they can avoid cloning.
    fn normalize_owned(self, terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
        self.normalize(terms)
    }

    /// Combine by consuming both sides, avoiding clones.
    ///
    /// Default implementation delegates to `combine(&self, &other)`.
    fn combine_owned(self, other: Self) -> Option<Self> {
        self.combine(&other)
    }

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

#[cfg(test)]
mod tests {
    use super::*;

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
}
