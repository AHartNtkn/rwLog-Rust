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
mod tests;
