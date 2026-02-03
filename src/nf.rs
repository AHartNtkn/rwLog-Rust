//! Normal Form (NF) representation for rewrite relations.
//!
//! An NF represents a relation as a pair of boundaries (match and build)
//! with an associated constraint. Variables are numbered by first occurrence
//! scanning match_boundary then build_boundary.
//!
//! Semantics: NF denotes the set of all ground instances where for all
//! substitutions σ, if input matches match_boundary[σ], output is build_boundary[σ].

use crate::constraint::{ConstraintDisplay, ConstraintOps};
use crate::symbol::SymbolStore;
use crate::term::{format_term, Term, TermId, TermStore};
use smallvec::SmallVec;
use std::collections::HashSet;

/// A boundary is a list of term patterns (tensor arity = length).
pub type Boundary = SmallVec<[TermId; 1]>;

/// Normal Form representation of a rewrite relation.
///
/// Variables are numbered 0, 1, 2, ... in order of first occurrence,
/// scanning match_boundary first, then build_boundary. This is the
/// canonical form required for deduplication in tabling.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NF<C> {
    /// Patterns to match against input (tensor of terms).
    pub match_boundary: Boundary,
    /// Patterns to construct output (tensor of terms).
    pub build_boundary: Boundary,
    /// Associated constraint.
    pub constraint: C,
}

impl<C: Default> NF<C> {
    /// Create an NF with default constraint.
    pub fn new(match_boundary: Boundary, build_boundary: Boundary) -> Self {
        Self {
            match_boundary,
            build_boundary,
            constraint: C::default(),
        }
    }
}

impl<C> NF<C> {
    /// Create an NF with explicit constraint.
    pub fn with_constraint(match_boundary: Boundary, build_boundary: Boundary, constraint: C) -> Self {
        Self {
            match_boundary,
            build_boundary,
            constraint,
        }
    }

    /// Create an identity NF (empty boundaries).
    /// Represents the identity relation that accepts any input and produces it unchanged.
    pub fn identity(constraint: C) -> Self {
        Self {
            match_boundary: SmallVec::new(),
            build_boundary: SmallVec::new(),
            constraint,
        }
    }

    /// Get the input arity (number of terms in match boundary).
    pub fn match_arity(&self) -> usize {
        self.match_boundary.len()
    }

    /// Get the output arity (number of terms in build boundary).
    pub fn build_arity(&self) -> usize {
        self.build_boundary.len()
    }
}

impl<C: ConstraintOps> NF<C> {
    /// Create an NF from patterns, canonicalizing variables.
    ///
    /// Variables are renumbered by first occurrence (match then build).
    /// The constraint is also renumbered to use the canonical variable indices.
    pub fn from_patterns(
        match_pats: Boundary,
        build_pats: Boundary,
        constraint: C,
        terms: &mut TermStore,
    ) -> Self {
        let mut nf = Self::with_constraint(match_pats, build_pats, constraint);
        canonicalize_nf(&mut nf, terms);
        nf
    }

    /// Factor a single-term rule (lhs -> rhs) into normal form.
    ///
    /// Convenience method for the common case of arity-1 relations.
    pub fn factor(lhs: TermId, rhs: TermId, constraint: C, terms: &mut TermStore) -> Self {
        Self::from_patterns(
            smallvec::smallvec![lhs],
            smallvec::smallvec![rhs],
            constraint,
            terms,
        )
    }
}

/// Canonicalize an NF in place by renumbering variables.
///
/// Variables are assigned indices 0, 1, 2, ... in order of first occurrence,
/// scanning match_boundary first, then build_boundary.
pub fn canonicalize_nf<C: ConstraintOps>(nf: &mut NF<C>, terms: &mut TermStore) {
    // Collect all variables in canonical order
    let match_vars = collect_vars_ordered_list(&nf.match_boundary, terms);
    let build_vars = collect_vars_ordered_list(&nf.build_boundary, terms);

    // Build combined ordering: match vars first, then build-only vars
    let mut ordered: Vec<u32> = match_vars.clone();
    let match_set: HashSet<u32> = match_vars.iter().copied().collect();
    for var in build_vars {
        if !match_set.contains(&var) {
            ordered.push(var);
        }
    }

    // Include constraint variables
    let mut constraint_vars = Vec::new();
    nf.constraint.collect_vars(terms, &mut constraint_vars);
    let mut seen: HashSet<u32> = ordered.iter().copied().collect();
    for var in constraint_vars {
        if seen.insert(var) {
            ordered.push(var);
        }
    }

    if ordered.is_empty() {
        return; // No variables to renumber
    }

    // Build renaming map
    let old_to_new = build_var_map(&ordered);

    // Apply renaming to boundaries
    nf.match_boundary = apply_var_renaming_list(&nf.match_boundary, &old_to_new, terms);
    nf.build_boundary = apply_var_renaming_list(&nf.build_boundary, &old_to_new, terms);

    // Apply renaming to constraint
    nf.constraint = nf.constraint.remap_vars(&old_to_new, terms);
}

/// Canonicalize an NF, returning a new NF.
pub fn canon_nf<C: ConstraintOps>(nf: &NF<C>, terms: &mut TermStore) -> NF<C> {
    let mut result = nf.clone();
    canonicalize_nf(&mut result, terms);
    result
}

/// Compute the maximum variable index in an NF.
pub fn max_var_in_nf<C>(nf: &NF<C>, terms: &TermStore) -> Option<u32> {
    let match_max = max_var_in_boundary(&nf.match_boundary, terms);
    let build_max = max_var_in_boundary(&nf.build_boundary, terms);
    match (match_max, build_max) {
        (Some(a), Some(b)) => Some(a.max(b)),
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        (None, None) => None,
    }
}

/// Compute the maximum variable index in a boundary.
pub fn max_var_in_boundary(boundary: &[TermId], terms: &TermStore) -> Option<u32> {
    let vars = collect_vars_ordered_list(boundary, terms);
    vars.into_iter().max()
}

/// Shift all variables in an NF by an offset, returning a new NF.
///
/// Used to rename variables apart before matching.
pub fn shift_nf_vars<C: ConstraintOps>(nf: &NF<C>, offset: u32, terms: &mut TermStore) -> NF<C> {
    let match_shifted = shift_vars_list(&nf.match_boundary, offset, terms);
    let build_shifted = shift_vars_list(&nf.build_boundary, offset, terms);
    let constraint_shifted = nf.constraint.shift_vars(offset, terms);
    NF::with_constraint(match_shifted, build_shifted, constraint_shifted)
}

/// Shift all variables in a boundary by an offset.
pub fn shift_vars_list(boundary: &[TermId], offset: u32, terms: &mut TermStore) -> Boundary {
    boundary
        .iter()
        .map(|&t| shift_vars(t, offset, terms))
        .collect()
}

/// Shift all variables in a term by an offset.
pub fn shift_vars(term: TermId, offset: u32, terms: &mut TermStore) -> TermId {
    match terms.resolve(term) {
        Some(Term::Var(idx)) => terms.var(idx + offset),
        Some(Term::App(func, children)) => {
            let new_children: SmallVec<[TermId; 4]> = children
                .iter()
                .map(|&child| shift_vars(child, offset, terms))
                .collect();
            terms.app(func, new_children)
        }
        None => term,
    }
}

// ============================================================================
// Variable collection utilities
// ============================================================================

/// Collect variables from a term in order of first appearance.
pub fn collect_vars_ordered(term: TermId, terms: &TermStore) -> Vec<u32> {
    let mut vars = Vec::new();
    let mut seen = HashSet::new();
    collect_vars_helper(term, terms, &mut vars, &mut seen);
    vars
}

/// Collect variables from a list of terms in order of first appearance.
pub fn collect_vars_ordered_list(terms_list: &[TermId], terms: &TermStore) -> Vec<u32> {
    let mut vars = Vec::new();
    let mut seen = HashSet::new();
    for &term in terms_list {
        collect_vars_helper(term, terms, &mut vars, &mut seen);
    }
    vars
}

fn collect_vars_helper(
    term: TermId,
    terms: &TermStore,
    vars: &mut Vec<u32>,
    seen: &mut HashSet<u32>,
) {
    match terms.resolve(term) {
        Some(Term::Var(idx)) => {
            if seen.insert(idx) {
                vars.push(idx);
            }
        }
        Some(Term::App(_, children)) => {
            for child in children {
                collect_vars_helper(child, terms, vars, seen);
            }
        }
        None => {}
    }
}

// ============================================================================
// Variable renaming utilities
// ============================================================================

/// Build a variable renaming map from a list of original variable indices.
/// Maps old_idx -> new_idx where new_idx is the position in vars.
pub fn build_var_map(vars: &[u32]) -> Vec<Option<u32>> {
    if vars.is_empty() {
        return Vec::new();
    }
    let max_var = vars.iter().copied().max().unwrap_or(0) as usize;
    let mut old_to_new = vec![None; max_var + 1];
    for (new_idx, &old_idx) in vars.iter().enumerate() {
        old_to_new[old_idx as usize] = Some(new_idx as u32);
    }
    old_to_new
}

/// Renumber variables in a term according to a mapping.
pub fn apply_var_renaming(
    term: TermId,
    old_to_new: &[Option<u32>],
    terms: &mut TermStore,
) -> TermId {
    match terms.resolve(term) {
        Some(Term::Var(idx)) => {
            let idx_usize = idx as usize;
            if idx_usize < old_to_new.len() {
                if let Some(new_idx) = old_to_new[idx_usize] {
                    return terms.var(new_idx);
                }
            }
            // Variable not in mapping - keep as is
            term
        }
        Some(Term::App(func, children)) => {
            let new_children: SmallVec<[TermId; 4]> = children
                .iter()
                .map(|&child| apply_var_renaming(child, old_to_new, terms))
                .collect();
            terms.app(func, new_children)
        }
        None => term,
    }
}

/// Renumber variables in a list of terms.
pub fn apply_var_renaming_list(
    terms_list: &[TermId],
    old_to_new: &[Option<u32>],
    terms: &mut TermStore,
) -> Boundary {
    terms_list
        .iter()
        .map(|&term| apply_var_renaming(term, old_to_new, terms))
        .collect()
}

/// Renumber variables in a term to use consecutive indices starting at 0.
pub fn renumber_vars(term: TermId, terms: &mut TermStore) -> (TermId, Vec<u32>) {
    let vars = collect_vars_ordered(term, terms);
    if vars.is_empty() {
        return (term, vec![]);
    }
    let old_to_new = build_var_map(&vars);
    let renumbered = apply_var_renaming(term, &old_to_new, terms);
    (renumbered, vars)
}

// ============================================================================
// Formatting
// ============================================================================

/// Format an NF for display.
pub fn format_nf<C: Clone + ConstraintDisplay>(
    nf: &NF<C>,
    terms: &mut TermStore,
    symbols: &SymbolStore,
) -> Result<String, String> {
    if nf.match_boundary.is_empty() && nf.build_boundary.is_empty() {
        return Ok("[] -> []".to_string());
    }

    let format_boundary = |boundary: &[TermId]| -> Result<String, String> {
        if boundary.len() == 1 {
            format_term(boundary[0], terms, symbols)
        } else {
            let parts: Result<Vec<String>, String> = boundary
                .iter()
                .map(|&t| format_term(t, terms, symbols))
                .collect();
            Ok(format!("[{}]", parts?.join(", ")))
        }
    };

    let lhs_str = format_boundary(&nf.match_boundary)?;
    let rhs_str = format_boundary(&nf.build_boundary)?;
    let constraint_str = nf.constraint.fmt_constraints(terms, symbols)?;

    if let Some(cs) = constraint_str {
        Ok(format!("{} {{ {} }} -> {}", lhs_str, cs, rhs_str))
    } else {
        Ok(format!("{} -> {}", lhs_str, rhs_str))
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::SymbolStore;

    fn setup() -> (TermStore, SymbolStore) {
        (TermStore::new(), SymbolStore::new())
    }

    #[test]
    fn canon_nf_renumbers_by_first_occurrence() {
        let (mut terms, mut symbols) = setup();
        let f = symbols.intern("f");
        let g = symbols.intern("g");

        // Create NF with non-canonical variable numbering
        // match: f($5, $3)  build: g($3, $5, $7)
        let v5 = terms.var(5);
        let v3 = terms.var(3);
        let v7 = terms.var(7);
        let match_pat = terms.app(f, smallvec::smallvec![v5, v3]);
        let build_pat = terms.app(g, smallvec::smallvec![v3, v5, v7]);

        let nf: NF<()> = NF::from_patterns(
            smallvec::smallvec![match_pat],
            smallvec::smallvec![build_pat],
            (),
            &mut terms,
        );

        // After canonicalization:
        // match vars in order: $5, $3 -> $0, $1
        // build vars: $3=$1, $5=$0, $7 is new -> $2
        // Result: match: f($0, $1)  build: g($1, $0, $2)

        assert_eq!(nf.match_boundary.len(), 1);
        assert_eq!(nf.build_boundary.len(), 1);

        // Check match boundary has vars 0, 1
        let match_vars = collect_vars_ordered_list(&nf.match_boundary, &terms);
        assert_eq!(match_vars, vec![0, 1]);

        // Check build boundary has vars 1, 0, 2
        let build_vars = collect_vars_ordered_list(&nf.build_boundary, &terms);
        assert_eq!(build_vars, vec![1, 0, 2]);
    }

    #[test]
    fn shift_nf_vars_offsets_all_variables() {
        let (mut terms, mut symbols) = setup();
        let f = symbols.intern("f");

        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let match_pat = terms.app(f, smallvec::smallvec![v0, v1]);
        let build_pat = v0;

        let nf: NF<()> = NF::new(
            smallvec::smallvec![match_pat],
            smallvec::smallvec![build_pat],
        );

        let shifted = shift_nf_vars(&nf, 10, &mut terms);

        let shifted_match_vars = collect_vars_ordered_list(&shifted.match_boundary, &terms);
        assert_eq!(shifted_match_vars, vec![10, 11]);

        let shifted_build_vars = collect_vars_ordered_list(&shifted.build_boundary, &terms);
        assert_eq!(shifted_build_vars, vec![10]);
    }

    #[test]
    fn identity_nf_has_empty_boundaries() {
        let nf: NF<()> = NF::identity(());
        assert!(nf.match_boundary.is_empty());
        assert!(nf.build_boundary.is_empty());
        assert_eq!(nf.match_arity(), 0);
        assert_eq!(nf.build_arity(), 0);
    }

    #[test]
    fn max_var_in_nf_finds_maximum() {
        let (mut terms, mut symbols) = setup();
        let f = symbols.intern("f");

        let v2 = terms.var(2);
        let v5 = terms.var(5);
        let v3 = terms.var(3);
        let match_pat = terms.app(f, smallvec::smallvec![v2, v5]);
        let build_pat = v3;

        let nf: NF<()> = NF::new(
            smallvec::smallvec![match_pat],
            smallvec::smallvec![build_pat],
        );

        assert_eq!(max_var_in_nf(&nf, &terms), Some(5));
    }

    #[test]
    fn collect_vars_ordered_preserves_first_occurrence_order() {
        let (mut terms, mut symbols) = setup();
        let f = symbols.intern("f");

        // f($3, $1, $3, $2)
        let v3 = terms.var(3);
        let v1 = terms.var(1);
        let v2 = terms.var(2);
        let term = terms.app(f, smallvec::smallvec![v3, v1, v3, v2]);

        let vars = collect_vars_ordered(term, &terms);
        assert_eq!(vars, vec![3, 1, 2]); // First occurrence order, no duplicates
    }
}
