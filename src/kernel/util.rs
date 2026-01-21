//! Shared utilities for kernel operations.
//!
//! This module contains helper functions used by both compose and meet operations.

use crate::nf::collect_vars_ordered;
use crate::subst::{apply_subst, Subst};
use crate::term::{Term, TermId, TermStore};
use crate::unify::unify;
use smallvec::SmallVec;

/// Find the maximum variable index in a list of patterns.
pub fn max_var_index_terms(pats: &[TermId], terms: &TermStore) -> Option<u32> {
    pats.iter()
        .flat_map(|&term| collect_vars_ordered(term, terms).into_iter())
        .max()
}

/// Shift all variables in a term by a given offset.
pub fn shift_vars(term: TermId, offset: u32, terms: &TermStore) -> TermId {
    match terms.resolve(term) {
        Some(Term::Var(idx)) => terms.var(idx + offset),
        Some(Term::App(func, children)) => {
            let new_children: SmallVec<[TermId; 4]> = children
                .iter()
                .map(|&c| shift_vars(c, offset, terms))
                .collect();
            terms.app(func, new_children)
        }
        None => term,
    }
}

/// Shift all variables in a list of patterns by a given offset.
pub fn shift_vars_list(pats: &[TermId], offset: u32, terms: &TermStore) -> SmallVec<[TermId; 1]> {
    if offset == 0 {
        return pats.iter().copied().collect();
    }
    pats.iter()
        .map(|&term| shift_vars(term, offset, terms))
        .collect()
}

/// Apply a substitution to a list of patterns.
pub fn apply_subst_list(
    pats: &[TermId],
    subst: &Subst,
    terms: &TermStore,
) -> SmallVec<[TermId; 1]> {
    pats.iter()
        .map(|&term| apply_subst(term, subst, terms))
        .collect()
}

/// Unify two lists of terms element-wise.
///
/// Returns the combined most general unifier if all pairs unify,
/// or None if any pair fails to unify.
pub fn unify_term_lists(left: &[TermId], right: &[TermId], terms: &TermStore) -> Option<Subst> {
    if left.len() != right.len() {
        return None;
    }

    let mut subst = Subst::new();
    for (&l, &r) in left.iter().zip(right.iter()) {
        let l_sub = apply_subst(l, &subst, terms);
        let r_sub = apply_subst(r, &subst, terms);
        let mgu = unify(l_sub, r_sub, terms)?;
        subst = compose_subst(&subst, &mgu, terms);
    }
    Some(subst)
}

/// Compose two substitutions.
///
/// The result applies `existing` first, then `new`.
pub fn compose_subst(existing: &Subst, new: &Subst, terms: &TermStore) -> Subst {
    let mut combined = Subst::new();
    for (var, term) in existing.iter() {
        let updated = apply_subst(term, new, terms);
        combined.bind(var, updated);
    }
    for (var, term) in new.iter() {
        combined.bind(var, term);
    }
    combined
}

/// Remap constraint variables by the given offset.
///
/// Returns the remapped constraint if offset is non-zero and there are variables,
/// otherwise returns a clone of the original.
pub fn remap_constraint_vars<C: crate::constraint::ConstraintOps>(
    constraint: &C,
    max_var: Option<u32>,
    offset: u32,
    terms: &TermStore,
) -> C {
    if offset == 0 {
        return constraint.clone();
    }
    match max_var {
        Some(max) => {
            let mut map = vec![None; max as usize + 1];
            for i in 0..=max {
                map[i as usize] = Some(i + offset);
            }
            constraint.remap_vars(&map, terms)
        }
        None => constraint.clone(),
    }
}
