//! Shared utilities for kernel operations.
//!
//! This module contains helper functions used by both compose and meet operations.

use crate::matching::match_disjoint;
use crate::subst::{apply_subst, Subst};
use crate::term::TermId;
use crate::term::TermStore;
use smallvec::SmallVec;

/// Apply a substitution to a list of patterns.
pub fn apply_subst_list(
    pats: &[TermId],
    subst: &Subst,
    terms: &mut TermStore,
) -> SmallVec<[TermId; 1]> {
    pats.iter()
        .map(|&term| apply_subst(term, subst, terms))
        .collect()
}

/// Match two lists of terms element-wise.
///
/// Returns a combined substitution over the disjoint namespace.
/// Since variables are renamed apart before matching, the same substitution
/// can be applied to terms from both sides - each side's terms only contain
/// their own variables, so irrelevant bindings are harmlessly ignored.
pub fn match_term_lists(
    left: &[TermId],
    right: &[TermId],
    terms: &mut TermStore,
) -> Option<Subst> {
    if left.len() != right.len() {
        return None;
    }

    let mut subst = Subst::new();
    for (&l, &r) in left.iter().zip(right.iter()) {
        let l_sub = apply_subst(l, &subst, terms);
        let r_sub = apply_subst(r, &subst, terms);
        let match_subst = match_disjoint(l_sub, r_sub, terms)?;
        subst = compose_subst(&subst, &match_subst, terms);
    }
    Some(subst)
}

/// Compose two substitutions.
///
/// The result applies `existing` first, then `new`.
pub fn compose_subst(existing: &Subst, new: &Subst, terms: &mut TermStore) -> Subst {
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
