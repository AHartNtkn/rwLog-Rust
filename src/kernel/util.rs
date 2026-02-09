//! Shared utilities for kernel operations.
//!
//! This module contains helper functions used by both compose and meet operations.

use crate::matching::{match_terms_combined, match_terms_combined_shifted};
use crate::nf::collect_vars_ordered;
use crate::subst::{apply_subst, apply_subst_shifted, Subst};
use crate::term::{TermId, TermStore};
use smallvec::SmallVec;

/// Find the maximum variable index in a list of patterns.
pub fn max_var_index_terms(pats: &[TermId], terms: &TermStore) -> Option<u32> {
    pats.iter()
        .flat_map(|&term| collect_vars_ordered(term, terms).into_iter())
        .max()
}

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

/// Pre-create shifted variable TermIds for virtual shifting.
///
/// Returns `shifted_vars[j] = terms.var(j + offset)` for `j` in `0..=max_var`.
/// Must be called before acquiring any read locks on the TermStore.
pub fn pre_create_shifted_vars(
    max_var: Option<u32>,
    offset: u32,
    terms: &TermStore,
) -> SmallVec<[TermId; 8]> {
    if offset == 0 {
        return SmallVec::new();
    }
    match max_var {
        Some(max) => (0..=max).map(|j| terms.var(j + offset)).collect(),
        None => SmallVec::new(),
    }
}

/// Apply a substitution to a list of patterns, virtually shifting variables.
pub fn apply_subst_shifted_list(
    pats: &[TermId],
    subst: &Subst,
    var_offset: u32,
    shifted_vars: &[TermId],
    terms: &mut TermStore,
) -> SmallVec<[TermId; 1]> {
    pats.iter()
        .map(|&term| apply_subst_shifted(term, subst, var_offset, shifted_vars, terms))
        .collect()
}

/// Match two lists of terms element-wise in disjoint namespaces.
///
/// Returns a pair of substitutions (left, right) when all pairs match,
/// or None if any pair fails to match.
pub fn match_term_lists(
    left: &[TermId],
    right: &[TermId],
    right_offset: u32,
    terms: &mut TermStore,
) -> Option<(Subst, Subst)> {
    match_term_lists_shifted(left, right, right_offset, &[], terms)
}

/// Match two lists of terms element-wise with virtual shifting on the right side.
///
/// The right terms are unshifted; variables are virtually offset by `right_offset`
/// during substitution application. This avoids physically creating shifted terms.
///
/// When `shifted_vars` is empty, behaves identically to standard element-wise matching.
pub fn match_term_lists_shifted(
    left: &[TermId],
    right: &[TermId],
    right_offset: u32,
    shifted_vars: &[TermId],
    terms: &mut TermStore,
) -> Option<(Subst, Subst)> {
    if left.len() != right.len() {
        return None;
    }

    let mut subst = Subst::new();
    for (&l, &r) in left.iter().zip(right.iter()) {
        if subst.is_empty() && !shifted_vars.is_empty() {
            // Fast path: subst is empty, so apply_subst(l, &empty) == l.
            // Instead of walking the right tree to shift variables via
            // apply_subst_shifted, use offset-aware matching that handles
            // the variable offset internally during traversal.
            let match_subst = match_terms_combined_shifted(l, r, shifted_vars, terms)?;
            subst = match_subst;
        } else {
            let l_sub = apply_subst(l, &subst, terms);
            let r_sub = apply_subst_shifted(r, &subst, right_offset, shifted_vars, terms);
            let match_subst = match_terms_combined(l_sub, r_sub, terms)?;
            subst = compose_subst(&subst, &match_subst, terms);
        }
    }
    Some(crate::matching::split_match_subst(
        &subst,
        right_offset,
        terms,
    ))
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

/// Build a remap map that shifts all variable indices by `offset`.
///
/// Returns `None` if no remapping is needed (offset is zero or no variables exist).
/// The map has `map[i] = Some(i + offset)` for `i` in `0..=max`.
pub fn build_remap_map<C: crate::constraint::ConstraintOps>(
    constraint: &C,
    max_var: Option<u32>,
    offset: u32,
    terms: &TermStore,
) -> Option<Vec<Option<u32>>> {
    if offset == 0 {
        return None;
    }
    let mut constraint_vars = Vec::new();
    constraint.collect_vars(terms, &mut constraint_vars);
    constraint_vars.sort_unstable();
    constraint_vars.dedup();
    let max_constraint = constraint_vars.last().copied();
    let max_all = match (max_var, max_constraint) {
        (Some(a), Some(b)) => Some(a.max(b)),
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        (None, None) => None,
    };
    match max_all {
        Some(max) => {
            let mut map = vec![None; max as usize + 1];
            for i in 0..=max {
                map[i as usize] = Some(i + offset);
            }
            Some(map)
        }
        None => None,
    }
}

/// Remap constraint variables by the given offset.
///
/// Returns the remapped constraint if offset is non-zero and there are variables,
/// otherwise returns a clone of the original.
pub fn remap_constraint_vars<C: crate::constraint::ConstraintOps>(
    constraint: &C,
    max_var: Option<u32>,
    offset: u32,
    terms: &mut TermStore,
) -> C {
    match build_remap_map(constraint, max_var, offset, terms) {
        Some(map) => constraint.remap_vars(&map, terms),
        None => constraint.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    #[test]
    fn match_term_lists_shifted_keeps_equality_for_app_rule_shape() {
        let mut parser = Parser::new();
        let left = parser
            .parse_term("(f $x (c z))")
            .expect("parse left")
            .term_id;
        let right = parser
            .parse_term("(f (f (b $x) $y) $z)")
            .expect("parse right")
            .term_id;
        let mut terms = parser.take_terms();

        let right_max_var = max_var_index_terms(&[right], &terms);
        let offset = max_var_index_terms(&[left], &terms)
            .map(|v| v + 1)
            .unwrap_or(0);
        let shifted_vars = pre_create_shifted_vars(right_max_var, offset, &terms);

        let (left_sub, right_sub) =
            match_term_lists_shifted(&[left], &[right], offset, &shifted_vars, &mut terms)
                .expect("expected match");

        let left_applied = apply_subst(left, &left_sub, &mut terms);
        let right_applied =
            apply_subst_shifted(right, &right_sub, offset, &shifted_vars, &mut terms);

        assert_eq!(
            left_applied, right_applied,
            "split substitutions must make both sides equal"
        );
    }
}
