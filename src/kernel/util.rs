//! Shared utilities for kernel operations.
//!
//! This module contains helper functions used by both compose and meet operations.

use crate::matching::{
    match_terms_combined, match_terms_combined_shifted,
    match_terms_combined_shifted_with_left_renaming,
};
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

/// Match two lists of terms element-wise with virtual shifting on the right side,
/// returning the raw combined substitution instead of splitting.
///
/// This is the same as `match_term_lists_shifted` but returns the raw combined
/// `Subst` instead of splitting into (left, right) halves via `split_match_subst`.
/// Variables `< right_offset` are left-side bindings; variables `>= right_offset`
/// are right-side bindings.
///
/// Used in meet_nf to defer splitting until factor_tensor_with_subst can resolve
/// bindings lazily.
pub fn match_term_lists_shifted_combined(
    left: &[TermId],
    right: &[TermId],
    right_offset: u32,
    shifted_vars: &[TermId],
    terms: &mut TermStore,
) -> Option<Subst> {
    if left.len() != right.len() {
        return None;
    }

    let mut subst = Subst::new();
    for (&l, &r) in left.iter().zip(right.iter()) {
        if subst.is_empty() && !shifted_vars.is_empty() {
            let match_subst = match_terms_combined_shifted(l, r, shifted_vars, terms)?;
            subst = match_subst;
        } else {
            let l_sub = apply_subst(l, &subst, terms);
            let r_sub = apply_subst_shifted(r, &subst, right_offset, shifted_vars, terms);
            let match_subst = match_terms_combined(l_sub, r_sub, terms)?;
            subst = compose_subst(&subst, &match_subst, terms);
        }
    }
    Some(subst)
}

/// Match two lists of ORIGINAL (not yet substituted) terms element-wise,
/// applying a pre-existing substitution (`pre_subst`) to each pair before matching.
///
/// This fuses the `apply_subst_list` + `apply_subst_shifted_list` + `match_term_lists_combined`
/// pipeline into a single pass, avoiding bulk intermediate term creation.
///
/// The left terms have `pre_subst` applied directly. The right terms have `pre_subst`
/// applied with virtual shifting. The resulting match subst is composed with `pre_subst`
/// to produce a single combined substitution.
///
/// Returns `Some(combined_subst)` where `combined_subst = compose(pre_subst, rhs_match_subst)`,
/// or `None` if matching fails.
pub fn match_rhs_lists_with_pre_subst(
    left: &[TermId],
    right: &[TermId],
    pre_subst: &Subst,
    right_offset: u32,
    shifted_vars: &[TermId],
    terms: &mut TermStore,
) -> Option<Subst> {
    if left.len() != right.len() {
        return None;
    }

    let mut rhs_subst = Subst::new();
    for (&l, &r) in left.iter().zip(right.iter()) {
        // Apply pre_subst to both sides, then apply incremental rhs_subst on top.
        let l_pre = apply_subst(l, pre_subst, terms);
        let r_pre = apply_subst_shifted(r, pre_subst, right_offset, shifted_vars, terms);

        if rhs_subst.is_empty() {
            let match_subst = match_terms_combined(l_pre, r_pre, terms)?;
            rhs_subst = match_subst;
        } else {
            let l_sub = apply_subst(l_pre, &rhs_subst, terms);
            let r_sub = apply_subst(r_pre, &rhs_subst, terms);
            let match_subst = match_terms_combined(l_sub, r_sub, terms)?;
            rhs_subst = compose_subst(&rhs_subst, &match_subst, terms);
        }
    }

    // Compose pre_subst with the rhs match result to get the full combined subst.
    Some(compose_subst(pre_subst, &rhs_subst, terms))
}

/// Match two lists of terms element-wise with left-side variable renaming
/// and right-side virtual shifting, returning the raw combined substitution.
///
/// Left-side variables are renamed via `left_rhs_map` during matching instead
/// of eagerly applying `apply_var_renaming_list`. Right-side variables are
/// virtually shifted as in `match_term_lists_shifted`.
///
/// Returns the raw combined substitution instead of splitting it into
/// (left, right) halves. This avoids the `split_match_subst` cost when the
/// caller can consume the combined substitution directly, resolving chains
/// lazily. Variables `< right_offset` are left-side bindings; variables
/// `>= right_offset` are right-side bindings (already shifted by matching).
///
/// This is used in compose_nf to avoid the tree walk of `collect_tensor(a)`
/// for the 99%+ of compose attempts that fail matching.
pub fn match_term_lists_shifted_with_left_renaming_combined(
    left: &[TermId],
    right: &[TermId],
    left_rhs_map: &[u32],
    right_offset: u32,
    shifted_vars: &[TermId],
    terms: &mut TermStore,
) -> Option<Subst> {
    if left.len() != right.len() {
        return None;
    }

    // Pre-compute the Option-wrapped renaming map once, outside the loop.
    // This avoids a heap allocation on every iteration of the fallback path.
    let rhs_map_opt: Vec<Option<u32>> = left_rhs_map.iter().map(|&v| Some(v)).collect();

    let mut subst = Subst::new();
    for (idx, (&l, &r)) in left.iter().zip(right.iter()).enumerate() {
        if subst.is_empty() && idx == 0 {
            let match_subst = match_terms_combined_shifted_with_left_renaming(
                l,
                r,
                left_rhs_map,
                shifted_vars,
                terms,
            )?;
            subst = match_subst;
        } else {
            let l_renamed = crate::nf::apply_var_renaming(l, &rhs_map_opt, terms);
            let l_sub = apply_subst(l_renamed, &subst, terms);
            let r_sub = apply_subst_shifted(r, &subst, right_offset, shifted_vars, terms);
            let match_subst = match_terms_combined(l_sub, r_sub, terms)?;
            subst = compose_subst(&subst, &match_subst, terms);
        }
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
    let max_all = max_var.max(max_constraint);
    max_all.map(|max| (0..=max).map(|i| Some(i + offset)).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    #[test]
    fn match_term_lists_shifted_combined_keeps_equality_for_app_rule_shape() {
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

        let combined =
            match_term_lists_shifted_combined(&[left], &[right], offset, &shifted_vars, &mut terms)
                .expect("expected match");

        // Split combined subst to verify correctness.
        let (left_sub, right_sub) =
            crate::matching::split_match_subst(&combined, offset, &mut terms);

        let left_applied = apply_subst(left, &left_sub, &mut terms);
        let right_applied =
            apply_subst_shifted(right, &right_sub, offset, &shifted_vars, &mut terms);

        assert_eq!(
            left_applied, right_applied,
            "split substitutions must make both sides equal"
        );
    }
}
