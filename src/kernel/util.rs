//! Shared utilities for kernel operations.
//!
//! This module contains helper functions used by both compose and meet operations.

use crate::constraint::ConstraintOps;
use crate::matching::{
    match_terms_combined, match_terms_combined_shifted,
    match_terms_combined_shifted_with_left_renaming,
};
use crate::subst::{apply_subst, apply_subst_shifted, Subst};
use crate::term::{Term, TermId, TermStore};
use smallvec::SmallVec;

/// Find the maximum variable index in a list of patterns.
///
/// Uses the TermStore's cached var_range metadata for O(1) per stored term,
/// and inline variable index extraction for inline vars. No tree traversal.
#[cfg(test)]
pub fn max_var_index_terms(pats: &[TermId], terms: &TermStore) -> Option<u32> {
    let guard = terms.read_lock();
    let mut max_var: Option<u32> = None;
    for &tid in pats {
        let term_max = if tid.is_inline_var() {
            Some(tid.inline_var_index())
        } else if tid.is_ground() {
            None
        } else if let Some((_, t_max)) = guard.var_range(tid) {
            Some(t_max)
        } else {
            None
        };
        max_var = match (max_var, term_max) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (a, None) => a,
            (None, b) => b,
        };
    }
    max_var
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

    // Lazily computed Option-wrapped renaming map. Only allocated when the
    // fallback path (idx > 0) is reached, avoiding the heap allocation for
    // the common single-pattern case.
    let mut rhs_map_opt: Option<Vec<Option<u32>>> = None;

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
            let map = rhs_map_opt
                .get_or_insert_with(|| left_rhs_map.iter().map(|&v| Some(v)).collect());
            let l_renamed = crate::nf::apply_var_renaming(l, map, terms);
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
fn compose_subst(existing: &Subst, new: &Subst, terms: &mut TermStore) -> Subst {
    if existing.is_empty() {
        return new.clone();
    }
    if new.is_empty() {
        return existing.clone();
    }
    let mut combined = Subst::new();
    for (var, term) in existing.iter() {
        let updated = apply_subst(term, new, terms);
        combined.bind(var, updated);
    }
    for (var, term) in new.iter() {
        // Only add bindings from `new` that aren't already in `existing`'s domain.
        // Overlapping vars were already handled in the first loop as
        // apply_subst(existing[var], new), which is the correct composition.
        if existing.get(var).is_none() {
            combined.bind(var, term);
        }
    }
    combined
}

/// Check if two term IDs have provably different root functors, meaning
/// their matching/meet must fail. Handles both inline nullary constants
/// (compare TermIds directly) and non-inline App nodes (compare root functors).
/// Returns false for variables or other inline types (cannot rule out match).
#[inline]
pub fn root_functor_mismatch(a_id: TermId, b_id: TermId, terms: &mut TermStore) -> bool {
    // Variables can match anything — cannot rule out.
    if a_id.is_inline_var() || b_id.is_inline_var() {
        return false;
    }
    // Inline nullary constants: different TermIds = different ground terms.
    if a_id.is_inline_nullary() && b_id.is_inline_nullary() {
        return a_id != b_id;
    }
    // Non-inline App nodes: compare root functors.
    if !a_id.is_inline() && !b_id.is_inline() {
        let a_root = match terms.get_unlocked(a_id) {
            Some(Term::App(f, _)) => Some(*f),
            _ => None,
        };
        let b_root = match terms.get_unlocked(b_id) {
            Some(Term::App(f, _)) => Some(*f),
            _ => None,
        };
        if let (Some(af), Some(bf)) = (a_root, b_root) {
            return af != bf;
        }
    }
    // One inline nullary + one non-inline App: they have different structure.
    // An inline nullary is always a 0-ary App, while non-inline App has arity >= 1.
    // These can never match.
    if (a_id.is_inline_nullary() && !b_id.is_inline())
        || (!a_id.is_inline() && b_id.is_inline_nullary())
    {
        // Check: non-inline side is actually an App (not a variable ref).
        let non_inline = if a_id.is_inline_nullary() { b_id } else { a_id };
        if let Some(Term::App(_, _)) = terms.get_unlocked(non_inline) {
            return true; // 0-ary vs >=1-ary: definitely different
        }
    }
    false
}

/// Apply substitution to both constraints, combine, and normalize.
///
/// This is the shared constraint-handling pipeline used by both compose_nf and meet_nf:
/// 1. Apply `subst` to a's constraint
/// 2. Optionally remap b's constraint variables by `b_var_offset`, then apply `subst`
/// 3. Combine the two constraints
/// 4. Normalize the combined constraint
///
/// Returns `None` if constraints conflict or are unsatisfiable.
pub fn apply_and_normalize_constraints<C: ConstraintOps>(
    a_constraint: &C,
    b_constraint: &C,
    b_max_var: Option<u32>,
    b_var_offset: u32,
    subst: &Subst,
    terms: &mut TermStore,
) -> Option<(C, Option<Subst>)> {
    let a_applied = a_constraint.apply_subst(subst, terms);
    let b_applied = match build_remap_map(b_constraint, b_max_var, b_var_offset, terms) {
        Some(map) => b_constraint.remap_and_apply_subst(&map, subst, terms),
        None => b_constraint.apply_subst(subst, terms),
    };
    let combined = a_applied.combine_owned(b_applied)?;
    combined.normalize_owned(terms)
}

/// Build a remap map that shifts all variable indices by `offset`.
///
/// Returns `None` if no remapping is needed (offset is zero or no variables exist).
/// The map has `map[i] = Some(i + offset)` for `i` in `0..=max`.
///
/// Constraint-only variables can have indices outside `rwt_max_var()`,
/// so we must collect constraint vars and take the max of both.
fn build_remap_map<C: ConstraintOps>(
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
    let max_constraint = constraint_vars.iter().copied().max();
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
