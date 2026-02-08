//! Shared utilities for kernel operations.
//!
//! This module contains helper functions used by both compose and meet operations.

use crate::matching::match_terms_combined;
use crate::nf::collect_vars_ordered;
use crate::subst::{apply_subst, Subst};
use crate::term::{Term, TermId, TermStore};
use smallvec::SmallVec;

/// Find the maximum variable index in a list of patterns.
pub fn max_var_index_terms(pats: &[TermId], terms: &TermStore) -> Option<u32> {
    pats.iter()
        .flat_map(|&term| collect_vars_ordered(term, terms).into_iter())
        .max()
}

/// Shift all variables in a term by a given offset.
///
/// Uses batched read_lock to avoid per-node lock acquisition and avoids
/// cloning children SmallVecs by copying TermIds (which are Copy).
pub fn shift_vars(term: TermId, offset: u32, terms: &mut TermStore) -> TermId {
    use crate::symbol::FuncId;

    // Fast path: zero offset changes nothing
    if offset == 0 {
        return term;
    }

    // Fast path: ground term (no variables to shift).
    // Just a bit test on TermId — zero memory access.
    if term.is_ground() {
        return term;
    }

    enum Work {
        Visit(TermId),
        BuildApp(TermId, FuncId, usize), // (original_tid, functor, child_count)
    }

    let mut work_stack: SmallVec<[Work; 16]> = SmallVec::new();
    let mut result_stack: SmallVec<[TermId; 16]> = SmallVec::new();

    work_stack.push(Work::Visit(term));

    while let Some(item) = work_stack.pop() {
        match item {
            Work::BuildApp(orig_tid, func, n) => {
                let start = result_stack.len() - n;
                // Check if all children are unchanged (ground subtree case).
                let guard = terms.read_lock();
                let all_same = match guard.get(orig_tid) {
                    Some(Term::App(_, orig_children)) => {
                        orig_children.len() == n
                            && orig_children
                                .iter()
                                .zip(&result_stack[start..])
                                .all(|(a, b)| *a == *b)
                    }
                    _ => false,
                };
                drop(guard);
                if all_same {
                    result_stack.truncate(start);
                    result_stack.push(orig_tid);
                } else {
                    let new_term = terms.app_from_slice(func, &result_stack[start..]);
                    result_stack.truncate(start);
                    result_stack.push(new_term);
                }
            }
            Work::Visit(tid) => {
                // Fast path: skip ground subtrees (just a bit test, no memory access).
                if tid.is_ground() {
                    result_stack.push(tid);
                    continue;
                }

                let guard = terms.read_lock();
                match guard.get(tid) {
                    Some(Term::Var(idx)) => {
                        let shifted = *idx + offset;
                        drop(guard);
                        result_stack.push(terms.var(shifted));
                    }
                    Some(Term::App(_, children)) if children.is_empty() => {
                        result_stack.push(tid);
                    }
                    Some(Term::App(f, children)) => {
                        let func = *f;
                        let n = children.len();
                        work_stack.push(Work::BuildApp(tid, func, n));
                        for i in (0..n).rev() {
                            work_stack.push(Work::Visit(children[i]));
                        }
                    }
                    None => {
                        result_stack.push(tid);
                    }
                }
            }
        }
    }

    debug_assert_eq!(result_stack.len(), 1);
    result_stack.pop().unwrap()
}

/// Shift all variables in a list of patterns by a given offset.
pub fn shift_vars_list(
    pats: &[TermId],
    offset: u32,
    terms: &mut TermStore,
) -> SmallVec<[TermId; 1]> {
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
    terms: &mut TermStore,
) -> SmallVec<[TermId; 1]> {
    pats.iter()
        .map(|&term| apply_subst(term, subst, terms))
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
    if left.len() != right.len() {
        return None;
    }

    let mut subst = Subst::new();
    for (&l, &r) in left.iter().zip(right.iter()) {
        let l_sub = apply_subst(l, &subst, terms);
        let r_sub = apply_subst(r, &subst, terms);
        let match_subst = match_terms_combined(l_sub, r_sub, terms)?;
        subst = compose_subst(&subst, &match_subst, terms);
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
    if offset == 0 {
        return constraint.clone();
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
            constraint.remap_vars(&map, terms)
        }
        None => constraint.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    #[test]
    fn match_term_lists_disjoint_keeps_equality_for_app_rule_shape() {
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

        let offset = max_var_index_terms(&[left], &terms)
            .map(|v| v + 1)
            .unwrap_or(0);
        let right_shifted = shift_vars(right, offset, &mut terms);

        let (left_sub, right_sub) = match_term_lists(&[left], &[right_shifted], offset, &mut terms)
            .expect("expected match");

        let left_applied = apply_subst(left, &left_sub, &mut terms);
        let right_applied = apply_subst(right_shifted, &right_sub, &mut terms);

        assert_eq!(
            left_applied, right_applied,
            "split substitutions must make both sides equal"
        );
    }
}
