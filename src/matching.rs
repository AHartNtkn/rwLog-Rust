//! Matching (not unification) for disjoint variable namespaces.
//!
//! Cross-side comparisons must use matching with separate substitutions per side.
//! Callers must rename apart (disjoint namespaces) before matching.

use crate::subst::Subst;
use crate::term::{Term, TermId, TermStore};
use smallvec::SmallVec;

#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};

/// A most-general matching as a pair of substitutions, one per side.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Matching {
    pub left: Subst,
    pub right: Subst,
}

/// Split a combined substitution into per-side substitutions.
///
/// `right_offset` is the offset used to rename the right side into a disjoint
/// variable namespace, so variables `< right_offset` belong to the left side.
pub(crate) fn split_subst(subst: &Subst, right_offset: u32) -> Matching {
    let mut left = Subst::new();
    let mut right = Subst::new();
    for (var, term) in subst.iter() {
        if var < right_offset {
            left.bind(var, term);
        } else {
            right.bind(var, term);
        }
    }
    Matching { left, right }
}

/// Match two terms that are already in disjoint variable namespaces.
///
/// Returns a combined substitution over the disjoint namespace.
/// This is matching over disjoint namespaces; callers must rename apart before use.
///
/// Uses an explicit worklist to avoid recursion.
/// Implements occurs-check to prevent infinite terms.
pub(crate) fn match_disjoint(t1: TermId, t2: TermId, terms: &TermStore) -> Option<Subst> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!("match_terms", ?t1, ?t2).entered();

    let mut subst = Subst::new();
    let mut worklist: SmallVec<[(TermId, TermId); 32]> = SmallVec::new();
    worklist.push((t1, t2));

    while let Some((a, b)) = worklist.pop() {
        // Dereference variables through the substitution
        let a_deref = deref(a, &subst, terms);
        let b_deref = deref(b, &subst, terms);

        if a_deref == b_deref {
            // Same term - already matched
            continue;
        }

        match (terms.resolve(a_deref), terms.resolve(b_deref)) {
            (Some(Term::Var(idx_a)), Some(Term::Var(idx_b))) => {
                // Both variables - bind one to the other
                // Prefer binding higher-indexed to lower-indexed for consistency
                if idx_a < idx_b {
                    subst.bind(idx_b, a_deref);
                } else {
                    subst.bind(idx_a, b_deref);
                }
            }
            (Some(Term::Var(idx)), Some(Term::App(_, _))) => {
                // Variable vs App - occurs check then bind
                if occurs(idx, b_deref, &subst, terms) {
                    #[cfg(feature = "tracing")]
                    trace!(var = idx, "match_occurs_check_failed");
                    return None; // Occurs check failed
                }
                subst.bind(idx, b_deref);
            }
            (Some(Term::App(_, _)), Some(Term::Var(idx))) => {
                // App vs Variable - occurs check then bind
                if occurs(idx, a_deref, &subst, terms) {
                    #[cfg(feature = "tracing")]
                    trace!(var = idx, "match_occurs_check_failed");
                    return None; // Occurs check failed
                }
                subst.bind(idx, a_deref);
            }
            (Some(Term::App(f1, children1)), Some(Term::App(f2, children2))) => {
                // Both Apps - must have same functor and arity
                if f1 != f2 {
                    #[cfg(feature = "tracing")]
                    trace!("match_functor_mismatch");
                    return None; // Different functors
                }
                if children1.len() != children2.len() {
                    #[cfg(feature = "tracing")]
                    trace!("match_arity_mismatch");
                    return None; // Different arities
                }
                // Add children pairs to worklist
                for (c1, c2) in children1.iter().zip(children2.iter()) {
                    worklist.push((*c1, *c2));
                }
            }
            _ => {
                // One or both terms are invalid
                #[cfg(feature = "tracing")]
                trace!("match_invalid_term");
                return None;
            }
        }
    }

    #[cfg(feature = "tracing")]
    trace!(bindings = subst.len(), "match_success");

    Some(subst)
}

/// Match two terms whose variable namespaces are disjoint.
///
/// `right_offset` is the offset used to rename the right side into a disjoint
/// namespace (all right vars are `>= right_offset`).
pub fn match_terms_disjoint(
    left: TermId,
    right: TermId,
    right_offset: u32,
    terms: &TermStore,
) -> Option<Matching> {
    let subst = match_disjoint(left, right, terms)?;
    Some(split_subst(&subst, right_offset))
}

/// Dereference a term through the substitution.
/// If the term is a variable bound in the substitution, follow the chain.
fn deref(term: TermId, subst: &Subst, terms: &TermStore) -> TermId {
    let mut current = term;
    loop {
        match terms.resolve(current) {
            Some(Term::Var(idx)) => {
                if let Some(bound) = subst.get(idx) {
                    current = bound;
                } else {
                    return current;
                }
            }
            _ => return current,
        }
    }
}

/// Occurs check: does variable `var` occur in term `term`?
/// Used to prevent creating infinite (cyclic) terms.
fn occurs(var: u32, term: TermId, subst: &Subst, terms: &TermStore) -> bool {
    let mut stack: SmallVec<[TermId; 16]> = SmallVec::new();
    stack.push(term);

    while let Some(t) = stack.pop() {
        let t_deref = deref(t, subst, terms);
        match terms.resolve(t_deref) {
            Some(Term::Var(idx)) => {
                if idx == var {
                    return true;
                }
            }
            Some(Term::App(_, children)) => {
                for child in children.iter() {
                    stack.push(*child);
                }
            }
            None => {}
        }
    }

    false
}


#[cfg(test)]
#[path = "tests/matching.rs"]
mod tests;
