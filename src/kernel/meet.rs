//! Meet (intersection) of two NFs.
//!
//! The meet represents the relation that satisfies BOTH a AND b.
//! For inputs, the input must match both a's and b's match patterns.
//! For outputs, the output must satisfy both a's and b's build patterns.

use crate::constraint::ConstraintOps;
use crate::nf::{canon_nf, max_var_in_nf, shift_nf_vars, NF};
use crate::term::TermStore;
#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};

use super::util::{apply_subst_list, compose_subst, match_term_lists};

/// Compute the meet (intersection) of two NFs.
///
/// Returns None if the meet is empty (patterns are incompatible).
pub fn meet_nf<C: ConstraintOps>(a: &NF<C>, b: &NF<C>, terms: &mut TermStore) -> Option<NF<C>> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!(
        "meet_nf",
        a_match_arity = a.match_boundary.len(),
        a_build_arity = a.build_boundary.len(),
        b_match_arity = b.match_boundary.len(),
        b_build_arity = b.build_boundary.len(),
    )
    .entered();

    // Arity check: both boundaries must match
    if a.match_boundary.len() != b.match_boundary.len()
        || a.build_boundary.len() != b.build_boundary.len()
    {
        #[cfg(feature = "tracing")]
        trace!("meet_arity_mismatch");
        return None;
    }

    // Compute offset to rename b's variables to disjoint namespace
    let a_max_var = max_var_in_nf(a, terms).map(|v| v + 1).unwrap_or(0);

    // Shift b's variables if needed
    let b_shifted = if a_max_var > 0 {
        shift_nf_vars(b, a_max_var, terms)
    } else {
        b.clone()
    };

    // Match match boundaries - get a combined substitution
    let mgu_lhs = match match_term_lists(&a.match_boundary, &b_shifted.match_boundary, terms) {
        Some(subst) => subst,
        None => {
            #[cfg(feature = "tracing")]
            trace!("meet_match_failed");
            return None;
        }
    };

    // Apply LHS matching to build boundaries, then match those
    let a_build_subst = apply_subst_list(&a.build_boundary, &mgu_lhs, terms);
    let b_build_subst = apply_subst_list(&b_shifted.build_boundary, &mgu_lhs, terms);

    let mgu_rhs = match match_term_lists(&a_build_subst, &b_build_subst, terms) {
        Some(subst) => subst,
        None => {
            #[cfg(feature = "tracing")]
            trace!("meet_build_failed");
            return None;
        }
    };

    // Compose both substitutions into one combined MGU
    let mgu = compose_subst(&mgu_lhs, &mgu_rhs, terms);

    // Compute final boundaries by applying the combined substitution
    let final_match = apply_subst_list(&a.match_boundary, &mgu, terms);
    let final_build = apply_subst_list(&a.build_boundary, &mgu, terms);

    // Combine constraints, then apply the combined substitution
    let combined = match a.constraint.combine(&b_shifted.constraint) {
        Some(c) => c,
        None => {
            #[cfg(feature = "tracing")]
            trace!("meet_constraint_conflict");
            return None;
        }
    };
    let combined = combined.apply_subst(&mgu, terms);

    let normalized = match combined.normalize(terms) {
        Some(result) => result,
        None => {
            #[cfg(feature = "tracing")]
            trace!("meet_constraint_unsat");
            return None;
        }
    };

    #[cfg(feature = "tracing")]
    trace!("meet_success");

    // Construct and canonicalize result
    let result = NF::with_constraint(final_match, final_build, normalized);
    Some(canon_nf(&result, terms))
}


#[cfg(test)]
#[path = "../tests/kernel_meet.rs"]
mod tests;
