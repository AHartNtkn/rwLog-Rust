//! Sequential composition of NFs: a ; b
//!
//! This computes the composition where output of a feeds into input of b.
//! - Match a.match_boundary against input
//! - Construct a.build_boundary
//! - Match b.match_boundary against a.build_boundary
//! - Construct b.build_boundary as final output

use crate::constraint::ConstraintOps;
use crate::nf::{canon_nf, max_var_in_nf, shift_nf_vars, NF};
use crate::term::TermStore;
#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};

use super::util::{apply_subst_list, match_term_lists};

/// Compose two NFs in sequence: a ; b
///
/// Returns None if composition fails (arity mismatch or matching failure).
pub fn compose_nf<C: ConstraintOps>(a: &NF<C>, b: &NF<C>, terms: &mut TermStore) -> Option<NF<C>> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!(
        "compose_nf",
        a_match_arity = a.match_boundary.len(),
        a_build_arity = a.build_boundary.len(),
        b_match_arity = b.match_boundary.len(),
        b_build_arity = b.build_boundary.len(),
    )
    .entered();

    // Arity check: a's output must match b's input
    if a.build_boundary.len() != b.match_boundary.len() {
        #[cfg(feature = "tracing")]
        trace!(
            a_build = a.build_boundary.len(),
            b_match = b.match_boundary.len(),
            "arity_mismatch"
        );
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

    #[cfg(feature = "tracing")]
    trace!(
        a_build = ?a.build_boundary,
        b_match_shifted = ?b_shifted.match_boundary,
        a_max_var,
        "matching_interface"
    );

    // Match a.build_boundary with b.match_boundary
    // Returns a combined substitution over the disjoint namespace.
    // The same subst is applied to both sides - since variables are renamed
    // apart, each side's terms only see their own bindings.
    let mgu = match match_term_lists(&a.build_boundary, &b_shifted.match_boundary, terms) {
        Some(subst) => {
            #[cfg(feature = "tracing")]
            trace!(mgu_size = subst.len(), "matching_success");
            subst
        }
        None => {
            #[cfg(feature = "tracing")]
            trace!("matching_failed");
            return None;
        }
    };

    // Apply the same substitution to both sides
    let new_match = apply_subst_list(&a.match_boundary, &mgu, terms);
    let new_build = apply_subst_list(&b_shifted.build_boundary, &mgu, terms);

    // Combine constraints, then apply substitution to the combined result
    let combined = match a.constraint.combine(&b_shifted.constraint) {
        Some(c) => c,
        None => {
            #[cfg(feature = "tracing")]
            trace!("compose_constraint_conflict");
            return None;
        }
    };
    let combined = combined.apply_subst(&mgu, terms);

    let normalized = match combined.normalize(terms) {
        Some(result) => result,
        None => {
            #[cfg(feature = "tracing")]
            trace!("compose_constraint_unsat");
            return None;
        }
    };

    // Construct and canonicalize result
    let result = NF::with_constraint(new_match, new_build, normalized);
    Some(canon_nf(&result, terms))
}


#[cfg(test)]
#[path = "../tests/kernel_compose.rs"]
mod tests;
