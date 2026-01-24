use crate::constraint::ConstraintOps;
use crate::nf::{collect_tensor, factor_tensor, NF};
use crate::term::TermStore;
#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};

use super::util::{
    apply_subst_list, match_term_lists, max_var_index_terms, remap_constraint_vars, shift_vars_list,
};

/// Compute the meet (intersection) of two NFs.
///
/// The meet represents the relation that satisfies BOTH a AND b.
/// For inputs, this means the input must match both a's and b's match patterns.
/// For outputs, this means the output must satisfy both a's and b's build patterns.
///
/// Returns None if the meet is empty (patterns are incompatible).
pub fn meet_nf<C: ConstraintOps>(a: &NF<C>, b: &NF<C>, terms: &mut TermStore) -> Option<NF<C>> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!(
        "meet_nf",
        a_match_arity = a.match_pats.len(),
        a_build_arity = a.build_pats.len(),
        b_match_arity = b.match_pats.len(),
        b_build_arity = b.build_pats.len(),
    )
    .entered();

    if a.match_pats.len() != b.match_pats.len() || a.build_pats.len() != b.build_pats.len() {
        #[cfg(feature = "tracing")]
        trace!("meet_arity_mismatch");
        return None;
    }

    let rw1 = collect_tensor(a, terms);
    let mut rw2 = collect_tensor(b, terms);
    let b_max_var = max_var_index_terms(&rw2.lhs, terms).max(max_var_index_terms(&rw2.rhs, terms));

    let b_var_offset = max_var_index_terms(&rw1.lhs, terms)
        .max(max_var_index_terms(&rw1.rhs, terms))
        .map(|v| v + 1)
        .unwrap_or(0);

    if b_var_offset != 0 {
        rw2.lhs = shift_vars_list(&rw2.lhs, b_var_offset, terms);
        rw2.rhs = shift_vars_list(&rw2.rhs, b_var_offset, terms);
    }

    let matching_lhs = match match_term_lists(&rw1.lhs, &rw2.lhs, b_var_offset, terms) {
        Some(matching) => matching,
        None => {
            #[cfg(feature = "tracing")]
            trace!("meet_match_failed");
            return None;
        }
    };

    let unified_lhs = apply_subst_list(&rw1.lhs, &matching_lhs.left, terms);
    let a_rhs_subst = apply_subst_list(&rw1.rhs, &matching_lhs.left, terms);
    let b_rhs_subst = apply_subst_list(&rw2.rhs, &matching_lhs.right, terms);

    let matching_rhs = match match_term_lists(&a_rhs_subst, &b_rhs_subst, b_var_offset, terms) {
        Some(matching) => matching,
        None => {
            #[cfg(feature = "tracing")]
            trace!("meet_build_failed");
            return None;
        }
    };

    let mut final_lhs = apply_subst_list(&unified_lhs, &matching_rhs.left, terms);
    let mut final_rhs = apply_subst_list(&a_rhs_subst, &matching_rhs.left, terms);

    let b_constraint =
        remap_constraint_vars(&b.drop_fresh.constraint, b_max_var, b_var_offset, terms);

    let a_constraint = a.drop_fresh.constraint.apply_subst(&matching_lhs.left, terms);
    let a_constraint = a_constraint.apply_subst(&matching_rhs.left, terms);
    let b_constraint = b_constraint.apply_subst(&matching_lhs.right, terms);
    let b_constraint = b_constraint.apply_subst(&matching_rhs.right, terms);

    let combined = match a_constraint.combine(&b_constraint) {
        Some(c) => c,
        None => {
            #[cfg(feature = "tracing")]
            trace!("meet_constraint_conflict");
            return None;
        }
    };

    let (normalized, subst_opt) = match combined.normalize(terms) {
        Some(result) => result,
        None => {
            #[cfg(feature = "tracing")]
            trace!("meet_constraint_unsat");
            return None;
        }
    };
    if let Some(subst) = subst_opt {
        final_lhs = apply_subst_list(&final_lhs, &subst, terms);
        final_rhs = apply_subst_list(&final_rhs, &subst, terms);
    }

    #[cfg(feature = "tracing")]
    trace!("meet_success");

    Some(factor_tensor(final_lhs, final_rhs, normalized, terms))
}


#[cfg(test)]
#[path = "../tests/kernel_meet.rs"]
mod tests;
