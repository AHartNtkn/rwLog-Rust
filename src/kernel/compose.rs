use crate::constraint::ConstraintOps;
use crate::nf::{collect_tensor, factor_tensor, NF};
use crate::term::TermStore;
#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};

use super::util::{
    apply_subst_list, match_term_lists, max_var_index_terms, remap_constraint_vars, shift_vars_list,
};

/// Compose two NFs in sequence: a ; b
///
/// This computes the composition where:
/// - First, a's match patterns are matched against input
/// - Variables are routed through a's DropFresh
/// - a's build patterns are constructed
/// - b's match patterns are matched against a's output
/// - Variables are routed through b's DropFresh
/// - b's build patterns are constructed
///
/// Returns None if composition fails (matching failure at interface).
pub fn compose_nf<C: ConstraintOps>(a: &NF<C>, b: &NF<C>, terms: &mut TermStore) -> Option<NF<C>> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!(
        "compose_nf",
        a_match_arity = a.match_pats.len(),
        a_build_arity = a.build_pats.len(),
        b_match_arity = b.match_pats.len(),
        b_build_arity = b.build_pats.len(),
        a_drop_fresh_in = a.drop_fresh.in_arity,
        a_drop_fresh_out = a.drop_fresh.out_arity,
        b_drop_fresh_in = b.drop_fresh.in_arity,
        b_drop_fresh_out = b.drop_fresh.out_arity,
    )
    .entered();

    if a.build_pats.len() != b.match_pats.len() {
        #[cfg(feature = "tracing")]
        trace!(
            a_build = a.build_pats.len(),
            b_match = b.match_pats.len(),
            "arity_mismatch"
        );
        return None; // Arity mismatch
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

    #[cfg(feature = "tracing")]
    trace!(
        a_rhs = ?rw1.rhs,
        b_lhs_shifted = ?rw2.lhs,
        b_var_offset,
        "matching_interface"
    );

    let matching = match match_term_lists(&rw1.rhs, &rw2.lhs, b_var_offset, terms) {
        Some(matching) => {
            #[cfg(feature = "tracing")]
            trace!(
                left_bindings = matching.left.len(),
                right_bindings = matching.right.len(),
                "matching_success"
            );
            matching
        }
        None => {
            #[cfg(feature = "tracing")]
            trace!("matching_failed");
            return None;
        }
    };

    let mut new_match = apply_subst_list(&rw1.lhs, &matching.left, terms);
    let mut new_build = apply_subst_list(&rw2.rhs, &matching.right, terms);

    let b_constraint =
        remap_constraint_vars(&b.drop_fresh.constraint, b_max_var, b_var_offset, terms);

    let a_constraint = a.drop_fresh.constraint.apply_subst(&matching.left, terms);
    let b_constraint = b_constraint.apply_subst(&matching.right, terms);
    let combined = match a_constraint.combine(&b_constraint) {
        Some(c) => c,
        None => {
            #[cfg(feature = "tracing")]
            trace!("compose_constraint_conflict");
            return None;
        }
    };

    let (normalized, subst_opt) = match combined.normalize(terms) {
        Some(result) => result,
        None => {
            #[cfg(feature = "tracing")]
            trace!("compose_constraint_unsat");
            return None;
        }
    };
    if let Some(subst) = subst_opt {
        new_match = apply_subst_list(&new_match, &subst, terms);
        new_build = apply_subst_list(&new_build, &subst, terms);
    }

    Some(factor_tensor(new_match, new_build, normalized, terms))
}


#[cfg(test)]
#[path = "../tests/kernel_compose.rs"]
mod tests;
