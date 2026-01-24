use crate::constraint::ConstraintOps;
use crate::nf::{collect_tensor, factor_tensor, NF};
use crate::term::TermStore;
#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};

use super::util::{
    apply_subst_list, max_var_index_terms, remap_constraint_vars, shift_vars_list, unify_term_lists,
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
/// Returns None if composition fails (unification failure at interface).
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
        "unifying_interface"
    );

    let mgu = match unify_term_lists(&rw1.rhs, &rw2.lhs, terms) {
        Some(mgu) => {
            #[cfg(feature = "tracing")]
            trace!(mgu_size = mgu.len(), "unification_success");
            mgu
        }
        None => {
            #[cfg(feature = "tracing")]
            trace!("unification_failed");
            return None;
        }
    };

    let mut new_match = apply_subst_list(&rw1.lhs, &mgu, terms);
    let mut new_build = apply_subst_list(&rw2.rhs, &mgu, terms);

    let b_constraint =
        remap_constraint_vars(&b.drop_fresh.constraint, b_max_var, b_var_offset, terms);

    let combined = match a.drop_fresh.constraint.combine(&b_constraint) {
        Some(c) => c,
        None => {
            #[cfg(feature = "tracing")]
            trace!("compose_constraint_conflict");
            return None;
        }
    };
    let combined = combined.apply_subst(&mgu, terms);

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
mod tests;
