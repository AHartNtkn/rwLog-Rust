//! Dual operation for NFs - swaps match/build and inverts DropFresh direction.
//!
//! The dual of a relation R is its converse: if R relates a to b,
//! then dual(R) relates b to a.

use crate::constraint::ConstraintOps;
use crate::drop_fresh::DropFresh;
use crate::nf::{collect_tensor, factor_tensor, NF};
use crate::term::TermStore;
use smallvec::SmallVec;

/// Compute the dual of a DropFresh.
///
/// The dual swaps input and output arities, and inverts the mapping.
/// After inversion, the map is re-sorted by first coordinate to maintain
/// the strictly-increasing invariant.
///
/// Properties:
/// - dual(dual(w)) == w (involution)
/// - dual swaps in_arity and out_arity
/// - Constraint is preserved
pub fn dual_drop_fresh<C: Clone>(drop_fresh: &DropFresh<C>) -> DropFresh<C> {
    // Swap arities
    let new_in_arity = drop_fresh.out_arity;
    let new_out_arity = drop_fresh.in_arity;

    // Invert map: (i, j) -> (j, i)
    let mut inverted: SmallVec<[(u32, u32); 4]> =
        drop_fresh.map.iter().map(|&(i, j)| (j, i)).collect();

    // CRITICAL: Re-sort by first coordinate to maintain invariant
    // The original map is sorted by i, so after inversion the j values
    // (now first) may not be in order.
    inverted.sort_by_key(|&(first, _)| first);

    DropFresh {
        in_arity: new_in_arity,
        out_arity: new_out_arity,
        map: inverted,
        constraint: drop_fresh.constraint.clone(),
    }
}

/// Compute the dual of a Normal Form.
///
/// The dual:
/// - Swaps match_pats and build_pats
/// - Dualizes the DropFresh
///
/// Properties:
/// - dual(dual(nf)) == nf (involution)
/// - If nf represents relation R, dual(nf) represents the converse R^(-1)
pub fn dual_nf<C: ConstraintOps>(nf: &NF<C>, terms: &mut TermStore) -> NF<C> {
    let direct = collect_tensor(nf, terms);
    factor_tensor(direct.rhs, direct.lhs, direct.constraint, terms)
}


#[cfg(test)]
#[path = "../tests/kernel_dual.rs"]
mod tests;
