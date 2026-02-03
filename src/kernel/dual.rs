//! Dual operation for NFs - swaps match and build boundaries.
//!
//! The dual of a relation R is its converse: if R relates a to b,
//! then dual(R) relates b to a.

use crate::nf::NF;

/// Compute the dual of a Normal Form.
///
/// The dual swaps match_boundary and build_boundary.
///
/// Properties:
/// - dual(dual(nf)) == nf (involution)
/// - If nf represents relation R, dual(nf) represents the converse R^(-1)
pub fn dual_nf<C: Clone>(nf: &NF<C>) -> NF<C> {
    NF {
        match_boundary: nf.build_boundary.clone(),
        build_boundary: nf.match_boundary.clone(),
        constraint: nf.constraint.clone(),
    }
}


#[cfg(test)]
#[path = "../tests/kernel_dual.rs"]
mod tests;
