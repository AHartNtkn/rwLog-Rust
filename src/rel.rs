//! Rel IR - Relation expressions for the direction-agnostic evaluation model.
//!
//! Rel replaces the old Goal enum with a more principled representation
//! that supports structural dual operations.

use crate::kernel::dual_nf;
use crate::nf::NF;
use std::sync::Arc;

/// Identifier for recursive relation bindings (Fix/Call).
pub type RelId = u32;

/// Relation expression - the IR for evaluation.
///
/// Each variant represents a different way to combine relations:
/// - `Zero`: empty relation (always fails)
/// - `Atom(nf)`: single span (atomic relation from NF)
/// - `Or(a, b)`: union/disjunction
/// - `And(a, b)`: intersection/conjunction
/// - `Seq(xs)`: n-ary sequential composition
/// - `Fix(id, body)`: recursive binding (μ binder)
/// - `Call(id)`: recursive reference
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Rel<C> {
    /// Empty relation - always fails.
    Zero,
    /// Atomic relation from a single NF span.
    Atom(Arc<NF<C>>),
    /// Union (disjunction) of two relations.
    Or(Arc<Rel<C>>, Arc<Rel<C>>),
    /// Intersection (conjunction) of two relations.
    And(Arc<Rel<C>>, Arc<Rel<C>>),
    /// Sequential composition of relations.
    Seq(Arc<[Arc<Rel<C>>]>),
    /// Recursive binding: Fix(id, body) binds `id` to be used in `body`.
    Fix(RelId, Arc<Rel<C>>),
    /// Recursive reference to a Fix-bound relation.
    Call(RelId),
}

/// Compute the structural dual of a relation.
///
/// The dual of a relation R is its converse relation R^(-1).
/// If R relates input to output, dual(R) relates output to input.
///
/// Properties:
/// - dual(dual(r)) == r (involution)
/// - dual(Zero) = Zero
/// - dual(Atom(nf)) = Atom(dual_nf(nf))
/// - dual(Or(a,b)) = Or(dual(a), dual(b)) (no swap)
/// - dual(And(a,b)) = And(dual(a), dual(b)) (no swap)
/// - dual(Seq([x0..xn])) = Seq([dual(xn)..dual(x0)]) (REVERSE and dual)
/// - dual(Fix(id, body)) = Fix(id, dual(body))
/// - dual(Call(id)) = Call(id)
pub fn dual<C: Clone>(rel: &Rel<C>) -> Rel<C> {
    match rel {
        Rel::Zero => Rel::Zero,

        Rel::Atom(nf) => Rel::Atom(Arc::new(dual_nf(nf))),

        Rel::Or(a, b) => Rel::Or(Arc::new(dual(a)), Arc::new(dual(b))),

        Rel::And(a, b) => Rel::And(Arc::new(dual(a)), Arc::new(dual(b))),

        Rel::Seq(xs) => {
            // CRITICAL: Reverse the sequence AND dual each element
            let dualed: Vec<Arc<Rel<C>>> = xs
                .iter()
                .rev() // Reverse order
                .map(|x| Arc::new(dual(x))) // Dual each element
                .collect();
            Rel::Seq(Arc::from(dualed))
        }

        Rel::Fix(id, body) => Rel::Fix(*id, Arc::new(dual(body))),

        Rel::Call(id) => Rel::Call(*id),
    }
}


#[cfg(test)]
#[path = "tests/rel.rs"]
mod tests;
