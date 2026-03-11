use crate::constraint::ConstraintOps;
use crate::kernel::meet_nf;
#[cfg(test)]
use crate::nf::NF;
use crate::node::Node;
use crate::term::TermStore;

use super::diagonal::{DiagonalJoin, JoinOutcome, JoinStrategy};
use super::InPlaceStepResult;
use super::{Work, WorkStep};

/// Meet work: fair diagonal join for conjunction/intersection.
///
/// Represents: And(left_node, right_node)
///
/// Uses fair diagonal enumeration:
/// - Pull alternately from left and right nodes
/// - When a new answer arrives, meet with all seen from other side
/// - Successful meets are queued in pending
///
/// Step policy:
/// 1. If pending non-empty: emit front
/// 2. Alternate pulling from left/right (flip)
/// 3. When new answer arrives, meet with all seen from other side
/// 4. Push successful meets to pending
#[derive(Clone, Debug, Default)]
struct MeetStrategy;

impl<C: ConstraintOps> JoinStrategy<C> for MeetStrategy {
    fn on_new_left(
        &mut self,
        join: &mut DiagonalJoin<C, Self>,
        left_idx: usize,
        terms: &mut TermStore,
    ) {
        let left = join.seen_l_at(left_idx).clone();
        for idx in 0..join.seen_r_len() {
            let right = join.seen_r_at(idx).clone();
            if let Some(met) = meet_nf(&left, &right, terms) {
                join.push_pending(met);
            }
        }
    }

    fn on_new_right(
        &mut self,
        join: &mut DiagonalJoin<C, Self>,
        right_idx: usize,
        terms: &mut TermStore,
    ) {
        let right = join.seen_r_at(right_idx).clone();
        for idx in 0..join.seen_l_len() {
            let left = join.seen_l_at(idx).clone();
            if let Some(met) = meet_nf(&left, &right, terms) {
                join.push_pending(met);
            }
        }
    }

    fn check_done(
        &self,
        _join: &DiagonalJoin<C, Self>,
        left_exhausted: bool,
        right_exhausted: bool,
    ) -> Option<JoinOutcome> {
        if left_exhausted && right_exhausted {
            Some(JoinOutcome::Done)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug)]
pub struct MeetWork<C: ConstraintOps> {
    core: DiagonalJoin<C, MeetStrategy>,
}

impl<C: ConstraintOps> MeetWork<C> {
    /// Create a new MeetWork from two nodes.
    pub fn new(left: Node<C>, right: Node<C>) -> Self {
        Self {
            core: DiagonalJoin::new(left, right, MeetStrategy),
        }
    }

    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        self.core.step(terms, Self::wrap)
    }

    #[inline(never)]
    pub(crate) fn step_in_place(&mut self, terms: &mut TermStore) -> InPlaceStepResult<C> {
        self.core.step_in_place(terms)
    }

    fn wrap(core: DiagonalJoin<C, MeetStrategy>) -> Work<C> {
        Work::Meet(MeetWork { core })
    }

    #[cfg(test)]
    pub(crate) fn left(&self) -> &Node<C> {
        &self.core.left
    }

    #[cfg(test)]
    pub(crate) fn right(&self) -> &Node<C> {
        &self.core.right
    }

    #[cfg(test)]
    pub(crate) fn flip(&self) -> bool {
        self.core.flip
    }

    #[cfg(test)]
    pub(crate) fn set_flip(&mut self, value: bool) {
        self.core.flip = value;
    }

    #[cfg(test)]
    pub(crate) fn seen_l(&self) -> &[NF<C>] {
        &self.core.seen_l
    }

    #[cfg(test)]
    pub(crate) fn seen_r(&self) -> &[NF<C>] {
        &self.core.seen_r
    }

    #[cfg(test)]
    pub(crate) fn pending_is_empty(&self) -> bool {
        self.core.pending_is_empty()
    }

    #[cfg(test)]
    pub(crate) fn push_pending_for_test(&mut self, nf: NF<C>) {
        self.core.push_pending_for_test(nf);
    }
}
