use crate::constraint::ConstraintOps;
use crate::kernel::compose_nf;
use crate::node::Node;
use crate::term::TermStore;

use super::diagonal::{DiagonalJoin, DiagonalStepResult, JoinOutcome, JoinStrategy};
use super::{Work, WorkStep};

/// Eager compose strategy: when a new NF arrives from either side, immediately
/// compose it with all existing opposite-side NFs and push results to pending.
/// This eliminates the cursor-based VecDeque and processes all pairs in a tight
/// loop at the point of arrival.
#[derive(Clone, Debug)]
struct ComposeStrategy;

impl ComposeStrategy {
    fn new() -> Self {
        Self
    }

    fn is_empty_identity<C: ConstraintOps>(nf: &crate::nf::NF<C>) -> bool {
        nf.match_pats.is_empty()
            && nf.build_pats.is_empty()
            && nf.drop_fresh.in_arity == 0
            && nf.drop_fresh.out_arity == 0
    }

    fn compose_pair<C: ConstraintOps>(
        left_nf: &crate::nf::NF<C>,
        right_nf: &crate::nf::NF<C>,
        terms: &mut TermStore,
    ) -> Option<crate::nf::NF<C>> {
        if Self::is_empty_identity(right_nf) {
            return Some(left_nf.clone());
        }
        if Self::is_empty_identity(left_nf) {
            return Some(right_nf.clone());
        }
        compose_nf(left_nf, right_nf, terms)
    }
}

impl Default for ComposeStrategy {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: ConstraintOps> JoinStrategy<C> for ComposeStrategy {
    fn on_new_left(
        &mut self,
        join: &mut DiagonalJoin<C, Self>,
        left_idx: usize,
        terms: &mut TermStore,
    ) {
        let right_len = join.seen_r_len();
        for right_idx in 0..right_len {
            let left_nf = join.seen_l_at(left_idx);
            let right_nf = join.seen_r_at(right_idx);
            if let Some(nf) = Self::compose_pair(left_nf, right_nf, terms) {
                join.push_pending(nf);
            }
        }
    }

    fn on_new_right(
        &mut self,
        join: &mut DiagonalJoin<C, Self>,
        right_idx: usize,
        terms: &mut TermStore,
    ) {
        let left_len = join.seen_l_len();
        for left_idx in 0..left_len {
            let left_nf = join.seen_l_at(left_idx);
            let right_nf = join.seen_r_at(right_idx);
            if let Some(nf) = Self::compose_pair(left_nf, right_nf, terms) {
                join.push_pending(nf);
            }
        }
    }

    fn check_done(
        &self,
        join: &DiagonalJoin<C, Self>,
        left_exhausted: bool,
        right_exhausted: bool,
    ) -> Option<JoinOutcome> {
        if left_exhausted && join.seen_l.is_empty() {
            return Some(JoinOutcome::Done);
        }
        if right_exhausted && join.seen_r.is_empty() {
            return Some(JoinOutcome::Done);
        }
        if left_exhausted && right_exhausted {
            return Some(JoinOutcome::Done);
        }
        None
    }
}

#[derive(Clone, Debug)]
pub struct ComposeWork<C: ConstraintOps> {
    core: DiagonalJoin<C, ComposeStrategy>,
}

impl<C: ConstraintOps> ComposeWork<C> {
    /// Create a new ComposeWork from two nodes.
    pub fn new(left: Node<C>, right: Node<C>) -> Self {
        Self {
            core: DiagonalJoin::new(left, right, ComposeStrategy::new()),
        }
    }

    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        self.core.step(terms, Self::wrap)
    }

    #[inline(never)]
    pub(crate) fn step_in_place(&mut self, terms: &mut TermStore) -> DiagonalStepResult<C> {
        self.core.step_in_place(terms)
    }

    fn wrap(core: DiagonalJoin<C, ComposeStrategy>) -> Work<C> {
        Work::Compose(ComposeWork { core })
    }

    #[cfg(test)]
    pub(crate) fn left(&self) -> &Node<C> {
        &self.core.left
    }

    #[cfg(test)]
    pub(crate) fn right(&self) -> &Node<C> {
        &self.core.right
    }
}
