use crate::constraint::ConstraintOps;
use crate::kernel::compose_nf;
use crate::node::Node;
use crate::term::TermStore;
use std::collections::VecDeque;

use super::diagonal::{DiagonalJoin, DiagonalStepResult, JoinOutcome, JoinStrategy};
use super::{Work, WorkStep};

#[derive(Clone, Debug)]
enum ComposeCursor {
    Left {
        left_idx: usize,
        right_idx: usize,
        right_limit: usize,
    },
    Right {
        right_idx: usize,
        left_idx: usize,
        left_limit: usize,
    },
}

#[derive(Clone, Debug)]
struct ComposeStrategy {
    pair_queue: VecDeque<ComposeCursor>,
}

impl ComposeStrategy {
    fn new() -> Self {
        Self {
            pair_queue: VecDeque::new(),
        }
    }

    fn enqueue_pairs_left<C: ConstraintOps>(
        &mut self,
        join: &DiagonalJoin<C, Self>,
        left_idx: usize,
    ) {
        let right_limit = join.seen_r_len();
        if right_limit == 0 {
            return;
        }
        self.pair_queue.push_back(ComposeCursor::Left {
            left_idx,
            right_idx: 0,
            right_limit,
        });
    }

    fn enqueue_pairs_right<C: ConstraintOps>(
        &mut self,
        join: &DiagonalJoin<C, Self>,
        right_idx: usize,
    ) {
        let left_limit = join.seen_l_len();
        if left_limit == 0 {
            return;
        }
        self.pair_queue.push_back(ComposeCursor::Right {
            right_idx,
            left_idx: 0,
            left_limit,
        });
    }

    fn process_pair_queue<C: ConstraintOps>(
        &mut self,
        join: &mut DiagonalJoin<C, Self>,
        terms: &mut TermStore,
    ) -> Option<crate::nf::NF<C>> {
        let mut cursor = self.pair_queue.pop_front()?;

        loop {
            match &mut cursor {
                ComposeCursor::Left {
                    left_idx,
                    right_idx,
                    right_limit,
                } => {
                    if *right_idx >= *right_limit {
                        break;
                    }
                    let left_nf = join.seen_l_at(*left_idx);
                    let right_nf = join.seen_r_at(*right_idx);
                    if let Some(nf) = Self::compose_pair(left_nf, right_nf, terms) {
                        join.push_pending(nf);
                    }
                    *right_idx += 1;
                }
                ComposeCursor::Right {
                    right_idx,
                    left_idx,
                    left_limit,
                } => {
                    if *left_idx >= *left_limit {
                        break;
                    }
                    let left_nf = join.seen_l_at(*left_idx);
                    let right_nf = join.seen_r_at(*right_idx);
                    if let Some(nf) = Self::compose_pair(left_nf, right_nf, terms) {
                        join.push_pending(nf);
                    }
                    *left_idx += 1;
                }
            }
        }

        join.pop_pending()
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
    fn pre_step(
        &mut self,
        join: &mut DiagonalJoin<C, Self>,
        terms: &mut TermStore,
    ) -> Option<crate::nf::NF<C>> {
        self.process_pair_queue(join, terms)
    }

    fn on_new_left(
        &mut self,
        join: &mut DiagonalJoin<C, Self>,
        left_idx: usize,
        _terms: &mut TermStore,
    ) {
        self.enqueue_pairs_left(join, left_idx);
    }

    fn on_new_right(
        &mut self,
        join: &mut DiagonalJoin<C, Self>,
        right_idx: usize,
        _terms: &mut TermStore,
    ) {
        self.enqueue_pairs_right(join, right_idx);
    }

    fn check_done(
        &self,
        join: &DiagonalJoin<C, Self>,
        left_exhausted: bool,
        right_exhausted: bool,
    ) -> Option<JoinOutcome> {
        if left_exhausted && join.seen_l.is_empty() && self.pair_queue.is_empty() {
            return Some(JoinOutcome::Done);
        }
        if right_exhausted && join.seen_r.is_empty() && self.pair_queue.is_empty() {
            return Some(JoinOutcome::Done);
        }
        if left_exhausted && right_exhausted {
            if self.pair_queue.is_empty() {
                return Some(JoinOutcome::Done);
            }
            return Some(JoinOutcome::More);
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
