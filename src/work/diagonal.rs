use crate::constraint::ConstraintOps;
use crate::nf::NF;
use crate::node::{step_node, Node, NodeStep};
use crate::term::TermStore;
use rustc_hash::FxHashSet;
use std::collections::VecDeque;

use super::{Work, WorkStep};

/// Result of stepping a DiagonalJoin in-place (no allocation).
pub(crate) enum DiagonalStepResult<C: ConstraintOps> {
    /// Emit an answer; DiagonalJoin has been updated in-place for continuation.
    Emit(NF<C>),
    /// No answer yet; DiagonalJoin has been updated in-place for continuation.
    More,
    /// Done; no more answers.
    Done,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum JoinOutcome {
    Done,
    More,
}

pub(crate) trait JoinStrategy<C: ConstraintOps>: Clone + std::fmt::Debug + Default {
    fn pre_step(
        &mut self,
        _join: &mut DiagonalJoin<C, Self>,
        _terms: &mut TermStore,
    ) -> Option<NF<C>>
    where
        Self: Sized,
    {
        None
    }

    fn on_new_left(
        &mut self,
        join: &mut DiagonalJoin<C, Self>,
        left_idx: usize,
        terms: &mut TermStore,
    ) where
        Self: Sized;

    fn on_new_right(
        &mut self,
        join: &mut DiagonalJoin<C, Self>,
        right_idx: usize,
        terms: &mut TermStore,
    ) where
        Self: Sized;

    fn check_done(
        &self,
        join: &DiagonalJoin<C, Self>,
        left_exhausted: bool,
        right_exhausted: bool,
    ) -> Option<JoinOutcome>
    where
        Self: Sized;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum JoinSide {
    Left,
    Right,
}

#[derive(Clone, Debug)]
pub(crate) struct DiagonalJoin<C: ConstraintOps, S: JoinStrategy<C> + Default> {
    pub(crate) left: Box<Node<C>>,
    pub(crate) right: Box<Node<C>>,
    pub(crate) seen_l: Vec<NF<C>>,
    pub(crate) seen_r: Vec<NF<C>>,
    seen_l_set: FxHashSet<NF<C>>,
    seen_r_set: FxHashSet<NF<C>>,
    pending: VecDeque<NF<C>>,
    pending_set: FxHashSet<NF<C>>,
    pub(crate) flip: bool,
    pub(crate) strategy: S,
}

impl<C: ConstraintOps, S: JoinStrategy<C> + Default> DiagonalJoin<C, S> {
    pub(crate) fn new(left: Node<C>, right: Node<C>, strategy: S) -> Self {
        Self {
            left: Box::new(left),
            right: Box::new(right),
            seen_l: Vec::new(),
            seen_r: Vec::new(),
            seen_l_set: FxHashSet::default(),
            seen_r_set: FxHashSet::default(),
            pending: VecDeque::new(),
            pending_set: FxHashSet::default(),
            flip: false,
            strategy,
        }
    }

    fn take_self(&mut self) -> Self {
        std::mem::replace(
            self,
            DiagonalJoin::new(Node::Fail, Node::Fail, S::default()),
        )
    }

    pub(crate) fn push_pending(&mut self, nf: NF<C>) {
        if self.pending_set.insert(nf.clone()) {
            self.pending.push_back(nf);
        }
    }

    pub(crate) fn pop_pending(&mut self) -> Option<NF<C>> {
        let nf = self.pending.pop_front()?;
        self.pending_set.remove(&nf);
        Some(nf)
    }

    pub(crate) fn seen_l_len(&self) -> usize {
        self.seen_l.len()
    }

    pub(crate) fn seen_r_len(&self) -> usize {
        self.seen_r.len()
    }

    pub(crate) fn seen_l_at(&self, idx: usize) -> &NF<C> {
        &self.seen_l[idx]
    }

    pub(crate) fn seen_r_at(&self, idx: usize) -> &NF<C> {
        &self.seen_r[idx]
    }

    #[cfg(test)]
    pub(crate) fn pending_is_empty(&self) -> bool {
        self.pending.is_empty()
    }

    #[cfg(test)]
    pub(crate) fn push_pending_for_test(&mut self, nf: NF<C>) {
        self.push_pending(nf);
    }

    pub(crate) fn step(&mut self, terms: &mut TermStore, wrap: fn(Self) -> Work<C>) -> WorkStep<C> {
        if let Some(nf) = self.pop_pending() {
            return WorkStep::Emit(nf, Box::new(wrap(self.take_self())));
        }

        let left_exhausted = matches!(*self.left, Node::Fail);
        let right_exhausted = matches!(*self.right, Node::Fail);

        if let Some(nf) = self.with_strategy_mut(|strategy, join| strategy.pre_step(join, terms)) {
            return WorkStep::Emit(nf, Box::new(wrap(self.take_self())));
        }

        if let Some(outcome) = self
            .strategy
            .check_done(self, left_exhausted, right_exhausted)
        {
            return match outcome {
                JoinOutcome::Done => WorkStep::Done,
                JoinOutcome::More => WorkStep::More(Box::new(wrap(self.take_self()))),
            };
        }

        let pull_from_right = if left_exhausted {
            true
        } else if right_exhausted {
            false
        } else {
            self.flip
        };

        if pull_from_right {
            self.pull_side(JoinSide::Right, terms, wrap)
        } else {
            self.pull_side(JoinSide::Left, terms, wrap)
        }
    }

    /// Step in-place, returning a simple result without allocating Box<Work>.
    ///
    /// Same logic as `step()` but mutates self in-place and returns
    /// `DiagonalStepResult` instead of `WorkStep`. The caller reuses the
    /// existing `Box<Work>` for the continuation, eliminating 3 heap
    /// allocations per step (2× dummy Box<Node::Fail> + 1× Box<Work>).
    pub(crate) fn step_in_place(&mut self, terms: &mut TermStore) -> DiagonalStepResult<C> {
        if let Some(nf) = self.pop_pending() {
            return DiagonalStepResult::Emit(nf);
        }

        let left_exhausted = matches!(*self.left, Node::Fail);
        let right_exhausted = matches!(*self.right, Node::Fail);

        if let Some(nf) = self.with_strategy_mut(|strategy, join| strategy.pre_step(join, terms)) {
            return DiagonalStepResult::Emit(nf);
        }

        if let Some(outcome) = self
            .strategy
            .check_done(self, left_exhausted, right_exhausted)
        {
            return match outcome {
                JoinOutcome::Done => DiagonalStepResult::Done,
                JoinOutcome::More => DiagonalStepResult::More,
            };
        }

        let pull_from_right = if left_exhausted {
            true
        } else if right_exhausted {
            false
        } else {
            self.flip
        };

        if pull_from_right {
            self.pull_side_in_place(JoinSide::Right, terms)
        } else {
            self.pull_side_in_place(JoinSide::Left, terms)
        }
    }

    fn pull_side_in_place(
        &mut self,
        side: JoinSide,
        terms: &mut TermStore,
    ) -> DiagonalStepResult<C> {
        let current = match side {
            JoinSide::Left => std::mem::replace(&mut *self.left, Node::Fail),
            JoinSide::Right => std::mem::replace(&mut *self.right, Node::Fail),
        };

        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                match side {
                    JoinSide::Left => {
                        *self.left = rest;
                        if self.seen_l_set.insert(nf.clone()) {
                            let idx = self.seen_l.len();
                            self.seen_l.push(nf);
                            self.with_strategy_mut(|strategy, join| {
                                strategy.on_new_left(join, idx, terms);
                            });
                        }
                        self.flip = true;
                    }
                    JoinSide::Right => {
                        *self.right = rest;
                        if self.seen_r_set.insert(nf.clone()) {
                            let idx = self.seen_r.len();
                            self.seen_r.push(nf);
                            self.with_strategy_mut(|strategy, join| {
                                strategy.on_new_right(join, idx, terms);
                            });
                        }
                        self.flip = false;
                    }
                }

                if let Some(result) = self.pop_pending() {
                    DiagonalStepResult::Emit(result)
                } else {
                    DiagonalStepResult::More
                }
            }
            NodeStep::Continue(rest) => {
                match side {
                    JoinSide::Left => {
                        *self.left = rest;
                        self.flip = true;
                    }
                    JoinSide::Right => {
                        *self.right = rest;
                        self.flip = false;
                    }
                }
                DiagonalStepResult::More
            }
            NodeStep::Exhausted => {
                match side {
                    JoinSide::Left => {
                        *self.left = Node::Fail;
                        self.flip = true;
                    }
                    JoinSide::Right => {
                        *self.right = Node::Fail;
                        self.flip = false;
                    }
                }
                DiagonalStepResult::More
            }
        }
    }

    fn with_strategy_mut<R>(&mut self, f: impl FnOnce(&mut S, &mut Self) -> R) -> R {
        let mut strategy = std::mem::take(&mut self.strategy);
        let result = f(&mut strategy, self);
        self.strategy = strategy;
        result
    }

    fn pull_side(
        &mut self,
        side: JoinSide,
        terms: &mut TermStore,
        wrap: fn(Self) -> Work<C>,
    ) -> WorkStep<C> {
        let current = match side {
            JoinSide::Left => std::mem::replace(&mut *self.left, Node::Fail),
            JoinSide::Right => std::mem::replace(&mut *self.right, Node::Fail),
        };

        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                match side {
                    JoinSide::Left => {
                        *self.left = rest;
                        if self.seen_l_set.insert(nf.clone()) {
                            let idx = self.seen_l.len();
                            self.seen_l.push(nf);
                            self.with_strategy_mut(|strategy, join| {
                                strategy.on_new_left(join, idx, terms);
                            });
                        }
                        self.flip = true;
                    }
                    JoinSide::Right => {
                        *self.right = rest;
                        if self.seen_r_set.insert(nf.clone()) {
                            let idx = self.seen_r.len();
                            self.seen_r.push(nf);
                            self.with_strategy_mut(|strategy, join| {
                                strategy.on_new_right(join, idx, terms);
                            });
                        }
                        self.flip = false;
                    }
                }

                if let Some(result) = self.pop_pending() {
                    WorkStep::Emit(result, Box::new(wrap(self.take_self())))
                } else {
                    WorkStep::More(Box::new(wrap(self.take_self())))
                }
            }
            NodeStep::Continue(rest) => {
                match side {
                    JoinSide::Left => {
                        *self.left = rest;
                        self.flip = true;
                    }
                    JoinSide::Right => {
                        *self.right = rest;
                        self.flip = false;
                    }
                }
                WorkStep::More(Box::new(wrap(self.take_self())))
            }
            NodeStep::Exhausted => {
                match side {
                    JoinSide::Left => {
                        *self.left = Node::Fail;
                        self.flip = true;
                    }
                    JoinSide::Right => {
                        *self.right = Node::Fail;
                        self.flip = false;
                    }
                }
                WorkStep::More(Box::new(wrap(self.take_self())))
            }
        }
    }
}
