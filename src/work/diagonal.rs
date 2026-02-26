use crate::constraint::ConstraintOps;
use crate::nf::NF;
use crate::term::TermStore;
use std::collections::VecDeque;

use super::{Work, WorkSet, WorkSetStep, WorkStep};

/// A no-op hasher that passes through a pre-hashed u64 value.
///
/// Used with `FxHashSet<u64>` where the u64 keys are already well-distributed
/// hash values (NF::hash_value()). Avoids double-hashing overhead.
#[derive(Default)]
struct IdentityHasher(u64);

impl std::hash::Hasher for IdentityHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _bytes: &[u8]) {
        // Not used for u64 keys
    }
    fn write_u64(&mut self, i: u64) {
        self.0 = i;
    }
}

type IdentityBuildHasher = std::hash::BuildHasherDefault<IdentityHasher>;
type U64HashSet = std::collections::HashSet<u64, IdentityBuildHasher>;

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
    pub(crate) left: WorkSet<C>,
    pub(crate) right: WorkSet<C>,
    pub(crate) seen_l: Vec<NF<C>>,
    pub(crate) seen_r: Vec<NF<C>>,
    seen_l_set: U64HashSet,
    seen_r_set: U64HashSet,
    pending: VecDeque<NF<C>>,
    pending_set: U64HashSet,
    pub(crate) flip: bool,
    pub(crate) strategy: S,
}

impl<C: ConstraintOps, S: JoinStrategy<C> + Default> DiagonalJoin<C, S> {
    pub(crate) fn new(left: Work<C>, right: Work<C>, strategy: S) -> Self {
        Self::new_with_sources(
            WorkSet::from_work(left),
            WorkSet::from_work(right),
            strategy,
        )
    }

    pub(crate) fn new_with_sources(left: WorkSet<C>, right: WorkSet<C>, strategy: S) -> Self {
        Self {
            left,
            right,
            seen_l: Vec::new(),
            seen_r: Vec::new(),
            seen_l_set: U64HashSet::default(),
            seen_r_set: U64HashSet::default(),
            pending: VecDeque::new(),
            pending_set: U64HashSet::default(),
            flip: false,
            strategy,
        }
    }

    pub(crate) fn new_with_seen_sources(
        left: WorkSet<C>,
        right: WorkSet<C>,
        seen_l: Vec<NF<C>>,
        seen_r: Vec<NF<C>>,
        strategy: S,
    ) -> Self {
        let mut seen_l_set = U64HashSet::default();
        for nf in &seen_l {
            seen_l_set.insert(nf.hash_value());
        }
        let mut seen_r_set = U64HashSet::default();
        for nf in &seen_r {
            seen_r_set.insert(nf.hash_value());
        }

        Self {
            left,
            right,
            seen_l,
            seen_r,
            seen_l_set,
            seen_r_set,
            pending: VecDeque::new(),
            pending_set: U64HashSet::default(),
            flip: false,
            strategy,
        }
    }

    fn take_self(&mut self) -> Self {
        std::mem::replace(
            self,
            DiagonalJoin::new_with_sources(WorkSet::new(), WorkSet::new(), S::default()),
        )
    }

    pub(crate) fn push_pending(&mut self, nf: NF<C>) {
        let hash = nf.hash_value();
        if self.pending_set.insert(hash) {
            self.pending.push_back(nf);
        }
    }

    pub(crate) fn pop_pending(&mut self) -> Option<NF<C>> {
        let nf = self.pending.pop_front()?;
        self.pending_set.remove(&nf.hash_value());
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

        let left_exhausted = self.left.is_exhausted();
        let right_exhausted = self.right.is_exhausted();

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
    /// existing `Box<Work>` for the continuation, eliminating the
    /// take-self + rebox path on hot loops.
    pub(crate) fn step_in_place(&mut self, terms: &mut TermStore) -> DiagonalStepResult<C> {
        if let Some(nf) = self.pop_pending() {
            return DiagonalStepResult::Emit(nf);
        }

        let left_exhausted = self.left.is_exhausted();
        let right_exhausted = self.right.is_exhausted();

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
        let step = match side {
            JoinSide::Left => self.left.step(terms),
            JoinSide::Right => self.right.step(terms),
        };

        match step {
            WorkSetStep::Emit(nf_val) => {
                let hash = nf_val.hash_value();
                match side {
                    JoinSide::Left => {
                        if self.seen_l_set.insert(hash) {
                            let idx = self.seen_l.len();
                            self.seen_l.push(nf_val);
                            self.with_strategy_mut(|strategy, join| {
                                strategy.on_new_left(join, idx, terms);
                            });
                        }
                        self.flip = true;
                    }
                    JoinSide::Right => {
                        if self.seen_r_set.insert(hash) {
                            let idx = self.seen_r.len();
                            self.seen_r.push(nf_val);
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
            WorkSetStep::Continue => {
                match side {
                    JoinSide::Left => {
                        self.flip = true;
                    }
                    JoinSide::Right => {
                        self.flip = false;
                    }
                }
                DiagonalStepResult::More
            }
            WorkSetStep::Exhausted => {
                match side {
                    JoinSide::Left => {
                        self.flip = true;
                    }
                    JoinSide::Right => {
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
        let step = match side {
            JoinSide::Left => self.left.step(terms),
            JoinSide::Right => self.right.step(terms),
        };

        match step {
            WorkSetStep::Emit(nf_val) => {
                let hash = nf_val.hash_value();
                match side {
                    JoinSide::Left => {
                        if self.seen_l_set.insert(hash) {
                            let idx = self.seen_l.len();
                            self.seen_l.push(nf_val);
                            self.with_strategy_mut(|strategy, join| {
                                strategy.on_new_left(join, idx, terms);
                            });
                        }
                        self.flip = true;
                    }
                    JoinSide::Right => {
                        if self.seen_r_set.insert(hash) {
                            let idx = self.seen_r.len();
                            self.seen_r.push(nf_val);
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
            WorkSetStep::Continue => {
                match side {
                    JoinSide::Left => {
                        self.flip = true;
                    }
                    JoinSide::Right => {
                        self.flip = false;
                    }
                }
                WorkStep::More(Box::new(wrap(self.take_self())))
            }
            WorkSetStep::Exhausted => {
                match side {
                    JoinSide::Left => {
                        self.flip = true;
                    }
                    JoinSide::Right => {
                        self.flip = false;
                    }
                }
                WorkStep::More(Box::new(wrap(self.take_self())))
            }
        }
    }
}
