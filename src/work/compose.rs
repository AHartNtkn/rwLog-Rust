use crate::constraint::ConstraintOps;
use crate::kernel::compose_nf;
use crate::term::TermStore;
use std::collections::VecDeque;

use super::diagonal::{DiagonalJoin, DiagonalStepResult, JoinOutcome, JoinStrategy};
use super::{build_root_tag, match_root_tag, tags_compatible, RootTag, Work, WorkSet, WorkStep};

#[derive(Clone, Debug)]
enum ComposeCursor {
    Left {
        left_idx: usize,
        /// Next right index to scan.
        next_right_idx: usize,
        /// Snapshot of seen_r length when this cursor was enqueued.
        /// Limits the scan so each pair is considered exactly once.
        right_limit: usize,
    },
    Right {
        right_idx: usize,
        /// Next left index to scan.
        next_left_idx: usize,
        /// Snapshot of seen_l length when this cursor was enqueued.
        /// Limits the scan so each pair is considered exactly once.
        left_limit: usize,
    },
}

#[derive(Clone, Debug)]
struct ComposeStrategy {
    pair_queue: VecDeque<ComposeCursor>,
    /// For each left NF index, its build root tag.
    left_build_tags: Vec<RootTag>,
    /// For each right NF index, its match root tag.
    right_match_tags: Vec<RootTag>,
}

impl ComposeStrategy {
    const MAX_PAIR_CHECKS_PER_STEP: usize = 128;

    fn new() -> Self {
        Self {
            pair_queue: VecDeque::new(),
            left_build_tags: Vec::new(),
            right_match_tags: Vec::new(),
        }
    }

    #[inline]
    fn pair_tags_compatible(&self, left_idx: usize, right_idx: usize) -> bool {
        tags_compatible(
            self.left_build_tags[left_idx],
            self.right_match_tags[right_idx],
        )
    }

    /// Enqueue compose pairs for a new left NF.
    /// The build tag must already have been pushed to `left_build_tags`.
    fn enqueue_pairs_left_with_tag<C: ConstraintOps>(
        &mut self,
        join: &DiagonalJoin<C, Self>,
        left_idx: usize,
        _build_tag: RootTag,
    ) {
        let right_limit = join.seen_r_len();
        if right_limit == 0 {
            return;
        }
        self.pair_queue.push_back(ComposeCursor::Left {
            left_idx,
            next_right_idx: 0,
            right_limit,
        });
    }

    /// Enqueue compose pairs for a new right NF.
    /// The match tag must already have been pushed to `right_match_tags`.
    fn enqueue_pairs_right_with_tag<C: ConstraintOps>(
        &mut self,
        join: &DiagonalJoin<C, Self>,
        right_idx: usize,
        _match_tag: RootTag,
    ) {
        let left_limit = join.seen_l_len();
        if left_limit == 0 {
            return;
        }
        self.pair_queue.push_back(ComposeCursor::Right {
            right_idx,
            next_left_idx: 0,
            left_limit,
        });
    }

    fn process_pair_queue<C: ConstraintOps>(
        &mut self,
        join: &mut DiagonalJoin<C, Self>,
        terms: &mut TermStore,
    ) -> Option<crate::nf::NF<C>> {
        let cursor = self.pair_queue.pop_front()?;
        match cursor {
            ComposeCursor::Left {
                left_idx,
                mut next_right_idx,
                right_limit,
            } => {
                let left_nf = join.seen_l_at(left_idx);
                let mut checks = 0usize;
                while next_right_idx < right_limit {
                    let right_idx = next_right_idx;
                    next_right_idx += 1;
                    checks += 1;
                    if !self.pair_tags_compatible(left_idx, right_idx) {
                        if checks >= Self::MAX_PAIR_CHECKS_PER_STEP && next_right_idx < right_limit
                        {
                            self.pair_queue.push_back(ComposeCursor::Left {
                                left_idx,
                                next_right_idx,
                                right_limit,
                            });
                            return join.pop_pending();
                        }
                        continue;
                    }
                    let right_nf = join.seen_r_at(right_idx);
                    if let Some(nf) = Self::compose_pair(left_nf, right_nf, terms) {
                        join.push_pending(nf);
                        // Emit eagerly on first success to improve time-to-first-answer.
                        // Resume this cursor later from where we left off.
                        if next_right_idx < right_limit {
                            self.pair_queue.push_front(ComposeCursor::Left {
                                left_idx,
                                next_right_idx,
                                right_limit,
                            });
                        }
                        return join.pop_pending();
                    }
                    if checks >= Self::MAX_PAIR_CHECKS_PER_STEP && next_right_idx < right_limit {
                        self.pair_queue.push_back(ComposeCursor::Left {
                            left_idx,
                            next_right_idx,
                            right_limit,
                        });
                        return join.pop_pending();
                    }
                }
            }
            ComposeCursor::Right {
                right_idx,
                mut next_left_idx,
                left_limit,
            } => {
                let right_nf = join.seen_r_at(right_idx);
                let mut checks = 0usize;
                while next_left_idx < left_limit {
                    let left_idx = next_left_idx;
                    next_left_idx += 1;
                    checks += 1;
                    if !self.pair_tags_compatible(left_idx, right_idx) {
                        if checks >= Self::MAX_PAIR_CHECKS_PER_STEP && next_left_idx < left_limit {
                            self.pair_queue.push_back(ComposeCursor::Right {
                                right_idx,
                                next_left_idx,
                                left_limit,
                            });
                            return join.pop_pending();
                        }
                        continue;
                    }
                    let left_nf = join.seen_l_at(left_idx);
                    if let Some(nf) = Self::compose_pair(left_nf, right_nf, terms) {
                        join.push_pending(nf);
                        // Emit eagerly on first success to improve time-to-first-answer.
                        // Resume this cursor later from where we left off.
                        if next_left_idx < left_limit {
                            self.pair_queue.push_front(ComposeCursor::Right {
                                right_idx,
                                next_left_idx,
                                left_limit,
                            });
                        }
                        return join.pop_pending();
                    }
                    if checks >= Self::MAX_PAIR_CHECKS_PER_STEP && next_left_idx < left_limit {
                        self.pair_queue.push_back(ComposeCursor::Right {
                            right_idx,
                            next_left_idx,
                            left_limit,
                        });
                        return join.pop_pending();
                    }
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
        if C::ALWAYS_EMPTY {
            // Eager path: all pairs were composed directly in on_new_left/on_new_right,
            // so there are no cursors to process. Results are already in pending.
            join.pop_pending()
        } else {
            self.process_pair_queue(join, terms)
        }
    }

    fn on_new_left(
        &mut self,
        join: &mut DiagonalJoin<C, Self>,
        left_idx: usize,
        terms: &mut TermStore,
    ) {
        let build_tag = build_root_tag(join.seen_l_at(left_idx), terms);
        self.left_build_tags.push(build_tag);
        if C::ALWAYS_EMPTY {
            // Eager: compose only functor-compatible pairs immediately
            let right_limit = join.seen_r_len();
            for right_idx in 0..right_limit {
                if !self.pair_tags_compatible(left_idx, right_idx) {
                    continue;
                }
                let left_nf = join.seen_l_at(left_idx);
                let right_nf = join.seen_r_at(right_idx);
                if let Some(nf) = Self::compose_pair(left_nf, right_nf, terms) {
                    join.push_pending(nf);
                }
            }
        } else {
            self.enqueue_pairs_left_with_tag(join, left_idx, build_tag);
        }
    }

    fn on_new_right(
        &mut self,
        join: &mut DiagonalJoin<C, Self>,
        right_idx: usize,
        terms: &mut TermStore,
    ) {
        let match_tag = match_root_tag(join.seen_r_at(right_idx), terms);
        self.right_match_tags.push(match_tag);
        if C::ALWAYS_EMPTY {
            // Eager: compose only functor-compatible pairs immediately
            let left_limit = join.seen_l_len();
            for left_idx in 0..left_limit {
                if !self.pair_tags_compatible(left_idx, right_idx) {
                    continue;
                }
                let left_nf = join.seen_l_at(left_idx);
                let right_nf = join.seen_r_at(right_idx);
                if let Some(nf) = Self::compose_pair(left_nf, right_nf, terms) {
                    join.push_pending(nf);
                }
            }
        } else {
            self.enqueue_pairs_right_with_tag(join, right_idx, match_tag);
        }
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
    /// Create a new ComposeWork from two work streams.
    pub fn new(left: Work<C>, right: Work<C>) -> Self {
        Self {
            core: DiagonalJoin::new(left, right, ComposeStrategy::new()),
        }
    }

    #[cfg(test)]
    pub(crate) fn new_with_sources(left: WorkSet<C>, right: WorkSet<C>) -> Self {
        Self {
            core: DiagonalJoin::new_with_sources(left, right, ComposeStrategy::new()),
        }
    }

    pub(crate) fn new_with_sources_preseed(
        mut left: WorkSet<C>,
        mut right: WorkSet<C>,
        terms: &mut TermStore,
    ) -> Self {
        let mut strategy = ComposeStrategy::new();
        let seen_l = left.drain_leading_atoms();
        let seen_r = right.drain_leading_atoms();

        for nf in &seen_l {
            strategy.left_build_tags.push(build_root_tag(nf, terms));
        }
        for nf in &seen_r {
            strategy.right_match_tags.push(match_root_tag(nf, terms));
        }

        let left_exhausted = left.is_exhausted();
        let right_exhausted = right.is_exhausted();
        if (left_exhausted && seen_l.is_empty()) || (right_exhausted && seen_r.is_empty()) {
            return Self {
                core: DiagonalJoin::new_with_sources(
                    WorkSet::new(),
                    WorkSet::new(),
                    ComposeStrategy::new(),
                ),
            };
        }

        let mut pending: VecDeque<crate::nf::NF<C>> = VecDeque::new();
        if !seen_l.is_empty() && !seen_r.is_empty() {
            for (ri, right_nf) in seen_r.iter().enumerate() {
                for (li, left_nf) in seen_l.iter().enumerate() {
                    if !strategy.pair_tags_compatible(li, ri) {
                        continue;
                    }
                    if let Some(nf) = ComposeStrategy::compose_pair(left_nf, right_nf, terms) {
                        pending.push_back(nf);
                    }
                }
            }
        }

        let flip = !seen_l.is_empty();
        let mut core = DiagonalJoin::new_with_seen_sources(left, right, seen_l, seen_r, strategy);
        core.flip = flip;
        for nf in pending {
            core.push_pending(nf);
        }
        Self { core }
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
    pub(crate) fn left(&self) -> &WorkSet<C> {
        &self.core.left
    }

    #[cfg(test)]
    pub(crate) fn right(&self) -> &WorkSet<C> {
        &self.core.right
    }
}
