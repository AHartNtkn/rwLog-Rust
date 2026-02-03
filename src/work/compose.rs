use crate::constraint::ConstraintOps;
use crate::kernel::compose_nf;
use crate::nf::NF;
use crate::node::{step_node, Node, NodeStep};
use crate::term::TermStore;
use std::collections::{HashSet, VecDeque};

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
pub struct ComposeWork<C: ConstraintOps> {
    /// Left search tree.
    pub left: Box<Node<C>>,
    /// Right search tree.
    pub right: Box<Node<C>>,
    /// Answers seen from left.
    pub seen_l: Vec<NF<C>>,
    /// Answers seen from right.
    pub seen_r: Vec<NF<C>>,
    /// Dedup set for left answers.
    seen_l_set: HashSet<NF<C>>,
    /// Dedup set for right answers.
    seen_r_set: HashSet<NF<C>>,
    /// Successful compositions waiting to be emitted.
    pub pending: VecDeque<NF<C>>,
    /// Dedup set for pending compositions.
    pending_set: HashSet<NF<C>>,
    /// Pending composition cursors.
    pair_queue: VecDeque<ComposeCursor>,
    /// If false, pull from left next; if true, pull from right.
    pub flip: bool,
}

impl<C: ConstraintOps> ComposeWork<C> {
    /// Create a new ComposeWork from two nodes.
    pub fn new(left: Node<C>, right: Node<C>) -> Self {
        Self {
            left: Box::new(left),
            right: Box::new(right),
            seen_l: Vec::new(),
            seen_r: Vec::new(),
            seen_l_set: HashSet::new(),
            seen_r_set: HashSet::new(),
            pending: VecDeque::new(),
            pending_set: HashSet::new(),
            pair_queue: VecDeque::new(),
            flip: false,
        }
    }

    fn take_self(&mut self) -> Self {
        std::mem::replace(self, ComposeWork::new(Node::Fail, Node::Fail))
    }

    fn push_pending(&mut self, nf: NF<C>) {
        if self.pending_set.insert(nf.clone()) {
            self.pending.push_back(nf);
        }
    }

    fn is_empty_identity(nf: &NF<C>) -> bool {
        nf.match_pats.is_empty()
            && nf.build_pats.is_empty()
            && nf.drop_fresh.in_arity == 0
            && nf.drop_fresh.out_arity == 0
    }

    fn compose_pair(
        left_nf: &NF<C>,
        right_nf: &NF<C>,
        terms: &mut TermStore,
    ) -> Option<NF<C>> {
        if Self::is_empty_identity(right_nf) {
            return Some(left_nf.clone());
        }
        if Self::is_empty_identity(left_nf) {
            return Some(right_nf.clone());
        }
        compose_nf(left_nf, right_nf, terms)
    }

    fn enqueue_pairs_left(&mut self, left_idx: usize) {
        let right_limit = self.seen_r.len();
        if right_limit == 0 {
            return;
        }
        self.pair_queue.push_back(ComposeCursor::Left {
            left_idx,
            right_idx: 0,
            right_limit,
        });
    }

    fn enqueue_pairs_right(&mut self, right_idx: usize) {
        let left_limit = self.seen_l.len();
        if left_limit == 0 {
            return;
        }
        self.pair_queue.push_back(ComposeCursor::Right {
            right_idx,
            left_idx: 0,
            left_limit,
        });
    }

    fn process_pair_queue(&mut self, terms: &mut TermStore) -> Option<NF<C>> {
        let Some(mut cursor) = self.pair_queue.pop_front() else {
            return None;
        };

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
                    let left_nf = &self.seen_l[*left_idx];
                    let right_nf = &self.seen_r[*right_idx];
                    if let Some(nf) = Self::compose_pair(left_nf, right_nf, terms) {
                        self.push_pending(nf);
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
                    let left_nf = &self.seen_l[*left_idx];
                    let right_nf = &self.seen_r[*right_idx];
                    if let Some(nf) = Self::compose_pair(left_nf, right_nf, terms) {
                        self.push_pending(nf);
                    }
                    *left_idx += 1;
                }
            }
        }

        if let Some(nf) = self.pending.pop_front() {
            self.pending_set.remove(&nf);
            return Some(nf);
        }

        None
    }

    /// Step this compose work, returning the next state.
    ///
    /// Step policy:
    /// 1. If pending non-empty: emit front
    /// 2. Alternate processing pair cursors and pulling new answers
    /// 3. Alternate pulling from left/right (flip)
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        if let Some(nf) = self.pending.pop_front() {
            self.pending_set.remove(&nf);
            return WorkStep::Emit(nf, Box::new(Work::Compose(self.take_self())));
        }

        let left_exhausted = matches!(*self.left, Node::Fail);
        let right_exhausted = matches!(*self.right, Node::Fail);

        if let Some(nf) = self.process_pair_queue(terms) {
            return WorkStep::Emit(nf, Box::new(Work::Compose(self.take_self())));
        }

        if left_exhausted && self.seen_l.is_empty() && self.pair_queue.is_empty() {
            return WorkStep::Done;
        }

        if right_exhausted && self.seen_r.is_empty() && self.pair_queue.is_empty() {
            return WorkStep::Done;
        }

        if left_exhausted && right_exhausted {
            if self.pair_queue.is_empty() {
                return WorkStep::Done;
            }
            return WorkStep::More(Box::new(Work::Compose(self.take_self())));
        }

        let pull_from_right = if left_exhausted {
            true
        } else if right_exhausted {
            false
        } else {
            self.flip
        };

        if pull_from_right {
            self.pull_right(terms)
        } else {
            self.pull_left(terms)
        }
    }

    fn pull_left(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let current = std::mem::replace(&mut *self.left, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                *self.left = rest;
                if self.seen_l_set.insert(nf.clone()) {
                    let idx = self.seen_l.len();
                    self.seen_l.push(nf.clone());
                    self.enqueue_pairs_left(idx);
                }
                self.flip = true;
                if let Some(result) = self.pending.pop_front() {
                    self.pending_set.remove(&result);
                    WorkStep::Emit(result, Box::new(Work::Compose(self.take_self())))
                } else {
                    WorkStep::More(Box::new(Work::Compose(self.take_self())))
                }
            }
            NodeStep::Continue(rest) => {
                *self.left = rest;
                self.flip = true;
                WorkStep::More(Box::new(Work::Compose(self.take_self())))
            }
            NodeStep::Exhausted => {
                *self.left = Node::Fail;
                self.flip = true;
                WorkStep::More(Box::new(Work::Compose(self.take_self())))
            }
        }
    }

    fn pull_right(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let current = std::mem::replace(&mut *self.right, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                *self.right = rest;
                if self.seen_r_set.insert(nf.clone()) {
                    let idx = self.seen_r.len();
                    self.seen_r.push(nf.clone());
                    self.enqueue_pairs_right(idx);
                }
                self.flip = false;
                if let Some(result) = self.pending.pop_front() {
                    self.pending_set.remove(&result);
                    WorkStep::Emit(result, Box::new(Work::Compose(self.take_self())))
                } else {
                    WorkStep::More(Box::new(Work::Compose(self.take_self())))
                }
            }
            NodeStep::Continue(rest) => {
                *self.right = rest;
                self.flip = false;
                WorkStep::More(Box::new(Work::Compose(self.take_self())))
            }
            NodeStep::Exhausted => {
                *self.right = Node::Fail;
                self.flip = false;
                WorkStep::More(Box::new(Work::Compose(self.take_self())))
            }
        }
    }
}
