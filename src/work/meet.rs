use crate::constraint::ConstraintOps;
use crate::kernel::meet_nf;
use crate::nf::NF;
use crate::node::{step_node, Node, NodeStep};
use crate::term::TermStore;
use std::collections::{HashSet, VecDeque};

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
#[derive(Clone, Debug)]
pub struct MeetWork<C: ConstraintOps> {
    /// Left search tree (boxed to break recursive type cycle)
    pub left: Box<Node<C>>,
    /// Right search tree (boxed to break recursive type cycle)
    pub right: Box<Node<C>>,
    /// Answers seen from left (in insertion order)
    pub seen_l: Vec<NF<C>>,
    /// Answers seen from right (in insertion order)
    pub seen_r: Vec<NF<C>>,
    /// Dedup set for left answers
    seen_l_set: HashSet<NF<C>>,
    /// Dedup set for right answers
    seen_r_set: HashSet<NF<C>>,
    /// Successful meets waiting to be emitted
    pub pending: VecDeque<NF<C>>,
    /// Dedup set for pending meets
    pending_set: HashSet<NF<C>>,
    /// If false, pull from left next; if true, pull from right
    pub flip: bool,
}

impl<C: ConstraintOps> MeetWork<C> {
    /// Create a new MeetWork from two nodes.
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
            flip: false,
        }
    }

    fn take_self(&mut self) -> Self {
        std::mem::replace(self, MeetWork::new(Node::Fail, Node::Fail))
    }

    /// Step this meet work, returning the next state.
    ///
    /// Step policy:
    /// 1. If pending non-empty: emit front
    /// 2. Alternate pulling from left/right (flip)
    /// 3. When new answer arrives, meet with all seen from other side
    /// 4. Push successful meets to pending
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        // Step 1: If pending has items, emit front
        if let Some(nf) = self.pending.pop_front() {
            self.pending_set.remove(&nf);
            return WorkStep::Emit(nf, Box::new(Work::Meet(self.take_self())));
        }

        // Step 2: Check if both sides are exhausted
        let left_exhausted = matches!(*self.left, Node::Fail);
        let right_exhausted = matches!(*self.right, Node::Fail);

        if left_exhausted && right_exhausted {
            return WorkStep::Done;
        }

        // Step 3: Alternate pulling from left/right based on flip
        // If one side is exhausted, pull from the other
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

    /// Pull from left node and meet with seen_r
    fn pull_left(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let current = std::mem::replace(&mut *self.left, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                *self.left = rest;
                if self.seen_l_set.insert(nf.clone()) {
                    self.seen_l.push(nf.clone());
                    for r_nf in self.seen_r.iter() {
                        if let Some(met) = meet_nf(&nf, r_nf, terms) {
                            if self.pending_set.insert(met.clone()) {
                                self.pending.push_back(met);
                            }
                        }
                    }
                }
                self.flip = true;
                if let Some(result) = self.pending.pop_front() {
                    self.pending_set.remove(&result);
                    WorkStep::Emit(result, Box::new(Work::Meet(self.take_self())))
                } else {
                    WorkStep::More(Box::new(Work::Meet(self.take_self())))
                }
            }
            NodeStep::Continue(rest) => {
                *self.left = rest;
                self.flip = true;
                WorkStep::More(Box::new(Work::Meet(self.take_self())))
            }
            NodeStep::Exhausted => {
                *self.left = Node::Fail;
                self.flip = true;
                WorkStep::More(Box::new(Work::Meet(self.take_self())))
            }
        }
    }

    /// Pull from right node and meet with seen_l
    fn pull_right(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let current = std::mem::replace(&mut *self.right, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                *self.right = rest;
                if self.seen_r_set.insert(nf.clone()) {
                    self.seen_r.push(nf.clone());
                    for l_nf in self.seen_l.iter() {
                        if let Some(met) = meet_nf(l_nf, &nf, terms) {
                            if self.pending_set.insert(met.clone()) {
                                self.pending.push_back(met);
                            }
                        }
                    }
                }
                self.flip = false;
                if let Some(result) = self.pending.pop_front() {
                    self.pending_set.remove(&result);
                    WorkStep::Emit(result, Box::new(Work::Meet(self.take_self())))
                } else {
                    WorkStep::More(Box::new(Work::Meet(self.take_self())))
                }
            }
            NodeStep::Continue(rest) => {
                *self.right = rest;
                self.flip = false;
                WorkStep::More(Box::new(Work::Meet(self.take_self())))
            }
            NodeStep::Exhausted => {
                *self.right = Node::Fail;
                self.flip = false;
                WorkStep::More(Box::new(Work::Meet(self.take_self())))
            }
        }
    }
}
