use crate::constraint::ConstraintOps;
use crate::kernel::meet_nf;
use crate::nf::NF;
use crate::term::TermStore;
use std::collections::{HashSet, VecDeque};

use crate::queue::{AnswerReceiver, AnswerSink, BlockedOn, QueueWaker, RecvResult, SinkResult};

#[derive(Debug, Clone)]
pub enum JoinStep {
    Progress,
    Blocked(BlockedOn),
    Done,
}

#[derive(Debug)]
struct JoinPart<C> {
    receiver: AnswerReceiver<C>,
    done: bool,
}

#[derive(Debug)]
pub struct AndJoiner<C: ConstraintOps> {
    parts: Vec<JoinPart<C>>,
    pub(crate) seen: Vec<Vec<NF<C>>>,
    seen_sets: Vec<HashSet<NF<C>>>,
    pub(crate) pending: VecDeque<NF<C>>,
    pending_set: HashSet<NF<C>>,
    pub(crate) turn: usize,
    waker: QueueWaker,
    last_empty_epoch: Option<u64>,
}

impl<C: ConstraintOps> AndJoiner<C> {
    #[cfg(test)]
    pub fn new(receivers: Vec<AnswerReceiver<C>>) -> Self {
        let count = receivers.len();
        let parts = receivers
            .into_iter()
            .map(|receiver| JoinPart {
                receiver,
                done: false,
            })
            .collect();
        Self {
            parts,
            seen: vec![Vec::new(); count],
            seen_sets: vec![HashSet::new(); count],
            pending: VecDeque::new(),
            pending_set: HashSet::new(),
            turn: 0,
            waker: QueueWaker::noop(),
            last_empty_epoch: None,
        }
    }

    pub fn from_state(
        receivers: Vec<AnswerReceiver<C>>,
        done: Vec<bool>,
        seen: Vec<Vec<NF<C>>>,
        pending: VecDeque<NF<C>>,
        turn: usize,
        waker: QueueWaker,
    ) -> Self {
        let seen_sets = seen
            .iter()
            .map(|items| items.iter().cloned().collect())
            .collect();
        let pending_set = pending.iter().cloned().collect();
        let parts = receivers
            .into_iter()
            .zip(done)
            .map(|(receiver, done)| JoinPart { receiver, done })
            .collect();
        Self {
            parts,
            seen,
            seen_sets,
            pending,
            pending_set,
            turn,
            waker,
            last_empty_epoch: None,
        }
    }

    fn push_pending(&mut self, nf: NF<C>) {
        if self.pending_set.insert(nf.clone()) {
            self.pending.push_back(nf);
        }
    }

    fn enqueue_meets(&mut self, idx: usize, nf: NF<C>, terms: &mut TermStore) {
        if self.parts.len() == 1 {
            self.push_pending(nf);
            return;
        }

        let mut acc = vec![nf];
        for (j, seen_j) in self.seen.iter().enumerate() {
            if j == idx {
                continue;
            }
            if seen_j.is_empty() {
                return;
            }

            let mut next = Vec::new();
            for left in acc.iter() {
                for right in seen_j.iter() {
                    if let Some(met) = meet_nf(left, right, terms) {
                        next.push(met);
                    }
                }
            }
            if next.is_empty() {
                return;
            }
            acc = next;
        }

        for result in acc {
            self.push_pending(result);
        }
    }

    pub fn step(&mut self, terms: &mut TermStore, sink: &mut AnswerSink<C>) -> JoinStep {
        if let Some(nf) = self.pending.front().cloned() {
            match sink.push(nf.clone()) {
                SinkResult::Accepted => {
                    self.pending.pop_front();
                    self.pending_set.remove(&nf);
                    return JoinStep::Progress;
                }
                SinkResult::Full => {
                    return JoinStep::Blocked(
                        sink.blocked_on()
                            .expect("queue sink should provide a waker"),
                    )
                }
                SinkResult::Closed => return JoinStep::Done,
            }
        }

        if self.parts.is_empty() {
            return JoinStep::Done;
        }

        if self
            .parts
            .iter()
            .enumerate()
            .any(|(idx, part)| part.done && self.seen[idx].is_empty())
        {
            return JoinStep::Done;
        }

        if self.parts.iter().all(|part| part.done) {
            return JoinStep::Done;
        }

        let current_epoch = self.waker.epoch();
        if self.last_empty_epoch == Some(current_epoch) {
            return JoinStep::Blocked(self.waker.blocked_on());
        }

        let part_count = self.parts.len();
        for offset in 0..part_count {
            let idx = (self.turn + offset) % part_count;
            if self.parts[idx].done {
                continue;
            }

            match self.parts[idx].receiver.try_recv() {
                RecvResult::Empty => continue,
                RecvResult::Closed => {
                    self.last_empty_epoch = None;
                    self.parts[idx].done = true;
                    self.turn = (idx + 1) % part_count;
                    if self.seen[idx].is_empty() {
                        return JoinStep::Done;
                    }
                    return JoinStep::Progress;
                }
                RecvResult::Item(nf) => {
                    self.last_empty_epoch = None;
                    self.turn = (idx + 1) % part_count;
                    if self.seen_sets[idx].insert(nf.clone()) {
                        self.seen[idx].push(nf.clone());
                        self.enqueue_meets(idx, nf, terms);
                    }
                    if let Some(result) = self.pending.front().cloned() {
                        match sink.push(result.clone()) {
                            SinkResult::Accepted => {
                                self.pending.pop_front();
                                self.pending_set.remove(&result);
                                return JoinStep::Progress;
                            }
                            SinkResult::Full => {
                                return JoinStep::Blocked(
                                    sink.blocked_on()
                                        .expect("queue sink should provide a waker"),
                                )
                            }
                            SinkResult::Closed => return JoinStep::Done,
                        }
                    }
                    return JoinStep::Progress;
                }
            }
        }

        self.last_empty_epoch = Some(current_epoch);
        JoinStep::Blocked(self.waker.blocked_on())
    }
}


#[cfg(test)]
#[path = "tests/join.rs"]
mod tests;
