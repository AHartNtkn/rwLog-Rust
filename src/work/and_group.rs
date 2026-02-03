use crate::constraint::ConstraintOps;
use crate::join::{AndJoiner, JoinStep};
use crate::nf::NF;
use crate::node::{step_node, Node, NodeStep};
use crate::queue::{
    AnswerQueue, AnswerReceiver, AnswerSender, BlockedOn, RecvResult, SinkResult, WakeHub,
};
use crate::term::TermStore;
use parking_lot::Mutex;
use std::collections::VecDeque;
use std::sync::Arc;

use super::{Work, WorkStep};

/// AndGroup work: queue-backed join for n-ary conjunction/intersection.
///
/// Represents: And(r0, r1, ..., rn-1)
///
/// Each part runs as a producer that pushes answers into a bounded queue.
/// The joiner consumes those queues round-robin and emits meets into an output queue.
#[derive(Clone, Copy, Debug)]
pub struct AndGroupConfig {
    part_queue_capacity: usize,
    output_queue_capacity: usize,
}

impl Default for AndGroupConfig {
    fn default() -> Self {
        Self {
            part_queue_capacity: 1,
            output_queue_capacity: 1,
        }
    }
}

#[derive(Clone, Debug)]
struct AndProducer<C: ConstraintOps> {
    node: Node<C>,
    sender: Option<AnswerSender<C>>,
    pending: Option<NF<C>>,
    blocked: Option<BlockedOn>,
    done: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AndProducerStep {
    Progress,
    Blocked,
    Done,
}

impl<C: ConstraintOps> AndProducer<C> {
    fn new(node: Node<C>, sender: AnswerSender<C>) -> Self {
        Self {
            node,
            sender: Some(sender),
            pending: None,
            blocked: None,
            done: false,
        }
    }

    fn runnable(&self) -> bool {
        if self.done {
            return false;
        }
        self.blocked.as_ref().map_or(true, |b| b.is_stale())
    }

    fn close_sender(&mut self) {
        self.sender = None;
    }

    fn step(&mut self, terms: &mut TermStore) -> AndProducerStep {
        if self.done {
            return AndProducerStep::Done;
        }

        if let Some(blocked) = &self.blocked {
            if !blocked.is_stale() {
                return AndProducerStep::Blocked;
            }
        }

        if let Some(nf) = self.pending.take() {
            let Some(sender) = self.sender.as_ref() else {
                self.done = true;
                return AndProducerStep::Done;
            };
            match sender.try_send(nf.clone()) {
                SinkResult::Accepted => {
                    self.blocked = None;
                    return AndProducerStep::Progress;
                }
                SinkResult::Full => {
                    self.pending = Some(nf);
                    self.blocked = Some(sender.blocked_on());
                    return AndProducerStep::Blocked;
                }
                SinkResult::Closed => {
                    self.done = true;
                    self.close_sender();
                    return AndProducerStep::Done;
                }
            }
        }

        let current = std::mem::replace(&mut self.node, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                self.node = rest;
                let Some(sender) = self.sender.as_ref() else {
                    self.done = true;
                    return AndProducerStep::Done;
                };
                match sender.try_send(nf.clone()) {
                    SinkResult::Accepted => {
                        self.blocked = None;
                        AndProducerStep::Progress
                    }
                    SinkResult::Full => {
                        self.pending = Some(nf);
                        self.blocked = Some(sender.blocked_on());
                        AndProducerStep::Blocked
                    }
                    SinkResult::Closed => {
                        self.done = true;
                        self.close_sender();
                        AndProducerStep::Done
                    }
                }
            }
            NodeStep::Continue(rest) => {
                self.node = rest;
                if matches!(self.node, Node::Fail) {
                    self.done = true;
                    self.close_sender();
                    return AndProducerStep::Done;
                }
                self.blocked = None;
                AndProducerStep::Progress
            }
            NodeStep::Exhausted => {
                self.node = Node::Fail;
                self.done = true;
                self.close_sender();
                AndProducerStep::Done
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct AndGroup<C: ConstraintOps> {
    producers: Vec<AndProducer<C>>,
    joiner: Arc<Mutex<AndJoiner<C>>>,
    joiner_sink: AnswerSender<C>,
    joiner_blocked: Option<BlockedOn>,
    joiner_done: bool,
    output_receiver: Arc<Mutex<AnswerReceiver<C>>>,
    /// Round-robin turn index across producers + joiner.
    pub turn: usize,
}

impl<C: ConstraintOps> AndGroup<C> {
    /// Create a new AndGroup from part nodes.
    pub fn new(parts: Vec<Node<C>>) -> Self {
        Self::with_config(parts, AndGroupConfig::default())
    }

    #[cfg(test)]
    pub(crate) fn producer_nodes(&self) -> impl Iterator<Item = &Node<C>> {
        self.producers.iter().map(|producer| &producer.node)
    }

    pub fn with_config(parts: Vec<Node<C>>, config: AndGroupConfig) -> Self {
        let (hub, _rx) = WakeHub::new();
        let joiner_waker = hub.waker();
        let output_waker = hub.waker();

        let mut receivers = Vec::new();
        let mut producers = Vec::new();

        for part in parts {
            let (tx, rx) =
                AnswerQueue::bounded_with_waker(config.part_queue_capacity, joiner_waker.clone());
            receivers.push(rx);
            producers.push(AndProducer::new(part, tx));
        }

        let (out_tx, out_rx) =
            AnswerQueue::bounded_with_waker(config.output_queue_capacity, output_waker);

        let joiner = AndJoiner::from_state(
            receivers,
            vec![false; producers.len()],
            vec![Vec::new(); producers.len()],
            VecDeque::new(),
            0,
            joiner_waker,
        );

        Self {
            producers,
            joiner: Arc::new(Mutex::new(joiner)),
            joiner_sink: out_tx,
            joiner_blocked: None,
            joiner_done: false,
            output_receiver: Arc::new(Mutex::new(out_rx)),
            turn: 0,
        }
    }

    fn take_self(&mut self) -> Self {
        std::mem::replace(self, AndGroup::new(Vec::new()))
    }

    fn joiner_runnable(&self) -> bool {
        if self.joiner_done {
            return false;
        }
        self.joiner_blocked.as_ref().map_or(true, |b| b.is_stale())
    }

    fn poll_output(&mut self) -> Option<NF<C>> {
        let receiver = self.output_receiver.lock();
        match receiver.try_recv() {
            RecvResult::Item(nf) => Some(nf),
            RecvResult::Empty => None,
            RecvResult::Closed => {
                self.joiner_done = true;
                None
            }
        }
    }

    fn step_joiner(&mut self, terms: &mut TermStore) -> JoinStep {
        let mut joiner = self.joiner.lock();
        let mut sink = crate::queue::AnswerSink::Queue(self.joiner_sink.clone());
        match joiner.step(terms, &mut sink) {
            JoinStep::Progress => {
                self.joiner_blocked = None;
                JoinStep::Progress
            }
            JoinStep::Blocked(blocked) => {
                self.joiner_blocked = Some(blocked.clone());
                JoinStep::Blocked(blocked)
            }
            JoinStep::Done => {
                self.joiner_done = true;
                self.joiner_blocked = None;
                JoinStep::Done
            }
        }
    }

    /// Step this AndGroup, returning the next state.
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        if let Some(nf) = self.poll_output() {
            return WorkStep::Emit(nf, Box::new(Work::AndGroup(self.take_self())));
        }

        if self.joiner_done {
            return WorkStep::Done;
        }

        let total = self.producers.len() + 1;
        if total == 0 {
            return WorkStep::Done;
        }

        for offset in 0..total {
            let idx = (self.turn + offset) % total;
            if idx == self.producers.len() {
                if !self.joiner_runnable() {
                    continue;
                }
                self.step_joiner(terms);
                self.turn = (idx + 1) % total;
                if let Some(nf) = self.poll_output() {
                    return WorkStep::Emit(nf, Box::new(Work::AndGroup(self.take_self())));
                }
                return WorkStep::More(Box::new(Work::AndGroup(self.take_self())));
            }

            if !self.producers[idx].runnable() {
                continue;
            }
            let _ = self.producers[idx].step(terms);
            self.turn = (idx + 1) % total;
            if let Some(nf) = self.poll_output() {
                return WorkStep::Emit(nf, Box::new(Work::AndGroup(self.take_self())));
            }
            return WorkStep::More(Box::new(Work::AndGroup(self.take_self())));
        }

        if self.joiner_done {
            WorkStep::Done
        } else {
            WorkStep::More(Box::new(Work::AndGroup(self.take_self())))
        }
    }
}
