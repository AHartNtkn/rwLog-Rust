use crate::constraint::ConstraintOps;
use crate::kernel::meet_nf;
use crate::nf::NF;
use crate::term::TermStore;
use crate::work::U64HashSet;
use std::collections::VecDeque;

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
    seen: Vec<Vec<NF<C>>>,
    seen_sets: Vec<U64HashSet>,
    pending: VecDeque<NF<C>>,
    pending_set: U64HashSet,
    turn: usize,
    waker: QueueWaker,
    last_empty_epoch: Option<u64>,
}

impl<C: ConstraintOps> AndJoiner<C> {
    pub fn with_waker(receivers: Vec<AnswerReceiver<C>>, waker: QueueWaker) -> Self {
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
            seen_sets: vec![U64HashSet::default(); count],
            pending: VecDeque::new(),
            pending_set: U64HashSet::default(),
            turn: 0,
            waker,
            last_empty_epoch: None,
        }
    }

    #[cfg(test)]
    pub fn new(receivers: Vec<AnswerReceiver<C>>) -> Self {
        Self::with_waker(receivers, QueueWaker::noop())
    }

    fn push_pending(&mut self, nf: NF<C>) {
        if self.pending_set.insert(nf.hash_value()) {
            self.pending.push_back(nf);
        }
    }

    fn enqueue_meets(&mut self, idx: usize, nf: NF<C>, terms: &mut TermStore) {
        if self.parts.len() == 1 {
            self.push_pending(nf);
            return;
        }

        let mut acc = vec![nf];
        let mut next = Vec::new();
        for (j, seen_j) in self.seen.iter().enumerate() {
            if j == idx {
                continue;
            }
            if seen_j.is_empty() {
                return;
            }

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
            std::mem::swap(&mut acc, &mut next);
            next.clear();
        }

        for result in acc {
            self.push_pending(result);
        }
    }

    fn try_drain_pending(&mut self, sink: &mut AnswerSink<C>) -> Option<JoinStep> {
        let nf = self.pending.front()?;
        match sink.push(nf.clone()) {
            SinkResult::Accepted => {
                let nf = self.pending.pop_front().unwrap();
                self.pending_set.remove(&nf.hash_value());
                Some(JoinStep::Progress)
            }
            SinkResult::Full => Some(JoinStep::Blocked(
                sink.blocked_on()
                    .expect("queue sink should provide a waker"),
            )),
            SinkResult::Closed => Some(JoinStep::Done),
        }
    }

    pub fn step(&mut self, terms: &mut TermStore, sink: &mut AnswerSink<C>) -> JoinStep {
        if let Some(step) = self.try_drain_pending(sink) {
            return step;
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
                    if self.seen_sets[idx].insert(nf.hash_value()) {
                        self.seen[idx].push(nf.clone());
                        self.enqueue_meets(idx, nf, terms);
                    }
                    if let Some(step) = self.try_drain_pending(sink) {
                        return step;
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
mod tests {
    use super::*;
    use crate::kernel::dual_nf;
    use crate::queue::{AnswerQueue, AnswerSink, RecvResult, SinkResult, WakeHub};
    use crate::test_utils::{make_rule_nf, setup};
    use parking_lot::Mutex;
    use std::sync::Arc;

    type CollectedAnswers = (AnswerSink<()>, Arc<Mutex<Vec<NF<()>>>>);

    fn collect_sink() -> CollectedAnswers {
        let out = Arc::new(Mutex::new(Vec::new()));
        (AnswerSink::Collector(out.clone()), out)
    }

    fn run_until_done(
        joiner: &mut AndJoiner<()>,
        terms: &mut TermStore,
        sink: &mut AnswerSink<()>,
    ) {
        let mut steps = 0usize;
        loop {
            match joiner.step(terms, sink) {
                JoinStep::Done => break,
                JoinStep::Progress | JoinStep::Blocked(_) => {
                    steps += 1;
                    if steps > 32 {
                        panic!("joiner did not terminate within {}", steps);
                    }
                }
            }
        }
    }

    fn run_round_robin(use_dual: bool) {
        let (symbols, mut terms) = setup();
        let mut nf = make_rule_nf("A", "B", &symbols, &terms);
        if use_dual {
            nf = dual_nf(&nf, &mut terms);
        }

        let (tx0, rx0) = AnswerQueue::bounded::<()>(2);
        let (tx1, rx1) = AnswerQueue::bounded::<()>(2);

        assert_eq!(tx0.try_send(nf.clone()), SinkResult::Accepted);
        assert_eq!(tx1.try_send(nf.clone()), SinkResult::Accepted);

        let mut joiner = AndJoiner::new(vec![rx0, rx1]);
        let (mut sink, _out) = collect_sink();

        assert_eq!(joiner.turn, 0);
        assert_eq!(joiner.seen[0].len(), 0);
        assert_eq!(joiner.seen[1].len(), 0);

        assert!(matches!(
            joiner.step(&mut terms, &mut sink),
            JoinStep::Progress
        ));
        assert_eq!(joiner.seen[0].len(), 1);
        assert_eq!(joiner.seen[1].len(), 0);
        assert_eq!(joiner.turn, 1);

        assert!(matches!(
            joiner.step(&mut terms, &mut sink),
            JoinStep::Progress
        ));
        assert_eq!(joiner.seen[0].len(), 1);
        assert_eq!(joiner.seen[1].len(), 1);
        assert_eq!(joiner.turn, 0);
    }

    #[test]
    fn and_joiner_round_robin_turns() {
        run_round_robin(false);
    }

    #[test]
    fn and_joiner_round_robin_turns_dual() {
        run_round_robin(true);
    }

    fn run_backpressure(use_dual: bool) {
        let (symbols, mut terms) = setup();
        let mut nf = make_rule_nf("A", "B", &symbols, &terms);
        if use_dual {
            nf = dual_nf(&nf, &mut terms);
        }

        let (tx0, rx0) = AnswerQueue::bounded::<()>(1);
        let (tx1, rx1) = AnswerQueue::bounded::<()>(1);

        assert_eq!(tx0.try_send(nf.clone()), SinkResult::Accepted);
        assert_eq!(tx1.try_send(nf.clone()), SinkResult::Accepted);

        let (out_tx, out_rx) = AnswerQueue::bounded::<()>(1);
        assert_eq!(out_tx.try_send(nf.clone()), SinkResult::Accepted);
        let mut sink = AnswerSink::Queue(out_tx);

        let mut joiner = AndJoiner::new(vec![rx0, rx1]);

        let _ = joiner.step(&mut terms, &mut sink);
        let step = joiner.step(&mut terms, &mut sink);
        assert!(matches!(step, JoinStep::Blocked(_)));
        assert!(
            !joiner.pending.is_empty(),
            "pending should retain blocked output"
        );

        match out_rx.try_recv() {
            RecvResult::Item(_) => {}
            other => panic!("expected drained item, got {:?}", other),
        }

        let step = joiner.step(&mut terms, &mut sink);
        assert!(matches!(step, JoinStep::Progress));
        match out_rx.try_recv() {
            RecvResult::Item(_) => {}
            other => panic!("expected joiner output, got {:?}", other),
        }
    }

    #[test]
    fn and_joiner_backpressure_keeps_pending() {
        run_backpressure(false);
    }

    #[test]
    fn and_joiner_backpressure_keeps_pending_dual() {
        run_backpressure(true);
    }

    fn run_closure_empty_part(use_dual: bool) {
        let (symbols, mut terms) = setup();
        let mut nf = make_rule_nf("A", "B", &symbols, &terms);
        if use_dual {
            nf = dual_nf(&nf, &mut terms);
        }

        let (tx0, rx0) = AnswerQueue::bounded::<()>(1);
        let (tx1, rx1) = AnswerQueue::bounded::<()>(1);

        drop(tx0);
        assert_eq!(tx1.try_send(nf.clone()), SinkResult::Accepted);
        drop(tx1);

        let mut joiner = AndJoiner::new(vec![rx0, rx1]);
        let (mut sink, out) = collect_sink();

        run_until_done(&mut joiner, &mut terms, &mut sink);
        assert!(
            out.lock().is_empty(),
            "empty part should force empty result set"
        );
    }

    #[test]
    fn and_joiner_closure_empty_part_terminates() {
        run_closure_empty_part(false);
    }

    #[test]
    fn and_joiner_closure_empty_part_terminates_dual() {
        run_closure_empty_part(true);
    }

    fn run_closure_after_answers(use_dual: bool) {
        let (symbols, mut terms) = setup();
        let mut nf = make_rule_nf("A", "B", &symbols, &terms);
        if use_dual {
            nf = dual_nf(&nf, &mut terms);
        }

        let (tx0, rx0) = AnswerQueue::bounded::<()>(1);
        let (tx1, rx1) = AnswerQueue::bounded::<()>(1);

        assert_eq!(tx0.try_send(nf.clone()), SinkResult::Accepted);
        assert_eq!(tx1.try_send(nf.clone()), SinkResult::Accepted);
        drop(tx0);
        drop(tx1);

        let mut joiner = AndJoiner::new(vec![rx0, rx1]);
        let (mut sink, out) = collect_sink();

        run_until_done(&mut joiner, &mut terms, &mut sink);
        let out = out.lock();
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], nf);
    }

    #[test]
    fn and_joiner_closure_after_answers_emits() {
        run_closure_after_answers(false);
    }

    #[test]
    fn and_joiner_closure_after_answers_emits_dual() {
        run_closure_after_answers(true);
    }

    fn run_joiner_waker_gates_polling(use_dual: bool) {
        let (symbols, mut terms) = setup();
        let mut nf = make_rule_nf("A", "B", &symbols, &terms);
        if use_dual {
            nf = dual_nf(&nf, &mut terms);
        }

        let (wake_hub, _wake_rx) = WakeHub::new();
        let joiner_waker = wake_hub.waker();
        let other_waker = wake_hub.waker();

        let (tx0, rx0) = AnswerQueue::bounded_with_waker::<()>(1, other_waker.clone());
        let (_tx1, rx1) = AnswerQueue::bounded_with_waker::<()>(1, other_waker);

        let mut joiner = AndJoiner::with_waker(vec![rx0, rx1], joiner_waker);
        let (mut sink, _out) = collect_sink();

        let step = joiner.step(&mut terms, &mut sink);
        assert!(matches!(step, JoinStep::Blocked(_)));

        assert_eq!(tx0.try_send(nf), SinkResult::Accepted);

        let step = joiner.step(&mut terms, &mut sink);
        assert!(matches!(step, JoinStep::Blocked(_)));
        assert_eq!(
            joiner.seen[0].len(),
            0,
            "joiner should not poll receivers without wake readiness"
        );
    }

    #[test]
    fn and_joiner_waker_gates_polling() {
        run_joiner_waker_gates_polling(false);
    }

    #[test]
    fn and_joiner_waker_gates_polling_dual() {
        run_joiner_waker_gates_polling(true);
    }
}
