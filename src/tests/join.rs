use super::*;
use crate::kernel::dual_nf;
use crate::queue::{AnswerQueue, AnswerSink, RecvResult, SinkResult, WakeHub};
use crate::test_utils::{make_rule_nf, setup};
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

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

    assert!(matches!(joiner.step(&mut terms, &mut sink), JoinStep::Progress));
    assert_eq!(joiner.seen[0].len(), 1);
    assert_eq!(joiner.seen[1].len(), 0);
    assert_eq!(joiner.turn, 1);

    assert!(matches!(joiner.step(&mut terms, &mut sink), JoinStep::Progress));
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
        out.lock().unwrap().is_empty(),
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
    let out = out.lock().unwrap();
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

    let mut joiner = AndJoiner::from_state(
        vec![rx0, rx1],
        vec![false, false],
        vec![Vec::new(), Vec::new()],
        VecDeque::new(),
        0,
        joiner_waker,
    );
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
