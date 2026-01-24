use super::*;
use std::time::Duration;

#[test]
fn sender_drop_wakes_blocked() {
    let (hub, rx) = WakeHub::new();
    let waker = hub.waker();
    let (tx, _rx) = AnswerQueue::bounded_with_waker::<()>(1, waker.clone());
    let blocked = waker.blocked_on();

    drop(tx);

    assert!(
        blocked.is_stale(),
        "dropping the sender should wake blocked tasks"
    );
    let id = rx
        .recv_timeout(Duration::from_millis(50))
        .expect("expected wake id after sender drop");
    assert_eq!(id, waker.id(), "unexpected wake id after sender drop");
}

#[test]
fn receiver_drop_wakes_blocked() {
    let (hub, rx) = WakeHub::new();
    let waker = hub.waker();
    let (_tx, rx_queue) = AnswerQueue::bounded_with_waker::<()>(1, waker.clone());
    let blocked = waker.blocked_on();

    drop(rx_queue);

    assert!(
        blocked.is_stale(),
        "dropping the receiver should wake blocked tasks"
    );
    let id = rx
        .recv_timeout(Duration::from_millis(50))
        .expect("expected wake id after receiver drop");
    assert_eq!(id, waker.id(), "unexpected wake id after receiver drop");
}

fn assert_send_sync<T: Send + Sync>() {}

#[test]
fn answer_sender_is_send_sync() {
    assert_send_sync::<AnswerSender<()>>();
}

#[test]
fn answer_receiver_is_send_sync() {
    assert_send_sync::<AnswerReceiver<()>>();
}
