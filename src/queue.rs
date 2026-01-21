use crate::nf::NF;
use crossbeam_channel::{Receiver, RecvTimeoutError, Sender, TryRecvError, TrySendError};
use std::collections::HashSet;
use std::hash::Hash;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::sync::Mutex;
use std::time::Duration;

#[derive(Clone, Debug)]
pub struct QueueWaker {
    id: u64,
    epoch: Arc<AtomicU64>,
    tx: Sender<u64>,
}

#[derive(Clone, Debug)]
pub struct BlockedOn {
    waker: QueueWaker,
    epoch: u64,
}

impl QueueWaker {
    pub fn wake(&self) {
        self.epoch.fetch_add(1, Ordering::AcqRel);
        let _ = self.tx.send(self.id);
    }

    pub fn blocked_on(&self) -> BlockedOn {
        BlockedOn {
            waker: self.clone(),
            epoch: self.epoch(),
        }
    }

    pub fn epoch(&self) -> u64 {
        self.epoch.load(Ordering::Acquire)
    }

    pub fn id(&self) -> u64 {
        self.id
    }

    pub(crate) fn noop() -> Self {
        let (tx, _rx) = crossbeam_channel::unbounded();
        QueueWaker {
            id: 0,
            epoch: Arc::new(AtomicU64::new(0)),
            tx,
        }
    }
}

impl BlockedOn {
    pub fn id(&self) -> u64 {
        self.waker.id()
    }

    pub fn is_stale(&self) -> bool {
        self.epoch != self.waker.epoch()
    }

    pub fn waker(&self) -> QueueWaker {
        self.waker.clone()
    }
}

#[derive(Debug)]
pub struct WakeHub {
    next_id: AtomicU64,
    tx: Sender<u64>,
}

impl WakeHub {
    pub fn new() -> (Arc<Self>, crossbeam_channel::Receiver<u64>) {
        let (tx, rx) = crossbeam_channel::unbounded();
        let hub = Arc::new(WakeHub {
            next_id: AtomicU64::new(1),
            tx,
        });
        (hub, rx)
    }

    pub fn waker(&self) -> QueueWaker {
        let id = self.next_id.fetch_add(1, Ordering::AcqRel);
        QueueWaker {
            id,
            epoch: Arc::new(AtomicU64::new(0)),
            tx: self.tx.clone(),
        }
    }
}

#[derive(Clone)]
pub struct AnswerSender<C> {
    inner: Sender<NF<C>>,
    waker: QueueWaker,
}

pub struct AnswerReceiver<C> {
    inner: Receiver<NF<C>>,
    waker: QueueWaker,
}

impl<C> Drop for AnswerSender<C> {
    fn drop(&mut self) {
        self.waker.wake();
    }
}

impl<C> Drop for AnswerReceiver<C> {
    fn drop(&mut self) {
        self.waker.wake();
    }
}

impl<C> std::fmt::Debug for AnswerSender<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AnswerSender").finish()
    }
}

impl<C> std::fmt::Debug for AnswerReceiver<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AnswerReceiver").finish()
    }
}

pub struct AnswerQueue;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SinkResult {
    Accepted,
    Full,
    Closed,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecvResult<C> {
    Item(NF<C>),
    Empty,
    Closed,
}

impl AnswerQueue {
    pub fn bounded_with_waker<C>(
        capacity: usize,
        waker: QueueWaker,
    ) -> (AnswerSender<C>, AnswerReceiver<C>) {
        let (tx, rx) = crossbeam_channel::bounded(capacity);
        let sender = AnswerSender {
            inner: tx,
            waker: waker.clone(),
        };
        let receiver = AnswerReceiver { inner: rx, waker };
        (sender, receiver)
    }

    #[cfg(test)]
    pub fn bounded<C>(capacity: usize) -> (AnswerSender<C>, AnswerReceiver<C>) {
        Self::bounded_with_waker(capacity, QueueWaker::noop())
    }
}

impl<C> AnswerSender<C> {
    pub fn try_send(&self, nf: NF<C>) -> SinkResult {
        match self.inner.try_send(nf) {
            Ok(()) => {
                self.waker.wake();
                SinkResult::Accepted
            }
            Err(TrySendError::Full(_)) => SinkResult::Full,
            Err(TrySendError::Disconnected(_)) => SinkResult::Closed,
        }
    }

    pub fn blocked_on(&self) -> BlockedOn {
        self.waker.blocked_on()
    }
}

impl<C> AnswerReceiver<C> {
    pub fn recv_timeout(&self, timeout: Duration) -> RecvResult<C> {
        match self.inner.recv_timeout(timeout) {
            Ok(nf) => {
                self.waker.wake();
                RecvResult::Item(nf)
            }
            Err(RecvTimeoutError::Timeout) => RecvResult::Empty,
            Err(RecvTimeoutError::Disconnected) => RecvResult::Closed,
        }
    }

    pub fn try_recv(&self) -> RecvResult<C> {
        match self.inner.try_recv() {
            Ok(nf) => {
                self.waker.wake();
                RecvResult::Item(nf)
            }
            Err(TryRecvError::Empty) => RecvResult::Empty,
            Err(TryRecvError::Disconnected) => RecvResult::Closed,
        }
    }

    pub fn blocked_on(&self) -> BlockedOn {
        self.waker.blocked_on()
    }
}

pub enum AnswerSink<C> {
    Queue(AnswerSender<C>),
    DedupQueue {
        sender: AnswerSender<C>,
        seen: Arc<Mutex<HashSet<NF<C>>>>,
    },
    #[cfg(test)]
    Collector(Arc<Mutex<Vec<NF<C>>>>),
}

impl<C: Clone + Eq + Hash> AnswerSink<C> {
    pub fn push(&mut self, nf: NF<C>) -> SinkResult {
        match self {
            AnswerSink::Queue(sender) => sender.try_send(nf),
            AnswerSink::DedupQueue { sender, seen } => match seen.lock() {
                Ok(mut guard) => {
                    if guard.contains(&nf) {
                        return SinkResult::Accepted;
                    }
                    match sender.try_send(nf.clone()) {
                        SinkResult::Accepted => {
                            guard.insert(nf);
                            SinkResult::Accepted
                        }
                        other => other,
                    }
                }
                Err(_) => SinkResult::Closed,
            },
            #[cfg(test)]
            AnswerSink::Collector(out) => match out.lock() {
                Ok(mut guard) => {
                    guard.push(nf);
                    SinkResult::Accepted
                }
                Err(_) => SinkResult::Closed,
            },
        }
    }

    pub fn blocked_on(&self) -> Option<BlockedOn> {
        match self {
            AnswerSink::Queue(sender) => Some(sender.blocked_on()),
            AnswerSink::DedupQueue { sender, .. } => Some(sender.blocked_on()),
            #[cfg(test)]
            AnswerSink::Collector(_) => None,
        }
    }
}

#[cfg(test)]
mod tests {
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
}
