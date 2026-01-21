use crate::constraint::ConstraintOps;
use crate::queue::BlockedOn;
use crate::queue::WakeHub;
use crate::term::TermStore;
use crossbeam_channel::Receiver as WakeReceiver;
use crossbeam_deque::{Injector, Steal, Stealer, Worker};
use parking_lot::Mutex;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use crate::task::{Task, TaskContext, TaskStatus};

pub struct Scheduler<C: ConstraintOps> {
    terms: Arc<TermStore>,
    threads: usize,
    budget: usize,
    queue_bound: usize,
    cancelled: Arc<AtomicBool>,
    wake_hub: Arc<WakeHub>,
    wake_rx: WakeReceiver<u64>,
    metrics: Arc<SchedulerMetrics>,
    _marker: PhantomData<C>,
}

#[derive(Debug)]
pub struct SchedulerMetrics {
    search_steps: AtomicU64,
    join_steps: AtomicU64,
    fix_producer_steps: AtomicU64,
    bind_producer_steps: AtomicU64,
    blocked_nanos: AtomicU64,
    ready_samples: AtomicU64,
    ready_total: AtomicU64,
    ready_max: AtomicU64,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, Default)]
pub struct SchedulerMetricsSnapshot {
    pub search_steps: u64,
    pub join_steps: u64,
    pub fix_producer_steps: u64,
    pub bind_producer_steps: u64,
    pub blocked_nanos: u64,
    pub ready_samples: u64,
    pub ready_total: u64,
    pub ready_max: u64,
}

impl SchedulerMetrics {
    pub fn new() -> Self {
        Self {
            search_steps: AtomicU64::new(0),
            join_steps: AtomicU64::new(0),
            fix_producer_steps: AtomicU64::new(0),
            bind_producer_steps: AtomicU64::new(0),
            blocked_nanos: AtomicU64::new(0),
            ready_samples: AtomicU64::new(0),
            ready_total: AtomicU64::new(0),
            ready_max: AtomicU64::new(0),
        }
    }

    pub fn record_search_step(&self) {
        self.search_steps.fetch_add(1, Ordering::Relaxed);
    }

    pub fn record_join_step(&self) {
        self.join_steps.fetch_add(1, Ordering::Relaxed);
    }

    pub fn record_fix_producer_step(&self) {
        self.fix_producer_steps.fetch_add(1, Ordering::Relaxed);
    }

    pub fn record_bind_producer_step(&self) {
        self.bind_producer_steps.fetch_add(1, Ordering::Relaxed);
    }

    pub fn record_blocked_duration(&self, duration: Duration) {
        let nanos = duration.as_nanos();
        let nanos = if nanos > u128::from(u64::MAX) {
            u64::MAX
        } else {
            nanos as u64
        };
        self.blocked_nanos.fetch_add(nanos, Ordering::Relaxed);
    }

    pub fn record_ready(&self, ready: u64) {
        self.ready_samples.fetch_add(1, Ordering::Relaxed);
        self.ready_total.fetch_add(ready, Ordering::Relaxed);
        let mut current = self.ready_max.load(Ordering::Relaxed);
        while ready > current {
            match self.ready_max.compare_exchange_weak(
                current,
                ready,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(next) => current = next,
            }
        }
    }

    #[allow(dead_code)]
    pub fn snapshot(&self) -> SchedulerMetricsSnapshot {
        SchedulerMetricsSnapshot {
            search_steps: self.search_steps.load(Ordering::Relaxed),
            join_steps: self.join_steps.load(Ordering::Relaxed),
            fix_producer_steps: self.fix_producer_steps.load(Ordering::Relaxed),
            bind_producer_steps: self.bind_producer_steps.load(Ordering::Relaxed),
            blocked_nanos: self.blocked_nanos.load(Ordering::Relaxed),
            ready_samples: self.ready_samples.load(Ordering::Relaxed),
            ready_total: self.ready_total.load(Ordering::Relaxed),
            ready_max: self.ready_max.load(Ordering::Relaxed),
        }
    }
}

impl Default for SchedulerMetrics {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: ConstraintOps + 'static> Scheduler<C> {
    pub fn new(
        terms: Arc<TermStore>,
        threads: usize,
        budget: usize,
        queue_bound: usize,
        cancelled: Arc<AtomicBool>,
        wake_hub: Arc<WakeHub>,
        wake_rx: WakeReceiver<u64>,
    ) -> Self {
        Self {
            terms,
            threads: threads.max(1),
            budget: budget.max(1),
            queue_bound: queue_bound.max(1),
            cancelled,
            wake_hub,
            wake_rx,
            metrics: Arc::new(SchedulerMetrics::new()),
            _marker: PhantomData,
        }
    }

    #[allow(dead_code)]
    pub fn metrics(&self) -> Arc<SchedulerMetrics> {
        self.metrics.clone()
    }

    pub fn run(&self, initial: Vec<Task<C>>) {
        let injector = Arc::new(Injector::new());
        let pending = Arc::new(AtomicUsize::new(initial.len()));
        let blocked: Arc<Mutex<HashMap<u64, Vec<BlockedTask<C>>>>> =
            Arc::new(Mutex::new(HashMap::new()));
        let blocked_count = Arc::new(AtomicUsize::new(0));
        for task in initial {
            injector.push(task);
        }
        self.metrics
            .record_ready(ready_count(&pending, &blocked_count));

        let mut workers = Vec::with_capacity(self.threads);
        let mut stealers = Vec::with_capacity(self.threads);
        for _ in 0..self.threads {
            let worker = Worker::new_fifo();
            stealers.push(worker.stealer());
            workers.push(worker);
        }
        let stealers = Arc::new(stealers);

        let mut handles = Vec::with_capacity(self.threads);
        for worker in workers {
            let injector = injector.clone();
            let stealers = stealers.clone();
            let pending = pending.clone();
            let cancelled = self.cancelled.clone();
            let wake_hub = self.wake_hub.clone();
            let wake_rx = self.wake_rx.clone();
            let blocked = blocked.clone();
            let blocked_count = blocked_count.clone();
            let metrics = self.metrics.clone();
            let ctx = TaskContext {
                terms: self.terms.clone(),
                injector: injector.clone(),
                pending: pending.clone(),
                budget: self.budget,
                queue_bound: self.queue_bound,
                wake_hub: wake_hub.clone(),
                cancelled: cancelled.clone(),
            };
            let handle = thread::spawn(move || loop {
                if cancelled.load(Ordering::Acquire) {
                    break;
                }

                if pending.load(Ordering::Acquire) == 0 {
                    break;
                }

                drain_wakes(
                    &wake_rx,
                    &blocked,
                    &injector,
                    &metrics,
                    &pending,
                    &blocked_count,
                );

                let task = worker
                    .pop()
                    .or_else(|| steal_task(&worker, &injector, &stealers));

                let mut task = match task {
                    Some(task) => task,
                    None => {
                        if pending.load(Ordering::Acquire) == 0 {
                            break;
                        }
                        if !blocked.lock().is_empty() {
                            if let Ok(id) =
                                wake_rx.recv_timeout(std::time::Duration::from_millis(10))
                            {
                                requeue_blocked(
                                    id,
                                    &blocked,
                                    &injector,
                                    &metrics,
                                    &pending,
                                    &blocked_count,
                                );
                            }
                        } else {
                            thread::yield_now();
                        }
                        continue;
                    }
                };

                record_task_step(&metrics, &task);

                match task.run(&ctx) {
                    TaskStatus::Done => {
                        pending.fetch_sub(1, Ordering::AcqRel);
                        metrics.record_ready(ready_count(&pending, &blocked_count));
                    }
                    TaskStatus::Progress => {
                        if !cancelled.load(Ordering::Acquire) {
                            injector.push(task);
                            metrics.record_ready(ready_count(&pending, &blocked_count));
                        } else {
                            pending.fetch_sub(1, Ordering::AcqRel);
                            metrics.record_ready(ready_count(&pending, &blocked_count));
                        }
                    }
                    TaskStatus::Blocked(wait) => {
                        if cancelled.load(Ordering::Acquire) {
                            pending.fetch_sub(1, Ordering::AcqRel);
                            metrics.record_ready(ready_count(&pending, &blocked_count));
                        } else {
                            park_blocked(
                                task,
                                wait,
                                &blocked,
                                &injector,
                                &metrics,
                                &pending,
                                &blocked_count,
                            );
                        }
                    }
                }
            });
            handles.push(handle);
        }

        for handle in handles {
            let _ = handle.join();
        }
    }
}

struct BlockedTask<C: ConstraintOps> {
    task: Task<C>,
    since: Instant,
}

fn ready_count(pending: &AtomicUsize, blocked: &AtomicUsize) -> u64 {
    let pending = pending.load(Ordering::Acquire);
    let blocked = blocked.load(Ordering::Acquire);
    pending.saturating_sub(blocked) as u64
}

fn record_task_step<C: ConstraintOps>(metrics: &SchedulerMetrics, task: &Task<C>) {
    match task {
        Task::Search(_) => metrics.record_search_step(),
        Task::Join(_) => metrics.record_join_step(),
        Task::FixProducer(_) => metrics.record_fix_producer_step(),
        Task::BindProducer(_) => metrics.record_bind_producer_step(),
        #[cfg(test)]
        Task::TestBlocked(_) => {}
    }
}

fn steal_task<C: ConstraintOps>(
    worker: &Worker<Task<C>>,
    injector: &Injector<Task<C>>,
    stealers: &[Stealer<Task<C>>],
) -> Option<Task<C>> {
    loop {
        match injector.steal_batch_and_pop(worker) {
            Steal::Success(task) => return Some(task),
            Steal::Retry => continue,
            Steal::Empty => break,
        }
    }

    for stealer in stealers {
        loop {
            match stealer.steal_batch_and_pop(worker) {
                Steal::Success(task) => return Some(task),
                Steal::Retry => continue,
                Steal::Empty => break,
            }
        }
    }

    None
}

fn park_blocked<C: ConstraintOps>(
    task: Task<C>,
    wait: BlockedOn,
    blocked: &Mutex<HashMap<u64, Vec<BlockedTask<C>>>>,
    injector: &Injector<Task<C>>,
    metrics: &SchedulerMetrics,
    pending: &AtomicUsize,
    blocked_count: &AtomicUsize,
) {
    if wait.is_stale() {
        injector.push(task);
        metrics.record_ready(ready_count(pending, blocked_count));
        return;
    }
    blocked_count.fetch_add(1, Ordering::AcqRel);
    let mut guard = blocked.lock();
    guard.entry(wait.id()).or_default().push(BlockedTask {
        task,
        since: Instant::now(),
    });
    metrics.record_ready(ready_count(pending, blocked_count));
}

fn requeue_blocked<C: ConstraintOps>(
    id: u64,
    blocked: &Mutex<HashMap<u64, Vec<BlockedTask<C>>>>,
    injector: &Injector<Task<C>>,
    metrics: &SchedulerMetrics,
    pending: &AtomicUsize,
    blocked_count: &AtomicUsize,
) {
    let tasks = blocked.lock().remove(&id);
    if let Some(tasks) = tasks {
        blocked_count.fetch_sub(tasks.len(), Ordering::AcqRel);
        for task in tasks {
            metrics.record_blocked_duration(task.since.elapsed());
            injector.push(task.task);
        }
    }
    metrics.record_ready(ready_count(pending, blocked_count));
}

fn drain_wakes<C: ConstraintOps>(
    wake_rx: &WakeReceiver<u64>,
    blocked: &Mutex<HashMap<u64, Vec<BlockedTask<C>>>>,
    injector: &Injector<Task<C>>,
    metrics: &SchedulerMetrics,
    pending: &AtomicUsize,
    blocked_count: &AtomicUsize,
) {
    while let Ok(id) = wake_rx.try_recv() {
        requeue_blocked(id, blocked, injector, metrics, pending, blocked_count);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::join::AndJoiner;
    use crate::node::Node;
    use crate::queue::WakeHub;
    use crate::queue::{AnswerQueue, AnswerSink};
    use crate::task::{JoinTask, SearchTask, TestBlockedTask};
    use std::sync::atomic::AtomicUsize;
    use std::sync::mpsc;
    use std::time::Duration;

    #[test]
    fn blocked_task_waits_for_wake() {
        let terms = Arc::new(TermStore::new());
        let (wake_hub, wake_rx) = WakeHub::new();
        let cancelled = Arc::new(AtomicBool::new(false));
        let scheduler: Scheduler<()> =
            Scheduler::new(terms, 1, 1, 1, cancelled.clone(), wake_hub.clone(), wake_rx);

        let runs = Arc::new(AtomicUsize::new(0));
        let waker = wake_hub.waker();
        let task = Task::TestBlocked(TestBlockedTask::block_forever(runs.clone(), waker.clone()));

        let handle = thread::spawn(move || scheduler.run(vec![task]));

        let start = std::time::Instant::now();
        while runs.load(Ordering::Acquire) == 0 && start.elapsed() < Duration::from_millis(200) {
            thread::yield_now();
        }
        assert_eq!(
            runs.load(Ordering::Acquire),
            1,
            "blocked task should start once"
        );
        thread::sleep(Duration::from_millis(20));
        assert_eq!(
            runs.load(Ordering::Acquire),
            1,
            "blocked task should not spin"
        );

        waker.wake();
        thread::sleep(Duration::from_millis(20));
        assert!(
            runs.load(Ordering::Acquire) > 1,
            "wake should requeue blocked task"
        );

        cancelled.store(true, Ordering::Release);
        let _ = handle.join();
    }

    #[test]
    fn stale_wake_requeues_immediately() {
        let terms = Arc::new(TermStore::new());
        let (wake_hub, wake_rx) = WakeHub::new();
        let cancelled = Arc::new(AtomicBool::new(false));
        let scheduler: Scheduler<()> =
            Scheduler::new(terms, 1, 1, 1, cancelled.clone(), wake_hub.clone(), wake_rx);

        let runs = Arc::new(AtomicUsize::new(0));
        let waker = wake_hub.waker();
        let blocked_on = waker.blocked_on();
        waker.wake(); // make the blocked token stale

        let task = Task::TestBlocked(TestBlockedTask::block_once(runs.clone(), blocked_on));
        let (done_tx, done_rx) = mpsc::channel();

        let handle = thread::spawn(move || {
            scheduler.run(vec![task]);
            let _ = done_tx.send(());
        });

        let done = done_rx.recv_timeout(Duration::from_millis(100)).is_ok();
        if !done {
            cancelled.store(true, Ordering::Release);
        }
        let _ = handle.join();

        assert!(done, "scheduler should not strand stale-blocked task");
        assert_eq!(runs.load(Ordering::Acquire), 2);
    }

    #[test]
    fn wake_resumes_all_blocked_tasks() {
        let terms = Arc::new(TermStore::new());
        let (wake_hub, wake_rx) = WakeHub::new();
        let cancelled = Arc::new(AtomicBool::new(false));
        let scheduler: Scheduler<()> =
            Scheduler::new(terms, 1, 1, 1, cancelled.clone(), wake_hub.clone(), wake_rx);

        let runs_a = Arc::new(AtomicUsize::new(0));
        let runs_b = Arc::new(AtomicUsize::new(0));
        let waker = wake_hub.waker();

        let task_a = Task::TestBlocked(TestBlockedTask::block_once(
            runs_a.clone(),
            waker.blocked_on(),
        ));
        let task_b = Task::TestBlocked(TestBlockedTask::block_once(
            runs_b.clone(),
            waker.blocked_on(),
        ));

        let (done_tx, done_rx) = mpsc::channel();
        let handle = thread::spawn(move || {
            scheduler.run(vec![task_a, task_b]);
            let _ = done_tx.send(());
        });

        thread::sleep(Duration::from_millis(20));
        waker.wake();

        let done = done_rx.recv_timeout(Duration::from_millis(200)).is_ok();
        if !done {
            cancelled.store(true, Ordering::Release);
        }
        let _ = handle.join();

        assert!(done, "scheduler should resume all blocked tasks");
        assert_eq!(runs_a.load(Ordering::Acquire), 2);
        assert_eq!(runs_b.load(Ordering::Acquire), 2);
    }

    fn make_search_task() -> Task<()> {
        let (tx, _rx) = AnswerQueue::bounded::<()>(1);
        Task::Search(SearchTask::new(Node::Fail, AnswerSink::Queue(tx)))
    }

    fn make_join_task() -> Task<()> {
        let (_tx, rx) = AnswerQueue::bounded::<()>(1);
        let joiner = AndJoiner::new(vec![rx]);
        let (sink_tx, _sink_rx) = AnswerQueue::bounded::<()>(1);
        Task::Join(JoinTask::new(joiner, AnswerSink::Queue(sink_tx)))
    }

    #[test]
    fn scheduler_metrics_counts_task_steps() {
        let terms = Arc::new(TermStore::new());
        let (wake_hub, wake_rx) = WakeHub::new();
        let cancelled = Arc::new(AtomicBool::new(false));
        let scheduler: Scheduler<()> =
            Scheduler::new(terms, 1, 1, 1, cancelled.clone(), wake_hub.clone(), wake_rx);
        let metrics = scheduler.metrics();

        let handle =
            thread::spawn(move || scheduler.run(vec![make_search_task(), make_join_task()]));
        let _ = handle.join();

        let snapshot = metrics.snapshot();
        assert_eq!(snapshot.search_steps, 1);
        assert_eq!(snapshot.join_steps, 1);
    }

    #[test]
    fn scheduler_metrics_counts_task_steps_dual() {
        let terms = Arc::new(TermStore::new());
        let (wake_hub, wake_rx) = WakeHub::new();
        let cancelled = Arc::new(AtomicBool::new(false));
        let scheduler: Scheduler<()> =
            Scheduler::new(terms, 1, 1, 1, cancelled.clone(), wake_hub.clone(), wake_rx);
        let metrics = scheduler.metrics();

        let handle =
            thread::spawn(move || scheduler.run(vec![make_search_task(), make_join_task()]));
        let _ = handle.join();

        let snapshot = metrics.snapshot();
        assert_eq!(snapshot.search_steps, 1);
        assert_eq!(snapshot.join_steps, 1);
    }

    #[test]
    fn scheduler_metrics_records_blocked_time() {
        let terms = Arc::new(TermStore::new());
        let (wake_hub, wake_rx) = WakeHub::new();
        let cancelled = Arc::new(AtomicBool::new(false));
        let scheduler: Scheduler<()> =
            Scheduler::new(terms, 1, 1, 1, cancelled.clone(), wake_hub.clone(), wake_rx);
        let metrics = scheduler.metrics();

        let runs = Arc::new(AtomicUsize::new(0));
        let waker = wake_hub.waker();
        let task = Task::TestBlocked(TestBlockedTask::block_once(
            runs.clone(),
            waker.blocked_on(),
        ));

        let handle = thread::spawn(move || scheduler.run(vec![task]));
        thread::sleep(Duration::from_millis(20));
        waker.wake();
        let _ = handle.join();

        let snapshot = metrics.snapshot();
        assert!(
            snapshot.blocked_nanos > 0,
            "blocked duration should be recorded"
        );
    }

    #[test]
    fn scheduler_metrics_records_blocked_time_dual() {
        let terms = Arc::new(TermStore::new());
        let (wake_hub, wake_rx) = WakeHub::new();
        let cancelled = Arc::new(AtomicBool::new(false));
        let scheduler: Scheduler<()> =
            Scheduler::new(terms, 1, 1, 1, cancelled.clone(), wake_hub.clone(), wake_rx);
        let metrics = scheduler.metrics();

        let runs = Arc::new(AtomicUsize::new(0));
        let waker = wake_hub.waker();
        let task = Task::TestBlocked(TestBlockedTask::block_once(
            runs.clone(),
            waker.blocked_on(),
        ));

        let handle = thread::spawn(move || scheduler.run(vec![task]));
        thread::sleep(Duration::from_millis(20));
        waker.wake();
        let _ = handle.join();

        let snapshot = metrics.snapshot();
        assert!(
            snapshot.blocked_nanos > 0,
            "blocked duration should be recorded"
        );
    }

    #[test]
    fn scheduler_metrics_records_ready_queue() {
        let terms = Arc::new(TermStore::new());
        let (wake_hub, wake_rx) = WakeHub::new();
        let cancelled = Arc::new(AtomicBool::new(false));
        let scheduler: Scheduler<()> =
            Scheduler::new(terms, 1, 1, 1, cancelled.clone(), wake_hub.clone(), wake_rx);
        let metrics = scheduler.metrics();

        let handle = thread::spawn(move || {
            scheduler.run(vec![make_search_task(), make_search_task()]);
        });
        let _ = handle.join();

        let snapshot = metrics.snapshot();
        assert!(snapshot.ready_max >= 2);
        assert!(snapshot.ready_samples > 0);
    }

    #[test]
    fn scheduler_metrics_records_ready_queue_dual() {
        let terms = Arc::new(TermStore::new());
        let (wake_hub, wake_rx) = WakeHub::new();
        let cancelled = Arc::new(AtomicBool::new(false));
        let scheduler: Scheduler<()> =
            Scheduler::new(terms, 1, 1, 1, cancelled.clone(), wake_hub.clone(), wake_rx);
        let metrics = scheduler.metrics();

        let handle = thread::spawn(move || {
            scheduler.run(vec![make_search_task(), make_search_task()]);
        });
        let _ = handle.join();

        let snapshot = metrics.snapshot();
        assert!(snapshot.ready_max >= 2);
        assert!(snapshot.ready_samples > 0);
    }
}
