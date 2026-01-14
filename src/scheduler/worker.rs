use crossbeam_deque::{Injector, Steal, Stealer, Worker as CbWorker};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread::JoinHandle;

use crate::eval::{step, EvalCtx, RuleStore, StepResult};
use crate::goal::GoalStore;
use crate::task::Task;
use crate::term::TermStore;

/// A work unit that can be scheduled.
#[derive(Debug)]
pub struct WorkUnit<C> {
    pub task: Task<C>,
}

impl<C> WorkUnit<C> {
    pub fn new(task: Task<C>) -> Self {
        Self { task }
    }
}

/// Statistics for a worker.
#[derive(Debug, Default)]
pub struct WorkerStats {
    pub tasks_processed: AtomicUsize,
    pub tasks_completed: AtomicUsize,
    pub tasks_yielded: AtomicUsize,
    pub steals_attempted: AtomicUsize,
    pub steals_successful: AtomicUsize,
}

impl WorkerStats {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn record_processed(&self) {
        self.tasks_processed.fetch_add(1, Ordering::Relaxed);
    }

    pub fn record_completed(&self) {
        self.tasks_completed.fetch_add(1, Ordering::Relaxed);
    }

    pub fn record_yielded(&self) {
        self.tasks_yielded.fetch_add(1, Ordering::Relaxed);
    }

    pub fn record_steal_attempt(&self) {
        self.steals_attempted.fetch_add(1, Ordering::Relaxed);
    }

    pub fn record_steal_success(&self) {
        self.steals_successful.fetch_add(1, Ordering::Relaxed);
    }
}

/// Worker configuration.
#[derive(Debug, Clone)]
pub struct WorkerConfig {
    /// Maximum steps to execute per task before yielding.
    pub budget: usize,
    /// Worker ID.
    pub id: usize,
}

impl Default for WorkerConfig {
    fn default() -> Self {
        Self {
            budget: 100,
            id: 0,
        }
    }
}

/// State shared between a worker thread and the scheduler.
pub struct WorkerShared<C: Send> {
    /// Stealer to steal from this worker's local queue.
    pub stealer: Stealer<WorkUnit<C>>,
    /// Statistics.
    pub stats: Arc<WorkerStats>,
    /// Stop flag.
    pub stop: Arc<AtomicBool>,
}

/// A worker that processes tasks.
pub struct Worker<C: Send> {
    /// Local work queue.
    local: CbWorker<WorkUnit<C>>,
    /// Global injector for new tasks.
    injector: Arc<Injector<WorkUnit<C>>>,
    /// Stealers from other workers.
    stealers: Vec<Stealer<WorkUnit<C>>>,
    /// Configuration.
    config: WorkerConfig,
    /// Statistics.
    stats: Arc<WorkerStats>,
    /// Stop flag.
    stop: Arc<AtomicBool>,
}

impl<C: Clone + Default + PartialEq + Send + 'static> Worker<C> {
    /// Create a new worker.
    pub fn new(
        injector: Arc<Injector<WorkUnit<C>>>,
        stealers: Vec<Stealer<WorkUnit<C>>>,
        config: WorkerConfig,
    ) -> (Self, WorkerShared<C>) {
        let local = CbWorker::new_fifo();
        let stealer = local.stealer();
        let stats = Arc::new(WorkerStats::new());
        let stop = Arc::new(AtomicBool::new(false));

        let worker = Self {
            local,
            injector,
            stealers,
            config,
            stats: Arc::clone(&stats),
            stop: Arc::clone(&stop),
        };

        let shared = WorkerShared {
            stealer,
            stats,
            stop,
        };

        (worker, shared)
    }

    /// Get the local queue for pushing work directly.
    pub fn local(&self) -> &CbWorker<WorkUnit<C>> {
        &self.local
    }

    /// Get worker statistics.
    pub fn stats(&self) -> &WorkerStats {
        &self.stats
    }

    /// Signal the worker to stop.
    pub fn signal_stop(&self) {
        self.stop.store(true, Ordering::SeqCst);
    }

    /// Check if the worker should stop.
    pub fn should_stop(&self) -> bool {
        self.stop.load(Ordering::SeqCst)
    }

    /// Try to get a task to work on.
    pub fn find_task(&self) -> Option<WorkUnit<C>> {
        // First try local queue
        if let Some(unit) = self.local.pop() {
            return Some(unit);
        }

        // Then try global injector
        loop {
            match self.injector.steal() {
                Steal::Success(unit) => return Some(unit),
                Steal::Empty => break,
                Steal::Retry => continue,
            }
        }

        // Finally try stealing from other workers
        self.stats.record_steal_attempt();
        for stealer in &self.stealers {
            loop {
                match stealer.steal() {
                    Steal::Success(unit) => {
                        self.stats.record_steal_success();
                        return Some(unit);
                    }
                    Steal::Empty => break,
                    Steal::Retry => continue,
                }
            }
        }

        None
    }

    /// Process a single task for up to `budget` steps.
    ///
    /// Returns the task if it's not done, or None if complete.
    pub fn process_task(
        &self,
        mut unit: WorkUnit<C>,
        ctx: &mut EvalCtx<'_, C>,
    ) -> Option<WorkUnit<C>> {
        self.stats.record_processed();

        for _ in 0..self.config.budget {
            if self.should_stop() {
                return Some(unit);
            }

            let result = step(&mut unit.task, ctx);

            match result {
                StepResult::Continue => {
                    // Keep going
                }
                StepResult::Yielded(_) => {
                    self.stats.record_yielded();
                    // Task yielded - return for further processing
                    return Some(unit);
                }
                StepResult::Blocked(_) => {
                    // Task is blocked - return for later
                    return Some(unit);
                }
                StepResult::Done => {
                    self.stats.record_completed();
                    return None;
                }
            }
        }

        // Budget exhausted - return task for later
        Some(unit)
    }

    /// Run the worker loop.
    pub fn run(
        &self,
        goals: &GoalStore,
        rules: &RuleStore<C>,
        terms: &mut TermStore,
    ) {
        while !self.should_stop() {
            if let Some(unit) = self.find_task() {
                let mut ctx = EvalCtx { goals, rules, terms };
                if let Some(remaining) = self.process_task(unit, &mut ctx) {
                    // Task not done - re-queue it
                    self.local.push(remaining);
                }
            } else {
                // No work available - yield
                std::thread::yield_now();
            }
        }
    }
}

/// Handle to a worker thread.
pub struct WorkerHandle<C: Send> {
    /// The worker's shared state.
    pub shared: WorkerShared<C>,
    /// The thread handle (if spawned).
    thread: Option<JoinHandle<()>>,
}

impl<C: Send> WorkerHandle<C> {
    /// Create a new handle.
    pub fn new(shared: WorkerShared<C>) -> Self {
        Self {
            shared,
            thread: None,
        }
    }

    /// Signal the worker to stop.
    pub fn signal_stop(&self) {
        self.shared.stop.store(true, Ordering::SeqCst);
    }

    /// Wait for the worker to finish (if spawned as thread).
    pub fn join(mut self) -> Result<(), Box<dyn std::any::Any + Send>> {
        if let Some(handle) = self.thread.take() {
            handle.join()
        } else {
            Ok(())
        }
    }

    /// Get worker statistics.
    pub fn stats(&self) -> &WorkerStats {
        &self.shared.stats
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nf::NF;
    use crate::wire::Wire;
    use smallvec::smallvec;
    use std::sync::Arc;

    fn make_identity_nf() -> NF<()> {
        NF::new(smallvec![], Wire::identity(0), smallvec![])
    }

    // ========== WORK UNIT TESTS ==========

    #[test]
    fn work_unit_wraps_task() {
        let task: Task<()> = Task::new(0, 0, make_identity_nf());
        let unit = WorkUnit::new(task);
        assert_eq!(unit.task.id, 0);
    }

    // ========== WORKER STATS TESTS ==========

    #[test]
    fn worker_stats_new_is_zero() {
        let stats = WorkerStats::new();
        assert_eq!(stats.tasks_processed.load(Ordering::Relaxed), 0);
        assert_eq!(stats.tasks_completed.load(Ordering::Relaxed), 0);
        assert_eq!(stats.tasks_yielded.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn worker_stats_record_processed() {
        let stats = WorkerStats::new();
        stats.record_processed();
        stats.record_processed();
        assert_eq!(stats.tasks_processed.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn worker_stats_record_completed() {
        let stats = WorkerStats::new();
        stats.record_completed();
        assert_eq!(stats.tasks_completed.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn worker_stats_record_yielded() {
        let stats = WorkerStats::new();
        stats.record_yielded();
        assert_eq!(stats.tasks_yielded.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn worker_stats_record_steals() {
        let stats = WorkerStats::new();
        stats.record_steal_attempt();
        stats.record_steal_attempt();
        stats.record_steal_success();
        assert_eq!(stats.steals_attempted.load(Ordering::Relaxed), 2);
        assert_eq!(stats.steals_successful.load(Ordering::Relaxed), 1);
    }

    // ========== WORKER CONFIG TESTS ==========

    #[test]
    fn worker_config_default() {
        let config = WorkerConfig::default();
        assert_eq!(config.budget, 100);
        assert_eq!(config.id, 0);
    }

    #[test]
    fn worker_config_custom() {
        let config = WorkerConfig {
            budget: 50,
            id: 5,
        };
        assert_eq!(config.budget, 50);
        assert_eq!(config.id, 5);
    }

    // ========== WORKER CREATION TESTS ==========

    #[test]
    fn worker_creation() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());
        let config = WorkerConfig::default();
        let (worker, shared) = Worker::new(Arc::clone(&injector), vec![], config);

        assert!(!worker.should_stop());
        assert_eq!(shared.stats.tasks_processed.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn worker_stop_signal() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());
        let config = WorkerConfig::default();
        let (worker, _shared) = Worker::new(Arc::clone(&injector), vec![], config);

        assert!(!worker.should_stop());
        worker.signal_stop();
        assert!(worker.should_stop());
    }

    // ========== TASK FINDING TESTS ==========

    #[test]
    fn find_task_from_local_queue() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());
        let config = WorkerConfig::default();
        let (worker, _shared) = Worker::new(Arc::clone(&injector), vec![], config);

        // Push directly to local queue
        let task = Task::new(0, 0, make_identity_nf());
        worker.local().push(WorkUnit::new(task));

        let found = worker.find_task();
        assert!(found.is_some());
        assert_eq!(found.unwrap().task.id, 0);
    }

    #[test]
    fn find_task_from_injector() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());
        let config = WorkerConfig::default();
        let (worker, _shared) = Worker::new(Arc::clone(&injector), vec![], config);

        // Push to global injector
        let task = Task::new(1, 0, make_identity_nf());
        injector.push(WorkUnit::new(task));

        let found = worker.find_task();
        assert!(found.is_some());
        assert_eq!(found.unwrap().task.id, 1);
    }

    #[test]
    fn find_task_steals_from_other_worker() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());

        // Create first worker with work
        let config1 = WorkerConfig { budget: 100, id: 0 };
        let (worker1, shared1) = Worker::new(Arc::clone(&injector), vec![], config1);

        // Create second worker that can steal from first
        let config2 = WorkerConfig { budget: 100, id: 1 };
        let (worker2, _shared2) = Worker::new(
            Arc::clone(&injector),
            vec![shared1.stealer],
            config2,
        );

        // Push to worker1's local queue
        let task = Task::new(2, 0, make_identity_nf());
        worker1.local().push(WorkUnit::new(task));

        // Worker2 should be able to steal it
        let found = worker2.find_task();
        assert!(found.is_some());
        assert_eq!(found.unwrap().task.id, 2);
    }

    #[test]
    fn find_task_returns_none_when_empty() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());
        let config = WorkerConfig::default();
        let (worker, _shared) = Worker::new(Arc::clone(&injector), vec![], config);

        let found = worker.find_task();
        assert!(found.is_none());
    }

    #[test]
    fn find_task_prefers_local_over_injector() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());
        let config = WorkerConfig::default();
        let (worker, _shared) = Worker::new(Arc::clone(&injector), vec![], config);

        // Push to both local and injector
        let local_task = Task::new(10, 0, make_identity_nf());
        let global_task = Task::new(20, 0, make_identity_nf());
        worker.local().push(WorkUnit::new(local_task));
        injector.push(WorkUnit::new(global_task));

        // Should get local task first
        let found = worker.find_task();
        assert!(found.is_some());
        assert_eq!(found.unwrap().task.id, 10);

        // Then global task
        let found2 = worker.find_task();
        assert!(found2.is_some());
        assert_eq!(found2.unwrap().task.id, 20);
    }

    // ========== TASK PROCESSING TESTS ==========

    #[test]
    fn process_task_fail_completes() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());
        let config = WorkerConfig::default();
        let (worker, _shared) = Worker::new(Arc::clone(&injector), vec![], config);

        let mut goals = GoalStore::new();
        let fail_id = goals.fail();

        let rules: RuleStore<()> = RuleStore::new();
        let mut terms = TermStore::new();

        let task = Task::new(0, fail_id, make_identity_nf());
        let unit = WorkUnit::new(task);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = worker.process_task(unit, &mut ctx);
        assert!(result.is_none()); // Task completed
        assert_eq!(worker.stats().tasks_completed.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn process_task_rule_yields() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());
        let config = WorkerConfig::default();
        let (worker, _shared) = Worker::new(Arc::clone(&injector), vec![], config);

        let mut goals = GoalStore::new();
        let mut rules: RuleStore<()> = RuleStore::new();
        let rule_id = rules.add(make_identity_nf());
        let goal_id = goals.rule(rule_id);

        let mut terms = TermStore::new();

        let task = Task::new(0, goal_id, make_identity_nf());
        let unit = WorkUnit::new(task);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = worker.process_task(unit, &mut ctx);
        assert!(result.is_some()); // Task yielded
        assert!(result.unwrap().task.is_yielded());
        assert_eq!(worker.stats().tasks_yielded.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn process_task_respects_budget() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());
        // Very small budget
        let config = WorkerConfig { budget: 2, id: 0 };
        let (worker, _shared) = Worker::new(Arc::clone(&injector), vec![], config);

        let mut goals = GoalStore::new();
        // Create a deep nested Alt that takes many steps
        let r1 = goals.rule(0);
        let r2 = goals.rule(1);
        let r3 = goals.rule(2);
        let alt_id = goals.alt(smallvec![r1, r2, r3]);

        let mut rules: RuleStore<()> = RuleStore::new();
        rules.add(make_identity_nf());
        rules.add(make_identity_nf());
        rules.add(make_identity_nf());

        let mut terms = TermStore::new();

        let task = Task::new(0, alt_id, make_identity_nf());
        let unit = WorkUnit::new(task);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        // Process with budget of 2 - should return task not yet complete
        let result = worker.process_task(unit, &mut ctx);
        assert!(result.is_some()); // Task returned due to budget or yield
    }

    #[test]
    fn process_task_blocked_returns_task() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());
        let config = WorkerConfig::default();
        let (worker, _shared) = Worker::new(Arc::clone(&injector), vec![], config);

        let mut goals = GoalStore::new();
        let rel_id = goals.new_rel("test");
        let call_id = goals.call(rel_id);

        let rules: RuleStore<()> = RuleStore::new();
        let mut terms = TermStore::new();

        let task = Task::new(0, call_id, make_identity_nf());
        let unit = WorkUnit::new(task);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = worker.process_task(unit, &mut ctx);
        assert!(result.is_some()); // Task blocked
        assert!(result.unwrap().task.is_blocked());
    }

    #[test]
    fn process_task_stops_on_signal() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());
        let config = WorkerConfig { budget: 1000, id: 0 };
        let (worker, _shared) = Worker::new(Arc::clone(&injector), vec![], config);

        // Signal stop before processing
        worker.signal_stop();

        let mut goals = GoalStore::new();
        let r1 = goals.rule(0);
        let r2 = goals.rule(1);
        let seq_id = goals.seq(smallvec![r1, r2]);

        let mut rules: RuleStore<()> = RuleStore::new();
        rules.add(make_identity_nf());
        rules.add(make_identity_nf());

        let mut terms = TermStore::new();

        let task = Task::new(0, seq_id, make_identity_nf());
        let unit = WorkUnit::new(task);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = worker.process_task(unit, &mut ctx);
        // Task should be returned even though not complete
        assert!(result.is_some());
    }

    // ========== WORKER HANDLE TESTS ==========

    #[test]
    fn worker_handle_signal_stop() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());
        let config = WorkerConfig::default();
        let (_worker, shared) = Worker::new(Arc::clone(&injector), vec![], config);
        let handle = WorkerHandle::new(shared);

        assert!(!handle.shared.stop.load(Ordering::SeqCst));
        handle.signal_stop();
        assert!(handle.shared.stop.load(Ordering::SeqCst));
    }

    #[test]
    fn worker_handle_stats_access() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());
        let config = WorkerConfig::default();
        let (_worker, shared) = Worker::new(Arc::clone(&injector), vec![], config);
        let handle = WorkerHandle::new(shared);

        handle.stats().record_processed();
        assert_eq!(handle.stats().tasks_processed.load(Ordering::Relaxed), 1);
    }

    // ========== CONCURRENT TESTS ==========

    #[test]
    fn multiple_workers_share_injector() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());

        // Create multiple workers
        let config1 = WorkerConfig { budget: 100, id: 0 };
        let config2 = WorkerConfig { budget: 100, id: 1 };
        let (worker1, shared1) = Worker::new(Arc::clone(&injector), vec![], config1);
        let (worker2, _shared2) = Worker::new(
            Arc::clone(&injector),
            vec![shared1.stealer],
            config2,
        );

        // Push multiple tasks to injector
        for i in 0..10 {
            let task = Task::new(i, 0, make_identity_nf());
            injector.push(WorkUnit::new(task));
        }

        // Both workers should be able to find tasks
        let found1 = worker1.find_task();
        let found2 = worker2.find_task();
        assert!(found1.is_some());
        assert!(found2.is_some());
    }

    #[test]
    fn work_stealing_with_multiple_workers() {
        let injector: Arc<Injector<WorkUnit<()>>> = Arc::new(Injector::new());

        // Worker 1 has work
        let config1 = WorkerConfig { budget: 100, id: 0 };
        let (worker1, shared1) = Worker::new(Arc::clone(&injector), vec![], config1);

        // Worker 2 can steal from worker 1
        let config2 = WorkerConfig { budget: 100, id: 1 };
        let (worker2, shared2) = Worker::new(
            Arc::clone(&injector),
            vec![shared1.stealer],
            config2,
        );

        // Worker 3 can steal from both
        let config3 = WorkerConfig { budget: 100, id: 2 };
        let (worker3, _shared3) = Worker::new(
            Arc::clone(&injector),
            vec![shared2.stealer],
            config3,
        );

        // Push work to worker1's local queue
        for i in 0..5 {
            let task = Task::new(i, 0, make_identity_nf());
            worker1.local().push(WorkUnit::new(task));
        }

        // Worker2 should be able to steal
        let stolen = worker2.find_task();
        assert!(stolen.is_some());

        // Put the stolen work in worker2's queue
        let task = Task::new(100, 0, make_identity_nf());
        worker2.local().push(WorkUnit::new(task));

        // Worker3 should be able to steal from worker2
        let stolen3 = worker3.find_task();
        assert!(stolen3.is_some());
    }
}
