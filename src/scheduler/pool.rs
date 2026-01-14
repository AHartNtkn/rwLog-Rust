use crossbeam_deque::Injector;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;

use crate::eval::RuleStore;
use crate::goal::GoalStore;
use crate::nf::NF;
use crate::task::Task;
use crate::term::TermStore;

use super::worker::{Worker, WorkerConfig, WorkerShared, WorkUnit};

/// Configuration for the scheduler.
#[derive(Debug, Clone)]
pub struct SchedulerConfig {
    /// Number of worker threads.
    pub num_workers: usize,
    /// Budget per task per worker.
    pub task_budget: usize,
}

impl Default for SchedulerConfig {
    fn default() -> Self {
        Self {
            num_workers: num_cpus(),
            task_budget: 100,
        }
    }
}

/// Get number of CPUs (fallback to 1).
fn num_cpus() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}

/// Global scheduler statistics.
#[derive(Debug, Default)]
pub struct SchedulerStats {
    pub tasks_submitted: AtomicUsize,
    pub tasks_completed: AtomicUsize,
}

impl SchedulerStats {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn record_submitted(&self) {
        self.tasks_submitted.fetch_add(1, Ordering::Relaxed);
    }

    pub fn record_completed(&self) {
        self.tasks_completed.fetch_add(1, Ordering::Relaxed);
    }
}

/// A work-stealing scheduler for parallel task execution.
pub struct Scheduler<C: Send + 'static> {
    /// Global task injector.
    injector: Arc<Injector<WorkUnit<C>>>,
    /// Worker handles.
    workers: Vec<WorkerShared<C>>,
    /// Global stop flag.
    stop: Arc<AtomicBool>,
    /// Statistics.
    stats: Arc<SchedulerStats>,
    /// Configuration.
    config: SchedulerConfig,
    /// Next task ID.
    next_task_id: AtomicUsize,
}

impl<C: Clone + Default + PartialEq + Send + 'static> Scheduler<C> {
    /// Create a new scheduler with default configuration.
    pub fn new() -> Self {
        Self::with_config(SchedulerConfig::default())
    }

    /// Create a new scheduler with custom configuration.
    pub fn with_config(config: SchedulerConfig) -> Self {
        let injector = Arc::new(Injector::new());
        let stop = Arc::new(AtomicBool::new(false));
        let stats = Arc::new(SchedulerStats::new());

        Self {
            injector,
            workers: Vec::new(),
            stop,
            stats,
            config,
            next_task_id: AtomicUsize::new(0),
        }
    }

    /// Get the global injector for submitting tasks.
    pub fn injector(&self) -> &Arc<Injector<WorkUnit<C>>> {
        &self.injector
    }

    /// Submit a new task to the scheduler.
    pub fn submit(&self, goal: u32, input: NF<C>) -> u32 {
        let id = self.next_task_id.fetch_add(1, Ordering::SeqCst) as u32;
        let task = Task::new(id, goal, input);
        let unit = WorkUnit::new(task);
        self.injector.push(unit);
        self.stats.record_submitted();
        id
    }

    /// Signal all workers to stop.
    pub fn stop(&self) {
        self.stop.store(true, Ordering::SeqCst);
        for worker in &self.workers {
            worker.stop.store(true, Ordering::SeqCst);
        }
    }

    /// Check if the scheduler is stopped.
    pub fn is_stopped(&self) -> bool {
        self.stop.load(Ordering::SeqCst)
    }

    /// Get scheduler statistics.
    pub fn stats(&self) -> &SchedulerStats {
        &self.stats
    }

    /// Get configuration.
    pub fn config(&self) -> &SchedulerConfig {
        &self.config
    }

    /// Get the number of workers.
    pub fn num_workers(&self) -> usize {
        self.workers.len()
    }

    /// Create workers but don't start them.
    ///
    /// Returns the workers and their shared state.
    pub fn create_workers(&mut self) -> Vec<Worker<C>> {
        let mut workers = Vec::new();
        let mut shareds = Vec::new();

        // First pass: create all workers
        for i in 0..self.config.num_workers {
            let config = WorkerConfig {
                budget: self.config.task_budget,
                id: i,
            };
            let (worker, shared) = Worker::new(
                Arc::clone(&self.injector),
                vec![], // Will be filled in second pass
                config,
            );
            workers.push(worker);
            shareds.push(shared);
        }

        // Store shared state
        self.workers = shareds;

        workers
    }

    /// Check if the injector is empty.
    pub fn is_empty(&self) -> bool {
        self.injector.is_empty()
    }

    /// Get aggregate stats from all workers.
    pub fn aggregate_worker_stats(&self) -> (usize, usize, usize) {
        let mut processed = 0;
        let mut completed = 0;
        let mut yielded = 0;
        for worker in &self.workers {
            processed += worker.stats.tasks_processed.load(Ordering::Relaxed);
            completed += worker.stats.tasks_completed.load(Ordering::Relaxed);
            yielded += worker.stats.tasks_yielded.load(Ordering::Relaxed);
        }
        (processed, completed, yielded)
    }
}

impl<C: Clone + Default + PartialEq + Send + 'static> Default for Scheduler<C> {
    fn default() -> Self {
        Self::new()
    }
}

/// A simple single-threaded executor for testing.
pub struct SingleThreadExecutor<'a, C: Clone + Default + PartialEq + Send + 'static> {
    scheduler: &'a Scheduler<C>,
    worker: Worker<C>,
}

impl<'a, C: Clone + Default + PartialEq + Send + 'static> SingleThreadExecutor<'a, C> {
    /// Create a new single-threaded executor.
    pub fn new(scheduler: &'a mut Scheduler<C>) -> Self {
        let config = WorkerConfig {
            budget: scheduler.config.task_budget,
            id: 0,
        };
        let (worker, shared) = Worker::new(
            Arc::clone(&scheduler.injector),
            vec![],
            config,
        );
        scheduler.workers.push(shared);
        Self { scheduler, worker }
    }

    /// Run tasks until the injector is empty or stop is signaled.
    pub fn run_until_empty(
        &self,
        goals: &GoalStore,
        rules: &RuleStore<C>,
        terms: &mut TermStore,
    ) {
        use crate::eval::EvalCtx;

        while !self.scheduler.is_stopped() {
            if let Some(unit) = self.worker.find_task() {
                let mut ctx = EvalCtx { goals, rules, terms };
                if let Some(remaining) = self.worker.process_task(unit, &mut ctx) {
                    // Re-queue incomplete tasks
                    self.worker.local().push(remaining);
                }
            } else if self.worker.local().is_empty() {
                break;
            }
        }
    }

    /// Process a single task (if available).
    pub fn step_once(
        &self,
        goals: &GoalStore,
        rules: &RuleStore<C>,
        terms: &mut TermStore,
    ) -> bool {
        use crate::eval::EvalCtx;

        if let Some(unit) = self.worker.find_task() {
            let mut ctx = EvalCtx { goals, rules, terms };
            if let Some(remaining) = self.worker.process_task(unit, &mut ctx) {
                self.worker.local().push(remaining);
            }
            true
        } else {
            false
        }
    }

    /// Process up to N tasks/steps.
    ///
    /// Returns the number of steps actually taken.
    pub fn step_n(
        &self,
        n: usize,
        goals: &GoalStore,
        rules: &RuleStore<C>,
        terms: &mut TermStore,
    ) -> usize {
        let mut count = 0;
        for _ in 0..n {
            if !self.step_once(goals, rules, terms) {
                break;
            }
            count += 1;
        }
        count
    }

    /// Get worker statistics.
    pub fn worker_stats(&self) -> &super::worker::WorkerStats {
        self.worker.stats()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wire::Wire;
    use smallvec::smallvec;

    fn make_identity_nf() -> NF<()> {
        NF::new(smallvec![], Wire::identity(0), smallvec![])
    }

    // ========== SCHEDULER CONFIG TESTS ==========

    #[test]
    fn scheduler_config_default() {
        let config = SchedulerConfig::default();
        assert!(config.num_workers >= 1);
        assert_eq!(config.task_budget, 100);
    }

    #[test]
    fn scheduler_config_custom() {
        let config = SchedulerConfig {
            num_workers: 4,
            task_budget: 50,
        };
        assert_eq!(config.num_workers, 4);
        assert_eq!(config.task_budget, 50);
    }

    // ========== SCHEDULER STATS TESTS ==========

    #[test]
    fn scheduler_stats_new() {
        let stats = SchedulerStats::new();
        assert_eq!(stats.tasks_submitted.load(Ordering::Relaxed), 0);
        assert_eq!(stats.tasks_completed.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn scheduler_stats_record() {
        let stats = SchedulerStats::new();
        stats.record_submitted();
        stats.record_submitted();
        stats.record_completed();
        assert_eq!(stats.tasks_submitted.load(Ordering::Relaxed), 2);
        assert_eq!(stats.tasks_completed.load(Ordering::Relaxed), 1);
    }

    // ========== SCHEDULER CREATION TESTS ==========

    #[test]
    fn scheduler_new() {
        let scheduler: Scheduler<()> = Scheduler::new();
        assert!(!scheduler.is_stopped());
        assert!(scheduler.is_empty());
    }

    #[test]
    fn scheduler_with_config() {
        let config = SchedulerConfig {
            num_workers: 2,
            task_budget: 50,
        };
        let scheduler: Scheduler<()> = Scheduler::with_config(config);
        assert_eq!(scheduler.config().num_workers, 2);
        assert_eq!(scheduler.config().task_budget, 50);
    }

    // ========== TASK SUBMISSION TESTS ==========

    #[test]
    fn submit_returns_unique_ids() {
        let scheduler: Scheduler<()> = Scheduler::new();
        let id1 = scheduler.submit(0, make_identity_nf());
        let id2 = scheduler.submit(0, make_identity_nf());
        let id3 = scheduler.submit(0, make_identity_nf());

        assert_eq!(id1, 0);
        assert_eq!(id2, 1);
        assert_eq!(id3, 2);
    }

    #[test]
    fn submit_increments_stats() {
        let scheduler: Scheduler<()> = Scheduler::new();
        scheduler.submit(0, make_identity_nf());
        scheduler.submit(0, make_identity_nf());

        assert_eq!(scheduler.stats().tasks_submitted.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn submit_adds_to_injector() {
        let scheduler: Scheduler<()> = Scheduler::new();
        assert!(scheduler.is_empty());

        scheduler.submit(0, make_identity_nf());
        assert!(!scheduler.is_empty());
    }

    // ========== STOP TESTS ==========

    #[test]
    fn stop_sets_flag() {
        let scheduler: Scheduler<()> = Scheduler::new();
        assert!(!scheduler.is_stopped());
        scheduler.stop();
        assert!(scheduler.is_stopped());
    }

    // ========== WORKER CREATION TESTS ==========

    #[test]
    fn create_workers() {
        let mut scheduler: Scheduler<()> = Scheduler::with_config(SchedulerConfig {
            num_workers: 3,
            task_budget: 100,
        });

        let workers = scheduler.create_workers();
        assert_eq!(workers.len(), 3);
        assert_eq!(scheduler.num_workers(), 3);
    }

    // ========== SINGLE THREAD EXECUTOR TESTS ==========

    #[test]
    fn executor_run_fail_task() {
        let mut scheduler: Scheduler<()> = Scheduler::with_config(SchedulerConfig {
            num_workers: 1,
            task_budget: 100,
        });

        let mut goals = GoalStore::new();
        let fail_id = goals.fail();

        scheduler.submit(fail_id, make_identity_nf());

        let rules: RuleStore<()> = RuleStore::new();
        let mut terms = TermStore::new();

        let executor = SingleThreadExecutor::new(&mut scheduler);
        executor.run_until_empty(&goals, &rules, &mut terms);

        assert_eq!(executor.worker_stats().tasks_completed.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn executor_run_rule_task() {
        let mut scheduler: Scheduler<()> = Scheduler::with_config(SchedulerConfig {
            num_workers: 1,
            task_budget: 100,
        });

        let mut goals = GoalStore::new();
        let mut rules: RuleStore<()> = RuleStore::new();
        let rule_id = rules.add(make_identity_nf());
        let goal_id = goals.rule(rule_id);

        scheduler.submit(goal_id, make_identity_nf());

        let mut terms = TermStore::new();

        let executor = SingleThreadExecutor::new(&mut scheduler);
        // Use bounded stepping since yielded tasks get re-queued
        executor.step_n(10, &goals, &rules, &mut terms);

        // Rule yields, so it won't be "completed" but "yielded"
        assert!(executor.worker_stats().tasks_yielded.load(Ordering::Relaxed) >= 1);
    }

    #[test]
    fn executor_run_multiple_tasks() {
        let mut scheduler: Scheduler<()> = Scheduler::with_config(SchedulerConfig {
            num_workers: 1,
            task_budget: 100,
        });

        let mut goals = GoalStore::new();
        let fail_id = goals.fail();

        // Submit multiple failing tasks
        for _ in 0..5 {
            scheduler.submit(fail_id, make_identity_nf());
        }

        let rules: RuleStore<()> = RuleStore::new();
        let mut terms = TermStore::new();

        let executor = SingleThreadExecutor::new(&mut scheduler);
        executor.run_until_empty(&goals, &rules, &mut terms);

        assert_eq!(executor.worker_stats().tasks_completed.load(Ordering::Relaxed), 5);
    }

    #[test]
    fn executor_step_once() {
        let mut scheduler: Scheduler<()> = Scheduler::with_config(SchedulerConfig {
            num_workers: 1,
            task_budget: 100,
        });

        let mut goals = GoalStore::new();
        let fail_id = goals.fail();

        scheduler.submit(fail_id, make_identity_nf());
        scheduler.submit(fail_id, make_identity_nf());

        let rules: RuleStore<()> = RuleStore::new();
        let mut terms = TermStore::new();

        let executor = SingleThreadExecutor::new(&mut scheduler);

        // Step once
        let had_work = executor.step_once(&goals, &rules, &mut terms);
        assert!(had_work);
        assert_eq!(executor.worker_stats().tasks_completed.load(Ordering::Relaxed), 1);

        // Step again
        let had_work2 = executor.step_once(&goals, &rules, &mut terms);
        assert!(had_work2);
        assert_eq!(executor.worker_stats().tasks_completed.load(Ordering::Relaxed), 2);

        // No more work
        let had_work3 = executor.step_once(&goals, &rules, &mut terms);
        assert!(!had_work3);
    }

    #[test]
    fn executor_alt_task() {
        let mut scheduler: Scheduler<()> = Scheduler::with_config(SchedulerConfig {
            num_workers: 1,
            task_budget: 1000,
        });

        let mut goals = GoalStore::new();
        let mut rules: RuleStore<()> = RuleStore::new();

        let nf = make_identity_nf();
        let r1 = rules.add(nf.clone());
        let r2 = rules.add(nf);

        let g1 = goals.rule(r1);
        let g2 = goals.rule(r2);
        let alt_id = goals.alt(smallvec![g1, g2]);

        scheduler.submit(alt_id, make_identity_nf());

        let mut terms = TermStore::new();

        let executor = SingleThreadExecutor::new(&mut scheduler);
        // Use bounded stepping since yielded tasks get re-queued
        executor.step_n(20, &goals, &rules, &mut terms);

        // Alt should yield at least once
        assert!(executor.worker_stats().tasks_yielded.load(Ordering::Relaxed) >= 1);
    }

    #[test]
    fn executor_seq_task() {
        let mut scheduler: Scheduler<()> = Scheduler::with_config(SchedulerConfig {
            num_workers: 1,
            task_budget: 1000,
        });

        let mut goals = GoalStore::new();
        let mut rules: RuleStore<()> = RuleStore::new();

        let nf = make_identity_nf();
        let r1 = rules.add(nf.clone());
        let r2 = rules.add(nf);

        let g1 = goals.rule(r1);
        let g2 = goals.rule(r2);
        let seq_id = goals.seq(smallvec![g1, g2]);

        scheduler.submit(seq_id, make_identity_nf());

        let mut terms = TermStore::new();

        let executor = SingleThreadExecutor::new(&mut scheduler);
        // Use bounded stepping since yielded tasks get re-queued
        executor.step_n(20, &goals, &rules, &mut terms);

        // Seq should process through
        assert!(executor.worker_stats().tasks_processed.load(Ordering::Relaxed) >= 1);
    }

    #[test]
    fn executor_respects_stop() {
        let mut scheduler: Scheduler<()> = Scheduler::with_config(SchedulerConfig {
            num_workers: 1,
            task_budget: 100,
        });

        let mut goals = GoalStore::new();
        let fail_id = goals.fail();

        // Submit many tasks
        for _ in 0..10 {
            scheduler.submit(fail_id, make_identity_nf());
        }

        // Stop before running
        scheduler.stop();

        let rules: RuleStore<()> = RuleStore::new();
        let mut terms = TermStore::new();

        let executor = SingleThreadExecutor::new(&mut scheduler);
        executor.run_until_empty(&goals, &rules, &mut terms);

        // Should have stopped without processing all
        assert_eq!(executor.worker_stats().tasks_processed.load(Ordering::Relaxed), 0);
    }

    // ========== AGGREGATE STATS TESTS ==========

    #[test]
    fn aggregate_worker_stats_empty() {
        let scheduler: Scheduler<()> = Scheduler::new();
        let (processed, completed, yielded) = scheduler.aggregate_worker_stats();
        assert_eq!(processed, 0);
        assert_eq!(completed, 0);
        assert_eq!(yielded, 0);
    }

    #[test]
    fn aggregate_worker_stats_after_execution() {
        let mut scheduler: Scheduler<()> = Scheduler::with_config(SchedulerConfig {
            num_workers: 1,
            task_budget: 100,
        });

        let mut goals = GoalStore::new();
        let fail_id = goals.fail();

        scheduler.submit(fail_id, make_identity_nf());
        scheduler.submit(fail_id, make_identity_nf());

        let rules: RuleStore<()> = RuleStore::new();
        let mut terms = TermStore::new();

        let executor = SingleThreadExecutor::new(&mut scheduler);
        executor.run_until_empty(&goals, &rules, &mut terms);

        let (processed, completed, _yielded) = scheduler.aggregate_worker_stats();
        assert_eq!(processed, 2);
        assert_eq!(completed, 2);
    }
}
