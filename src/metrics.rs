//! Evaluation metrics collection for profiling and analysis.
//!
//! This module provides aggregate counters for evaluation operations.
//! When the `tracing` feature is enabled, metrics are collected during evaluation.
//! When disabled, all operations are no-ops with zero overhead.
//!
//! # Usage
//!
//! ```rust,ignore
//! use rwlog::metrics::EvalMetrics;
//!
//! let metrics = EvalMetrics::new();
//! // ... run evaluation ...
//! let report = metrics.report();
//! println!("Steps: {}, Backtracks: {}", report.steps, report.backtracks);
//! ```

#[cfg(feature = "tracing")]
use std::sync::atomic::{AtomicU64, Ordering};

/// Aggregate metrics collected during evaluation.
///
/// All counters use relaxed ordering for minimal overhead.
/// This means values may be slightly stale in multi-threaded contexts,
/// but the final report after evaluation completes will be accurate.
#[cfg(feature = "tracing")]
pub struct EvalMetrics {
    /// Total evaluation steps taken
    pub steps: AtomicU64,
    /// Successful NF compositions
    pub compositions: AtomicU64,
    /// Failed composition attempts (unification failed)
    pub composition_failures: AtomicU64,
    /// Successful NF meets (conjunctions)
    pub meets: AtomicU64,
    /// Failed meet attempts
    pub meet_failures: AtomicU64,
    /// Backtrack operations
    pub backtracks: AtomicU64,
    /// Total unification attempts
    pub unifications: AtomicU64,
    /// Failed unifications
    pub unification_failures: AtomicU64,
    /// Goal state transitions
    pub goal_transitions: AtomicU64,
    /// Tasks spawned
    pub tasks_spawned: AtomicU64,
    /// Tasks that blocked on a relation
    pub tasks_blocked: AtomicU64,
    /// Tasks that completed
    pub tasks_completed: AtomicU64,
    /// Continuation stack pushes
    pub kont_pushes: AtomicU64,
    /// Continuation stack pops
    pub kont_pops: AtomicU64,
    /// Maximum continuation stack depth observed
    pub max_kont_depth: AtomicU64,
    /// Answers yielded
    pub answers_yielded: AtomicU64,
}

#[cfg(feature = "tracing")]
impl EvalMetrics {
    /// Create a new metrics collector with all counters at zero.
    pub fn new() -> Self {
        Self {
            steps: AtomicU64::new(0),
            compositions: AtomicU64::new(0),
            composition_failures: AtomicU64::new(0),
            meets: AtomicU64::new(0),
            meet_failures: AtomicU64::new(0),
            backtracks: AtomicU64::new(0),
            unifications: AtomicU64::new(0),
            unification_failures: AtomicU64::new(0),
            goal_transitions: AtomicU64::new(0),
            tasks_spawned: AtomicU64::new(0),
            tasks_blocked: AtomicU64::new(0),
            tasks_completed: AtomicU64::new(0),
            kont_pushes: AtomicU64::new(0),
            kont_pops: AtomicU64::new(0),
            max_kont_depth: AtomicU64::new(0),
            answers_yielded: AtomicU64::new(0),
        }
    }

    /// Record an evaluation step.
    #[inline]
    pub fn record_step(&self) {
        self.steps.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a successful composition.
    #[inline]
    pub fn record_composition(&self) {
        self.compositions.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a failed composition attempt.
    #[inline]
    pub fn record_composition_failure(&self) {
        self.composition_failures.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a successful meet operation.
    #[inline]
    pub fn record_meet(&self) {
        self.meets.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a failed meet attempt.
    #[inline]
    pub fn record_meet_failure(&self) {
        self.meet_failures.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a backtrack operation.
    #[inline]
    pub fn record_backtrack(&self) {
        self.backtracks.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a unification attempt (success).
    #[inline]
    pub fn record_unification(&self) {
        self.unifications.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a failed unification.
    #[inline]
    pub fn record_unification_failure(&self) {
        self.unification_failures.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a goal state transition.
    #[inline]
    pub fn record_goal_transition(&self) {
        self.goal_transitions.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a task spawn.
    #[inline]
    pub fn record_task_spawned(&self) {
        self.tasks_spawned.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a task block.
    #[inline]
    pub fn record_task_blocked(&self) {
        self.tasks_blocked.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a task completion.
    #[inline]
    pub fn record_task_completed(&self) {
        self.tasks_completed.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a continuation push with current depth.
    #[inline]
    pub fn record_kont_push(&self, new_depth: u64) {
        self.kont_pushes.fetch_add(1, Ordering::Relaxed);
        self.update_max_kont_depth(new_depth);
    }

    /// Record a continuation pop.
    #[inline]
    pub fn record_kont_pop(&self) {
        self.kont_pops.fetch_add(1, Ordering::Relaxed);
    }

    /// Update the maximum continuation depth if the new depth is higher.
    #[inline]
    pub fn update_max_kont_depth(&self, depth: u64) {
        let mut current = self.max_kont_depth.load(Ordering::Relaxed);
        while depth > current {
            match self.max_kont_depth.compare_exchange_weak(
                current,
                depth,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(c) => current = c,
            }
        }
    }

    /// Record an answer being yielded.
    #[inline]
    pub fn record_answer_yielded(&self) {
        self.answers_yielded.fetch_add(1, Ordering::Relaxed);
    }

    /// Generate a snapshot report of all metrics.
    pub fn report(&self) -> MetricsReport {
        MetricsReport {
            steps: self.steps.load(Ordering::Relaxed),
            compositions: self.compositions.load(Ordering::Relaxed),
            composition_failures: self.composition_failures.load(Ordering::Relaxed),
            meets: self.meets.load(Ordering::Relaxed),
            meet_failures: self.meet_failures.load(Ordering::Relaxed),
            backtracks: self.backtracks.load(Ordering::Relaxed),
            unifications: self.unifications.load(Ordering::Relaxed),
            unification_failures: self.unification_failures.load(Ordering::Relaxed),
            goal_transitions: self.goal_transitions.load(Ordering::Relaxed),
            tasks_spawned: self.tasks_spawned.load(Ordering::Relaxed),
            tasks_blocked: self.tasks_blocked.load(Ordering::Relaxed),
            tasks_completed: self.tasks_completed.load(Ordering::Relaxed),
            kont_pushes: self.kont_pushes.load(Ordering::Relaxed),
            kont_pops: self.kont_pops.load(Ordering::Relaxed),
            max_kont_depth: self.max_kont_depth.load(Ordering::Relaxed),
            answers_yielded: self.answers_yielded.load(Ordering::Relaxed),
        }
    }

    /// Reset all metrics to zero.
    pub fn reset(&self) {
        self.steps.store(0, Ordering::Relaxed);
        self.compositions.store(0, Ordering::Relaxed);
        self.composition_failures.store(0, Ordering::Relaxed);
        self.meets.store(0, Ordering::Relaxed);
        self.meet_failures.store(0, Ordering::Relaxed);
        self.backtracks.store(0, Ordering::Relaxed);
        self.unifications.store(0, Ordering::Relaxed);
        self.unification_failures.store(0, Ordering::Relaxed);
        self.goal_transitions.store(0, Ordering::Relaxed);
        self.tasks_spawned.store(0, Ordering::Relaxed);
        self.tasks_blocked.store(0, Ordering::Relaxed);
        self.tasks_completed.store(0, Ordering::Relaxed);
        self.kont_pushes.store(0, Ordering::Relaxed);
        self.kont_pops.store(0, Ordering::Relaxed);
        self.max_kont_depth.store(0, Ordering::Relaxed);
        self.answers_yielded.store(0, Ordering::Relaxed);
    }
}

#[cfg(feature = "tracing")]
impl Default for EvalMetrics {
    fn default() -> Self {
        Self::new()
    }
}

/// Snapshot of metrics at a point in time.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MetricsReport {
    pub steps: u64,
    pub compositions: u64,
    pub composition_failures: u64,
    pub meets: u64,
    pub meet_failures: u64,
    pub backtracks: u64,
    pub unifications: u64,
    pub unification_failures: u64,
    pub goal_transitions: u64,
    pub tasks_spawned: u64,
    pub tasks_blocked: u64,
    pub tasks_completed: u64,
    pub kont_pushes: u64,
    pub kont_pops: u64,
    pub max_kont_depth: u64,
    pub answers_yielded: u64,
}

impl MetricsReport {
    /// Calculate composition success rate.
    pub fn composition_success_rate(&self) -> f64 {
        let total = self.compositions + self.composition_failures;
        if total == 0 {
            1.0
        } else {
            self.compositions as f64 / total as f64
        }
    }

    /// Calculate unification success rate.
    pub fn unification_success_rate(&self) -> f64 {
        let total = self.unifications + self.unification_failures;
        if total == 0 {
            1.0
        } else {
            self.unifications as f64 / total as f64
        }
    }

    /// Calculate average continuation depth (rough estimate).
    pub fn avg_kont_depth(&self) -> f64 {
        if self.kont_pushes == 0 {
            0.0
        } else {
            // This is a rough estimate - actual average would need per-step tracking
            self.max_kont_depth as f64 / 2.0
        }
    }
}

impl std::fmt::Display for MetricsReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "=== Evaluation Metrics ===")?;
        writeln!(f, "Steps:              {}", self.steps)?;
        writeln!(
            f,
            "Compositions:       {} ({} failures, {:.1}% success)",
            self.compositions,
            self.composition_failures,
            self.composition_success_rate() * 100.0
        )?;
        writeln!(
            f,
            "Meets:              {} ({} failures)",
            self.meets, self.meet_failures
        )?;
        writeln!(f, "Backtracks:         {}", self.backtracks)?;
        writeln!(
            f,
            "Unifications:       {} ({} failures, {:.1}% success)",
            self.unifications,
            self.unification_failures,
            self.unification_success_rate() * 100.0
        )?;
        writeln!(f, "Goal transitions:   {}", self.goal_transitions)?;
        writeln!(
            f,
            "Tasks:              {} spawned, {} blocked, {} completed",
            self.tasks_spawned, self.tasks_blocked, self.tasks_completed
        )?;
        writeln!(
            f,
            "Continuations:      {} pushes, {} pops, max depth {}",
            self.kont_pushes, self.kont_pops, self.max_kont_depth
        )?;
        writeln!(f, "Answers yielded:    {}", self.answers_yielded)?;
        Ok(())
    }
}

// No-op implementation when tracing is disabled
#[cfg(not(feature = "tracing"))]
pub struct EvalMetrics;

#[cfg(not(feature = "tracing"))]
impl EvalMetrics {
    #[inline]
    pub fn new() -> Self {
        EvalMetrics
    }
    #[inline]
    pub fn record_step(&self) {}
    #[inline]
    pub fn record_composition(&self) {}
    #[inline]
    pub fn record_composition_failure(&self) {}
    #[inline]
    pub fn record_meet(&self) {}
    #[inline]
    pub fn record_meet_failure(&self) {}
    #[inline]
    pub fn record_backtrack(&self) {}
    #[inline]
    pub fn record_unification(&self) {}
    #[inline]
    pub fn record_unification_failure(&self) {}
    #[inline]
    pub fn record_goal_transition(&self) {}
    #[inline]
    pub fn record_task_spawned(&self) {}
    #[inline]
    pub fn record_task_blocked(&self) {}
    #[inline]
    pub fn record_task_completed(&self) {}
    #[inline]
    pub fn record_kont_push(&self, _new_depth: u64) {}
    #[inline]
    pub fn record_kont_pop(&self) {}
    #[inline]
    pub fn update_max_kont_depth(&self, _depth: u64) {}
    #[inline]
    pub fn record_answer_yielded(&self) {}
    #[inline]
    pub fn report(&self) -> MetricsReport {
        MetricsReport::default()
    }
    #[inline]
    pub fn reset(&self) {}
}

#[cfg(not(feature = "tracing"))]
impl Default for EvalMetrics {
    fn default() -> Self {
        Self::new()
    }
}


#[cfg(test)]
mod tests;
