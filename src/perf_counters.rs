use std::cell::Cell;
use std::collections::HashSet;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

/// Histogram of (call_count, num_pairs_with_that_count), sorted by call_count.
pub type FrequencyHistogram = Vec<(u32, usize)>;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PerfCountersSnapshot {
    pub engine_steps: u64,
    pub engine_emits: u64,
    pub engine_continues: u64,
    pub engine_exhausted: u64,
    pub compose_attempts: u64,
    pub compose_successes: u64,
    pub compose_failures: u64,
    pub meet_attempts: u64,
    pub meet_successes: u64,
    pub meet_failures: u64,
    pub compose_unique_pairs: u64,
    pub meet_unique_pairs: u64,
    pub fixpoint_producer_starts: u64,
    pub fixpoint_verification_starts: u64,
    pub fixpoint_verification_steps: u64,
    pub or_spine_walks: u64,
    pub or_spine_total_siblings: u64,
    pub or_spine_max_siblings: u64,
}

thread_local! {
    static ENABLED: Cell<bool> = const { Cell::new(false) };
}
static ENGINE_STEPS: AtomicU64 = AtomicU64::new(0);
static ENGINE_EMITS: AtomicU64 = AtomicU64::new(0);
static ENGINE_CONTINUES: AtomicU64 = AtomicU64::new(0);
static ENGINE_EXHAUSTED: AtomicU64 = AtomicU64::new(0);
static COMPOSE_ATTEMPTS: AtomicU64 = AtomicU64::new(0);
static COMPOSE_SUCCESSES: AtomicU64 = AtomicU64::new(0);
static COMPOSE_FAILURES: AtomicU64 = AtomicU64::new(0);
static MEET_ATTEMPTS: AtomicU64 = AtomicU64::new(0);
static MEET_SUCCESSES: AtomicU64 = AtomicU64::new(0);
static MEET_FAILURES: AtomicU64 = AtomicU64::new(0);
static FIXPOINT_PRODUCER_STARTS: AtomicU64 = AtomicU64::new(0);
static FIXPOINT_VERIFICATION_STARTS: AtomicU64 = AtomicU64::new(0);
static FIXPOINT_VERIFICATION_STEPS: AtomicU64 = AtomicU64::new(0);
static OR_SPINE_WALKS: AtomicU64 = AtomicU64::new(0);
static OR_SPINE_TOTAL_SIBLINGS: AtomicU64 = AtomicU64::new(0);
static OR_SPINE_MAX_SIBLINGS: AtomicU64 = AtomicU64::new(0);
static NORMALIZE_TOTAL: AtomicU64 = AtomicU64::new(0);
static NORMALIZE_UNIQUE: Mutex<Option<HashSet<u64>>> = Mutex::new(None);

static COMPOSE_PAIR_SET: Mutex<Option<HashSet<u64>>> = Mutex::new(None);
static MEET_PAIR_SET: Mutex<Option<HashSet<u64>>> = Mutex::new(None);
static COMPOSE_PAIR_FREQ: Mutex<Option<std::collections::HashMap<u64, u32>>> = Mutex::new(None);
static MEET_PAIR_FREQ: Mutex<Option<std::collections::HashMap<u64, u32>>> = Mutex::new(None);
static CAPTURE_LOCK: Mutex<()> = Mutex::new(());

#[inline]
fn enabled() -> bool {
    ENABLED.with(|e| e.get())
}

#[inline]
fn bump(counter: &AtomicU64) {
    counter.fetch_add(1, Ordering::Relaxed);
}

pub fn is_enabled() -> bool {
    enabled()
}

pub fn set_enabled(on: bool) {
    ENABLED.with(|e| e.set(on));
}

pub fn reset() {
    ENGINE_STEPS.store(0, Ordering::Relaxed);
    ENGINE_EMITS.store(0, Ordering::Relaxed);
    ENGINE_CONTINUES.store(0, Ordering::Relaxed);
    ENGINE_EXHAUSTED.store(0, Ordering::Relaxed);
    COMPOSE_ATTEMPTS.store(0, Ordering::Relaxed);
    COMPOSE_SUCCESSES.store(0, Ordering::Relaxed);
    COMPOSE_FAILURES.store(0, Ordering::Relaxed);
    MEET_ATTEMPTS.store(0, Ordering::Relaxed);
    MEET_SUCCESSES.store(0, Ordering::Relaxed);
    MEET_FAILURES.store(0, Ordering::Relaxed);
    FIXPOINT_PRODUCER_STARTS.store(0, Ordering::Relaxed);
    FIXPOINT_VERIFICATION_STARTS.store(0, Ordering::Relaxed);
    FIXPOINT_VERIFICATION_STEPS.store(0, Ordering::Relaxed);
    OR_SPINE_WALKS.store(0, Ordering::Relaxed);
    OR_SPINE_TOTAL_SIBLINGS.store(0, Ordering::Relaxed);
    OR_SPINE_MAX_SIBLINGS.store(0, Ordering::Relaxed);
    NORMALIZE_TOTAL.store(0, Ordering::Relaxed);
    *NORMALIZE_UNIQUE.lock().unwrap() = Some(HashSet::new());
    *COMPOSE_PAIR_SET.lock().unwrap() = Some(HashSet::new());
    *MEET_PAIR_SET.lock().unwrap() = Some(HashSet::new());
    *COMPOSE_PAIR_FREQ.lock().unwrap() = Some(std::collections::HashMap::new());
    *MEET_PAIR_FREQ.lock().unwrap() = Some(std::collections::HashMap::new());
}

pub fn snapshot() -> PerfCountersSnapshot {
    let compose_unique = COMPOSE_PAIR_SET
        .lock()
        .unwrap()
        .as_ref()
        .map_or(0, |s| s.len() as u64);
    let meet_unique = MEET_PAIR_SET
        .lock()
        .unwrap()
        .as_ref()
        .map_or(0, |s| s.len() as u64);
    PerfCountersSnapshot {
        engine_steps: ENGINE_STEPS.load(Ordering::Relaxed),
        engine_emits: ENGINE_EMITS.load(Ordering::Relaxed),
        engine_continues: ENGINE_CONTINUES.load(Ordering::Relaxed),
        engine_exhausted: ENGINE_EXHAUSTED.load(Ordering::Relaxed),
        compose_attempts: COMPOSE_ATTEMPTS.load(Ordering::Relaxed),
        compose_successes: COMPOSE_SUCCESSES.load(Ordering::Relaxed),
        compose_failures: COMPOSE_FAILURES.load(Ordering::Relaxed),
        meet_attempts: MEET_ATTEMPTS.load(Ordering::Relaxed),
        meet_successes: MEET_SUCCESSES.load(Ordering::Relaxed),
        meet_failures: MEET_FAILURES.load(Ordering::Relaxed),
        compose_unique_pairs: compose_unique,
        meet_unique_pairs: meet_unique,
        fixpoint_producer_starts: FIXPOINT_PRODUCER_STARTS.load(Ordering::Relaxed),
        fixpoint_verification_starts: FIXPOINT_VERIFICATION_STARTS.load(Ordering::Relaxed),
        fixpoint_verification_steps: FIXPOINT_VERIFICATION_STEPS.load(Ordering::Relaxed),
        or_spine_walks: OR_SPINE_WALKS.load(Ordering::Relaxed),
        or_spine_total_siblings: OR_SPINE_TOTAL_SIBLINGS.load(Ordering::Relaxed),
        or_spine_max_siblings: OR_SPINE_MAX_SIBLINGS.load(Ordering::Relaxed),
    }
}

pub fn capture<T>(f: impl FnOnce() -> T) -> (T, PerfCountersSnapshot) {
    struct RestoreEnabled(bool);
    impl Drop for RestoreEnabled {
        fn drop(&mut self) {
            set_enabled(self.0);
        }
    }

    let _lock = CAPTURE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let previous = is_enabled();
    set_enabled(true);
    reset();
    let _restore = RestoreEnabled(previous);
    let out = f();
    let snap = snapshot();
    (out, snap)
}

pub fn record_engine_step() {
    if enabled() {
        bump(&ENGINE_STEPS);
    }
}

pub fn record_engine_emit() {
    if enabled() {
        bump(&ENGINE_EMITS);
    }
}

pub fn record_engine_continue() {
    if enabled() {
        bump(&ENGINE_CONTINUES);
    }
}

pub fn record_engine_exhausted() {
    if enabled() {
        bump(&ENGINE_EXHAUSTED);
    }
}

/// Returns frequency histograms: (compose_freq_distribution, meet_freq_distribution)
/// Each is a Vec<(call_count, num_pairs_with_that_count)> sorted by call_count.
pub fn pair_frequency_histograms() -> (FrequencyHistogram, FrequencyHistogram) {
    fn histogram(map: &Mutex<Option<std::collections::HashMap<u64, u32>>>) -> FrequencyHistogram {
        let guard = map.lock().unwrap();
        let Some(freq) = guard.as_ref() else {
            return vec![];
        };
        let mut counts: std::collections::BTreeMap<u32, usize> = std::collections::BTreeMap::new();
        for &count in freq.values() {
            *counts.entry(count).or_insert(0) += 1;
        }
        counts.into_iter().collect()
    }
    (histogram(&COMPOSE_PAIR_FREQ), histogram(&MEET_PAIR_FREQ))
}

pub fn record_compose_result(success: bool) {
    if enabled() {
        bump(&COMPOSE_ATTEMPTS);
        if success {
            bump(&COMPOSE_SUCCESSES);
        } else {
            bump(&COMPOSE_FAILURES);
        }
    }
}

pub fn record_compose_pair_hash(hash: u64) {
    if enabled() {
        if let Ok(mut guard) = COMPOSE_PAIR_SET.lock() {
            if let Some(set) = guard.as_mut() {
                set.insert(hash);
            }
        }
        if let Ok(mut guard) = COMPOSE_PAIR_FREQ.lock() {
            if let Some(map) = guard.as_mut() {
                *map.entry(hash).or_insert(0) += 1;
            }
        }
    }
}

pub fn record_meet_result(success: bool) {
    if enabled() {
        bump(&MEET_ATTEMPTS);
        if success {
            bump(&MEET_SUCCESSES);
        } else {
            bump(&MEET_FAILURES);
        }
    }
}

pub fn record_meet_pair_hash(hash: u64) {
    if enabled() {
        if let Ok(mut guard) = MEET_PAIR_SET.lock() {
            if let Some(set) = guard.as_mut() {
                set.insert(hash);
            }
        }
        if let Ok(mut guard) = MEET_PAIR_FREQ.lock() {
            if let Some(map) = guard.as_mut() {
                *map.entry(hash).or_insert(0) += 1;
            }
        }
    }
}

/// Record that a table's producer started its first iteration.
pub fn record_fixpoint_producer_start() {
    if enabled() {
        bump(&FIXPOINT_PRODUCER_STARTS);
    }
}

/// Record that a table's producer started a verification (re-run) iteration.
pub fn record_fixpoint_verification_start() {
    if enabled() {
        bump(&FIXPOINT_VERIFICATION_STARTS);
    }
}

/// Record a single step taken during a verification iteration.
pub fn record_fixpoint_verification_step() {
    if enabled() {
        bump(&FIXPOINT_VERIFICATION_STEPS);
    }
}

/// Record a normalize_owned call with a hash of the pre-normalization ChrState.
pub fn record_normalize_call(state_hash: u64) {
    if enabled() {
        bump(&NORMALIZE_TOTAL);
        if let Ok(mut guard) = NORMALIZE_UNIQUE.lock() {
            if let Some(set) = guard.as_mut() {
                set.insert(state_hash);
            }
        }
    }
}

/// Get the normalize duplication stats: (total_calls, unique_states).
pub fn normalize_stats() -> (u64, u64) {
    let total = NORMALIZE_TOTAL.load(Ordering::Relaxed);
    let unique = NORMALIZE_UNIQUE
        .lock()
        .unwrap()
        .as_ref()
        .map_or(0, |s| s.len() as u64);
    (total, unique)
}

/// Record an Or spine walk with the given number of siblings collected.
pub fn record_or_spine_walk(siblings_count: u64) {
    if enabled() {
        bump(&OR_SPINE_WALKS);
        OR_SPINE_TOTAL_SIBLINGS.fetch_add(siblings_count, Ordering::Relaxed);
        OR_SPINE_MAX_SIBLINGS.fetch_max(siblings_count, Ordering::Relaxed);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Engine;
    use crate::parser::Parser;

    /// Separate mutex for test serialization. Must NOT be CAPTURE_LOCK since
    /// capture() acquires CAPTURE_LOCK internally, and std::sync::Mutex is
    /// not reentrant. Lock ordering: TEST_SERIALIZE (outer) → CAPTURE_LOCK
    /// (inner) — no circular dependency.
    static TEST_SERIALIZE: Mutex<()> = Mutex::new(());

    fn test_lock() -> std::sync::MutexGuard<'static, ()> {
        TEST_SERIALIZE.lock().unwrap_or_else(|e| e.into_inner())
    }

    #[test]
    fn disabled_counters_stay_zero() {
        let _guard = test_lock();
        set_enabled(false);
        reset();
        record_engine_step();
        record_engine_emit();
        record_engine_continue();
        record_engine_exhausted();
        record_compose_result(true);
        record_compose_result(false);
        record_meet_result(true);
        record_meet_result(false);
        assert_eq!(snapshot(), PerfCountersSnapshot::default());
    }

    #[test]
    fn capture_restores_previous_state() {
        let _guard = test_lock();
        set_enabled(false);
        let (value, snap) = capture(|| {
            record_engine_step();
            7usize
        });
        assert_eq!(value, 7);
        assert_eq!(snap.engine_steps, 1);
        assert!(!is_enabled());
    }

    #[test]
    fn compose_path_records_steps_and_compose_attempts() {
        let _guard = test_lock();
        let mut parser = Parser::new();
        let rel = parser
            .parse_rel_body("[a -> b ; b -> c]")
            .expect("parse compose query");
        let terms = parser.take_terms();

        let (answers, snap) = capture(|| {
            let mut engine: Engine<()> = Engine::new(rel, terms);
            engine.count_answers()
        });

        assert_eq!(answers, 1);
        assert!(snap.compose_attempts > 0);
    }

    #[test]
    fn meet_path_records_meet_attempts() {
        let _guard = test_lock();
        let mut parser = Parser::new();
        let rel = parser
            .parse_rel_body("[a -> a & a -> a]")
            .expect("parse meet query");
        let terms = parser.take_terms();

        let (answers, snap) = capture(|| {
            let mut engine: Engine<()> = Engine::new(rel, terms);
            engine.count_answers()
        });

        assert_eq!(answers, 1);
        assert!(snap.meet_attempts > 0);
    }
}
