use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

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
}

static ENABLED: AtomicBool = AtomicBool::new(false);
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

#[inline]
fn enabled() -> bool {
    ENABLED.load(Ordering::Relaxed)
}

#[inline]
fn bump(counter: &AtomicU64) {
    counter.fetch_add(1, Ordering::Relaxed);
}

pub fn is_enabled() -> bool {
    enabled()
}

pub fn set_enabled(on: bool) {
    ENABLED.store(on, Ordering::Relaxed);
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
}

pub fn snapshot() -> PerfCountersSnapshot {
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
    }
}

pub fn capture<T>(f: impl FnOnce() -> T) -> (T, PerfCountersSnapshot) {
    struct RestoreEnabled(bool);
    impl Drop for RestoreEnabled {
        fn drop(&mut self) {
            set_enabled(self.0);
        }
    }

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Engine;
    use crate::parser::Parser;
    use std::sync::{Mutex, OnceLock};

    fn test_lock() -> std::sync::MutexGuard<'static, ()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
            .lock()
            .expect("lock perf_counters test mutex")
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
