use rwlog::perf_corpus::{
    csv_escape, csv_escape_opt, environment_fingerprint, prepare_case, run_prepared_with_stats,
    select_cases, stats_median_u64, EnvironmentFingerprint,
};
use serde::Serialize;
use std::alloc::{GlobalAlloc, Layout};
use std::sync::atomic::{AtomicU64, Ordering};

struct CountingAlloc;

static INNER: mimalloc::MiMalloc = mimalloc::MiMalloc;

static ALLOC_CALLS: AtomicU64 = AtomicU64::new(0);
static DEALLOC_CALLS: AtomicU64 = AtomicU64::new(0);
static REALLOC_CALLS: AtomicU64 = AtomicU64::new(0);
static ALLOC_BYTES: AtomicU64 = AtomicU64::new(0);
static DEALLOC_BYTES: AtomicU64 = AtomicU64::new(0);
static REALLOC_IN_BYTES: AtomicU64 = AtomicU64::new(0);
static REALLOC_OUT_BYTES: AtomicU64 = AtomicU64::new(0);

#[global_allocator]
static GLOBAL: CountingAlloc = CountingAlloc;

unsafe impl GlobalAlloc for CountingAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
        ALLOC_BYTES.fetch_add(layout.size() as u64, Ordering::Relaxed);
        INNER.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        DEALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
        DEALLOC_BYTES.fetch_add(layout.size() as u64, Ordering::Relaxed);
        INNER.dealloc(ptr, layout)
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        REALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
        REALLOC_IN_BYTES.fetch_add(layout.size() as u64, Ordering::Relaxed);
        REALLOC_OUT_BYTES.fetch_add(new_size as u64, Ordering::Relaxed);
        INNER.realloc(ptr, layout, new_size)
    }
}

#[derive(Clone, Copy, Debug)]
struct Snapshot {
    alloc_calls: u64,
    dealloc_calls: u64,
    realloc_calls: u64,
    alloc_bytes: u64,
    dealloc_bytes: u64,
    realloc_in_bytes: u64,
    realloc_out_bytes: u64,
}

impl Snapshot {
    fn now() -> Self {
        Self {
            alloc_calls: ALLOC_CALLS.load(Ordering::Relaxed),
            dealloc_calls: DEALLOC_CALLS.load(Ordering::Relaxed),
            realloc_calls: REALLOC_CALLS.load(Ordering::Relaxed),
            alloc_bytes: ALLOC_BYTES.load(Ordering::Relaxed),
            dealloc_bytes: DEALLOC_BYTES.load(Ordering::Relaxed),
            realloc_in_bytes: REALLOC_IN_BYTES.load(Ordering::Relaxed),
            realloc_out_bytes: REALLOC_OUT_BYTES.load(Ordering::Relaxed),
        }
    }

    fn delta(self, earlier: Snapshot) -> Self {
        Self {
            alloc_calls: self.alloc_calls - earlier.alloc_calls,
            dealloc_calls: self.dealloc_calls - earlier.dealloc_calls,
            realloc_calls: self.realloc_calls - earlier.realloc_calls,
            alloc_bytes: self.alloc_bytes - earlier.alloc_bytes,
            dealloc_bytes: self.dealloc_bytes - earlier.dealloc_bytes,
            realloc_in_bytes: self.realloc_in_bytes - earlier.realloc_in_bytes,
            realloc_out_bytes: self.realloc_out_bytes - earlier.realloc_out_bytes,
        }
    }
}

#[derive(Debug, Serialize)]
struct AllocRow {
    id: String,
    tier: String,
    category: String,
    mode: String,
    answers: usize,
    iters: usize,
    parse_alloc_calls: u64,
    parse_alloc_bytes: u64,
    exec_alloc_calls: u64,
    exec_alloc_bytes: u64,
    parse_realloc_calls: u64,
    exec_realloc_calls: u64,
    exec_engine_steps: u64,
    exec_engine_emits: u64,
    exec_engine_continues: u64,
    exec_compose_attempts: u64,
    exec_compose_successes: u64,
    exec_meet_attempts: u64,
    exec_meet_successes: u64,
}

#[derive(Debug, Serialize)]
struct AllocReport {
    environment: EnvironmentFingerprint,
    selected_cases: usize,
    iters: usize,
    rows: Vec<AllocRow>,
}

fn parse_args() -> (Option<String>, usize, bool, bool) {
    let mut id_filter = None;
    let mut iters = 5usize;
    let mut json = false;
    let mut csv = false;
    let mut args = std::env::args().skip(1).peekable();
    while let Some(arg) = args.next() {
        if arg == "--id" {
            id_filter = Some(args.next().expect("--id requires value"));
            continue;
        }
        if arg == "--iters" {
            iters = args
                .next()
                .expect("--iters requires value")
                .parse()
                .expect("--iters must be integer");
            continue;
        }
        if arg == "--json" {
            json = true;
            continue;
        }
        if arg == "--csv" {
            csv = true;
            continue;
        }
        panic!("unknown argument: {arg}");
    }
    assert!(iters > 0, "--iters must be > 0");
    if json && csv {
        panic!("--json and --csv are mutually exclusive");
    }
    (id_filter, iters, json, csv)
}

fn main() {
    let (id_filter, iters, json, csv) = parse_args();
    let cases = select_cases(id_filter);
    let env = environment_fingerprint();

    if !json && !csv {
        println!(
            "id | mode | answers | parse_alloc_calls | parse_alloc_bytes | exec_alloc_calls | exec_alloc_bytes | parse_realloc_calls | exec_realloc_calls | exec_steps | exec_compose | exec_meet"
        );
    }
    let mut rows = Vec::new();

    for case in &cases {
        let mut parse_calls = Vec::with_capacity(iters);
        let mut parse_bytes = Vec::with_capacity(iters);
        let mut parse_realloc = Vec::with_capacity(iters);
        let mut exec_calls = Vec::with_capacity(iters);
        let mut exec_bytes = Vec::with_capacity(iters);
        let mut exec_realloc = Vec::with_capacity(iters);
        let mut exec_steps = Vec::with_capacity(iters);
        let mut exec_emits = Vec::with_capacity(iters);
        let mut exec_continues = Vec::with_capacity(iters);
        let mut exec_compose_attempts = Vec::with_capacity(iters);
        let mut exec_compose_successes = Vec::with_capacity(iters);
        let mut exec_meet_attempts = Vec::with_capacity(iters);
        let mut exec_meet_successes = Vec::with_capacity(iters);
        let mut answers = 0usize;

        for _ in 0..iters {
            let s0 = Snapshot::now();
            let prepared = prepare_case(case);
            let s1 = Snapshot::now();
            let stats = run_prepared_with_stats(case, prepared);
            answers = stats.answers;
            let s2 = Snapshot::now();

            let parse = s1.delta(s0);
            let exec = s2.delta(s1);
            parse_calls.push(parse.alloc_calls);
            parse_bytes.push(parse.alloc_bytes + parse.realloc_out_bytes);
            parse_realloc.push(parse.realloc_calls);
            exec_calls.push(exec.alloc_calls);
            exec_bytes.push(exec.alloc_bytes + exec.realloc_out_bytes);
            exec_realloc.push(exec.realloc_calls);
            exec_steps.push(stats.counters.engine_steps);
            exec_emits.push(stats.counters.engine_emits);
            exec_continues.push(stats.counters.engine_continues);
            exec_compose_attempts.push(stats.counters.compose_attempts);
            exec_compose_successes.push(stats.counters.compose_successes);
            exec_meet_attempts.push(stats.counters.meet_attempts);
            exec_meet_successes.push(stats.counters.meet_successes);
        }

        let parse_calls_m = stats_median_u64(&mut parse_calls);
        let parse_bytes_m = stats_median_u64(&mut parse_bytes);
        let parse_realloc_m = stats_median_u64(&mut parse_realloc);
        let exec_calls_m = stats_median_u64(&mut exec_calls);
        let exec_bytes_m = stats_median_u64(&mut exec_bytes);
        let exec_realloc_m = stats_median_u64(&mut exec_realloc);
        let exec_steps_m = stats_median_u64(&mut exec_steps);
        let exec_emits_m = stats_median_u64(&mut exec_emits);
        let exec_continues_m = stats_median_u64(&mut exec_continues);
        let exec_compose_attempts_m = stats_median_u64(&mut exec_compose_attempts);
        let exec_compose_successes_m = stats_median_u64(&mut exec_compose_successes);
        let exec_meet_attempts_m = stats_median_u64(&mut exec_meet_attempts);
        let exec_meet_successes_m = stats_median_u64(&mut exec_meet_successes);

        let row = AllocRow {
            id: case.id.clone(),
            tier: case.tier.as_str().to_string(),
            category: case.category.as_str().to_string(),
            mode: case.mode.as_str().to_string(),
            answers,
            iters,
            parse_alloc_calls: parse_calls_m,
            parse_alloc_bytes: parse_bytes_m,
            exec_alloc_calls: exec_calls_m,
            exec_alloc_bytes: exec_bytes_m,
            parse_realloc_calls: parse_realloc_m,
            exec_realloc_calls: exec_realloc_m,
            exec_engine_steps: exec_steps_m,
            exec_engine_emits: exec_emits_m,
            exec_engine_continues: exec_continues_m,
            exec_compose_attempts: exec_compose_attempts_m,
            exec_compose_successes: exec_compose_successes_m,
            exec_meet_attempts: exec_meet_attempts_m,
            exec_meet_successes: exec_meet_successes_m,
        };

        if !json && !csv {
            println!(
                "{} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {}",
                row.id,
                row.mode,
                row.answers,
                row.parse_alloc_calls,
                row.parse_alloc_bytes,
                row.exec_alloc_calls,
                row.exec_alloc_bytes,
                row.parse_realloc_calls,
                row.exec_realloc_calls,
                row.exec_engine_steps,
                row.exec_compose_attempts,
                row.exec_meet_attempts
            );
        }
        rows.push(row);
    }

    if json {
        let report = AllocReport {
            environment: env,
            selected_cases: rows.len(),
            iters,
            rows,
        };
        println!(
            "{}",
            serde_json::to_string_pretty(&report).expect("serialize alloc report")
        );
        return;
    }
    if csv {
        println!(
            "id,tier,category,mode,answers,iters,parse_alloc_calls,parse_alloc_bytes,exec_alloc_calls,exec_alloc_bytes,parse_realloc_calls,exec_realloc_calls,exec_engine_steps,exec_engine_emits,exec_engine_continues,exec_compose_attempts,exec_compose_successes,exec_meet_attempts,exec_meet_successes,env_os,env_arch,env_cpu,env_rustc,env_rustflags,env_timestamp_unix_s,env_git_sha,env_run_id"
        );
        for row in rows {
            println!(
                "{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}",
                csv_escape(&row.id),
                csv_escape(&row.tier),
                csv_escape(&row.category),
                csv_escape(&row.mode),
                row.answers,
                row.iters,
                row.parse_alloc_calls,
                row.parse_alloc_bytes,
                row.exec_alloc_calls,
                row.exec_alloc_bytes,
                row.parse_realloc_calls,
                row.exec_realloc_calls,
                row.exec_engine_steps,
                row.exec_engine_emits,
                row.exec_engine_continues,
                row.exec_compose_attempts,
                row.exec_compose_successes,
                row.exec_meet_attempts,
                row.exec_meet_successes,
                csv_escape(&env.os),
                csv_escape(&env.arch),
                csv_escape_opt(env.cpu_model.as_deref()),
                csv_escape(&env.rustc_version),
                csv_escape_opt(env.rustflags.as_deref()),
                env.timestamp_unix_s,
                csv_escape_opt(env.git_sha.as_deref()),
                csv_escape_opt(env.run_id.as_deref()),
            );
        }
    }
}
