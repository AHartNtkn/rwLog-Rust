#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use rwlog::perf_corpus::{
    apply_filters, environment_fingerprint, load_cases, prepare_case, run_prepared_with_stats,
    sort_cases, CorpusCase, CorpusFilters, EnvironmentFingerprint,
};
use serde::Serialize;
use std::time::Instant;

#[derive(Clone, Copy, Debug)]
enum Phase {
    Parse,
    Execute,
    EndToEnd,
}

impl Phase {
    fn from_arg(s: &str) -> Self {
        match s {
            "parse" => Phase::Parse,
            "execute" => Phase::Execute,
            "end_to_end" => Phase::EndToEnd,
            other => panic!("--phase must be parse|execute|end_to_end, got '{other}'"),
        }
    }
}

impl Phase {
    fn as_str(self) -> &'static str {
        match self {
            Phase::Parse => "parse",
            Phase::Execute => "execute",
            Phase::EndToEnd => "end_to_end",
        }
    }
}

#[derive(Debug, Serialize)]
struct RunRow {
    id: String,
    tier: String,
    category: String,
    phase: String,
    mode: String,
    answers: usize,
    iters: usize,
    median_us: f64,
    p95_us: f64,
    engine_steps_median: u64,
    engine_emits_median: u64,
    engine_continues_median: u64,
    compose_attempts_median: u64,
    compose_successes_median: u64,
    meet_attempts_median: u64,
    meet_successes_median: u64,
}

#[derive(Debug, Serialize)]
struct RunReport {
    environment: EnvironmentFingerprint,
    selected_cases: usize,
    iters: usize,
    phase: String,
    rows: Vec<RunRow>,
}

fn parse_args() -> (Option<String>, usize, Phase, bool, bool) {
    let mut id_filter = None;
    let mut iters = 1usize;
    let mut phase = Phase::EndToEnd;
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
        if arg == "--phase" {
            phase = Phase::from_arg(&args.next().expect("--phase requires value"));
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
    (id_filter, iters, phase, json, csv)
}

fn select_cases(id_filter: Option<String>) -> Vec<CorpusCase> {
    let mut filters = CorpusFilters::from_env();
    if let Some(id) = id_filter {
        filters.filter_substring = Some(id);
    }
    let mut cases = apply_filters(load_cases(), &filters);
    sort_cases(&mut cases);
    if cases.is_empty() {
        panic!("no corpus cases selected");
    }
    cases
}

fn median_u64(values: &mut [u64]) -> u64 {
    values.sort_unstable();
    values[values.len() / 2]
}

fn main() {
    let (id_filter, iters, phase, json, csv) = parse_args();
    let cases = select_cases(id_filter);
    let env = environment_fingerprint();

    if !json && !csv {
        println!(
            "selected_cases={} iters={} phase={}",
            cases.len(),
            iters,
            phase.as_str()
        );
    }

    let mut rows = Vec::new();

    for case in &cases {
        let mut samples_ns = Vec::with_capacity(iters);
        let mut last_answers = 0usize;
        let mut engine_steps = Vec::with_capacity(iters);
        let mut engine_emits = Vec::with_capacity(iters);
        let mut engine_continues = Vec::with_capacity(iters);
        let mut compose_attempts = Vec::with_capacity(iters);
        let mut compose_successes = Vec::with_capacity(iters);
        let mut meet_attempts = Vec::with_capacity(iters);
        let mut meet_successes = Vec::with_capacity(iters);

        for _ in 0..iters {
            let start = Instant::now();
            match phase {
                Phase::Parse => {
                    let prepared = prepare_case(case);
                    std::hint::black_box(prepared);
                    engine_steps.push(0);
                    engine_emits.push(0);
                    engine_continues.push(0);
                    compose_attempts.push(0);
                    compose_successes.push(0);
                    meet_attempts.push(0);
                    meet_successes.push(0);
                }
                Phase::Execute => {
                    let prepared = prepare_case(case);
                    let mid = Instant::now();
                    let stats = run_prepared_with_stats(case, prepared);
                    last_answers = stats.answers;
                    engine_steps.push(stats.counters.engine_steps);
                    engine_emits.push(stats.counters.engine_emits);
                    engine_continues.push(stats.counters.engine_continues);
                    compose_attempts.push(stats.counters.compose_attempts);
                    compose_successes.push(stats.counters.compose_successes);
                    meet_attempts.push(stats.counters.meet_attempts);
                    meet_successes.push(stats.counters.meet_successes);
                    let elapsed = mid.elapsed();
                    samples_ns.push(elapsed.as_nanos() as u64);
                    continue;
                }
                Phase::EndToEnd => {
                    let prepared = prepare_case(case);
                    let stats = run_prepared_with_stats(case, prepared);
                    last_answers = stats.answers;
                    engine_steps.push(stats.counters.engine_steps);
                    engine_emits.push(stats.counters.engine_emits);
                    engine_continues.push(stats.counters.engine_continues);
                    compose_attempts.push(stats.counters.compose_attempts);
                    compose_successes.push(stats.counters.compose_successes);
                    meet_attempts.push(stats.counters.meet_attempts);
                    meet_successes.push(stats.counters.meet_successes);
                }
            }
            samples_ns.push(start.elapsed().as_nanos() as u64);
        }

        samples_ns.sort_unstable();
        let median = samples_ns[samples_ns.len() / 2];
        let p95_idx = ((samples_ns.len() as f64) * 0.95).ceil() as usize - 1;
        let p95 = samples_ns[p95_idx.min(samples_ns.len() - 1)];
        let row = RunRow {
            id: case.id.clone(),
            tier: case.tier.as_str().to_string(),
            category: case.category.as_str().to_string(),
            phase: phase.as_str().to_string(),
            mode: case.mode.as_str().to_string(),
            answers: last_answers,
            iters,
            median_us: median as f64 / 1_000.0,
            p95_us: p95 as f64 / 1_000.0,
            engine_steps_median: median_u64(&mut engine_steps),
            engine_emits_median: median_u64(&mut engine_emits),
            engine_continues_median: median_u64(&mut engine_continues),
            compose_attempts_median: median_u64(&mut compose_attempts),
            compose_successes_median: median_u64(&mut compose_successes),
            meet_attempts_median: median_u64(&mut meet_attempts),
            meet_successes_median: median_u64(&mut meet_successes),
        };
        if !json && !csv {
            println!(
                "{} | mode={} | answers={} | median_us={:.3} | p95_us={:.3} | steps={} | compose={} | meet={}",
                row.id,
                row.mode,
                row.answers,
                row.median_us,
                row.p95_us,
                row.engine_steps_median,
                row.compose_attempts_median,
                row.meet_attempts_median,
            );
        }
        rows.push(row);
    }

    if json {
        let report = RunReport {
            environment: env,
            selected_cases: rows.len(),
            iters,
            phase: phase.as_str().to_string(),
            rows,
        };
        println!(
            "{}",
            serde_json::to_string_pretty(&report).expect("serialize run report")
        );
        return;
    }
    if csv {
        println!(
            "id,tier,category,phase,mode,answers,iters,median_us,p95_us,engine_steps_median,engine_emits_median,engine_continues_median,compose_attempts_median,compose_successes_median,meet_attempts_median,meet_successes_median,env_os,env_arch,env_cpu,env_rustc,env_rustflags,env_timestamp_unix_s,env_git_sha,env_run_id"
        );
        for row in rows {
            println!(
                "{},{},{},{},{},{},{},{:.3},{:.3},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}",
                csv_escape(&row.id),
                csv_escape(&row.tier),
                csv_escape(&row.category),
                csv_escape(&row.phase),
                csv_escape(&row.mode),
                row.answers,
                row.iters,
                row.median_us,
                row.p95_us,
                row.engine_steps_median,
                row.engine_emits_median,
                row.engine_continues_median,
                row.compose_attempts_median,
                row.compose_successes_median,
                row.meet_attempts_median,
                row.meet_successes_median,
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

fn csv_escape(s: &str) -> String {
    if s.contains(',') || s.contains('"') || s.contains('\n') {
        format!("\"{}\"", s.replace('"', "\"\""))
    } else {
        s.to_string()
    }
}

fn csv_escape_opt(s: Option<&str>) -> String {
    match s {
        Some(v) => csv_escape(v),
        None => String::new(),
    }
}
