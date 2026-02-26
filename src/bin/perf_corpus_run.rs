#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use rwlog::perf_corpus::{
    apply_filters, compile_prepared, environment_fingerprint, load_cases, prepare_case,
    run_compiled_with_stats, run_prepared_with_stats, sort_cases, CorpusCase, CorpusFilters,
    EnvironmentFingerprint, ExecutionCounters,
};
use serde::Serialize;
use std::collections::BTreeMap;
use std::time::Instant;

#[derive(Clone, Copy, Debug)]
enum Phase {
    Parse,
    Compile,
    Execute,
    EndToEnd,
}

impl Phase {
    fn from_arg(s: &str) -> Self {
        match s {
            "parse" => Phase::Parse,
            "compile" => Phase::Compile,
            "execute" => Phase::Execute,
            "end_to_end" => Phase::EndToEnd,
            other => panic!("--phase must be parse|compile|execute|end_to_end, got '{other}'"),
        }
    }
}

impl Phase {
    fn as_str(self) -> &'static str {
        match self {
            Phase::Parse => "parse",
            Phase::Compile => "compile",
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
    engine_steps: u64,
    engine_emits: u64,
    engine_continues: u64,
    engine_exhausted: u64,
    compose_attempts: u64,
    compose_successes: u64,
    compose_failures: u64,
    compose_unique_pairs: u64,
    meet_attempts: u64,
    meet_successes: u64,
    meet_failures: u64,
    meet_unique_pairs: u64,
    fixpoint_producer_starts: u64,
    fixpoint_verification_starts: u64,
    fixpoint_verification_steps: u64,
    or_spine_walks: u64,
    or_spine_total_siblings: u64,
    or_spine_max_siblings: u64,
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

/// Collect per-iteration counter vectors and compute medians.
struct CounterAccumulator {
    engine_steps: Vec<u64>,
    engine_emits: Vec<u64>,
    engine_continues: Vec<u64>,
    engine_exhausted: Vec<u64>,
    compose_attempts: Vec<u64>,
    compose_successes: Vec<u64>,
    compose_failures: Vec<u64>,
    compose_unique_pairs: Vec<u64>,
    meet_attempts: Vec<u64>,
    meet_successes: Vec<u64>,
    meet_failures: Vec<u64>,
    meet_unique_pairs: Vec<u64>,
    fixpoint_producer_starts: Vec<u64>,
    fixpoint_verification_starts: Vec<u64>,
    fixpoint_verification_steps: Vec<u64>,
    or_spine_walks: Vec<u64>,
    or_spine_total_siblings: Vec<u64>,
    or_spine_max_siblings: Vec<u64>,
}

impl CounterAccumulator {
    fn new(capacity: usize) -> Self {
        Self {
            engine_steps: Vec::with_capacity(capacity),
            engine_emits: Vec::with_capacity(capacity),
            engine_continues: Vec::with_capacity(capacity),
            engine_exhausted: Vec::with_capacity(capacity),
            compose_attempts: Vec::with_capacity(capacity),
            compose_successes: Vec::with_capacity(capacity),
            compose_failures: Vec::with_capacity(capacity),
            compose_unique_pairs: Vec::with_capacity(capacity),
            meet_attempts: Vec::with_capacity(capacity),
            meet_successes: Vec::with_capacity(capacity),
            meet_failures: Vec::with_capacity(capacity),
            meet_unique_pairs: Vec::with_capacity(capacity),
            fixpoint_producer_starts: Vec::with_capacity(capacity),
            fixpoint_verification_starts: Vec::with_capacity(capacity),
            fixpoint_verification_steps: Vec::with_capacity(capacity),
            or_spine_walks: Vec::with_capacity(capacity),
            or_spine_total_siblings: Vec::with_capacity(capacity),
            or_spine_max_siblings: Vec::with_capacity(capacity),
        }
    }

    fn push_zeros(&mut self) {
        self.engine_steps.push(0);
        self.engine_emits.push(0);
        self.engine_continues.push(0);
        self.engine_exhausted.push(0);
        self.compose_attempts.push(0);
        self.compose_successes.push(0);
        self.compose_failures.push(0);
        self.compose_unique_pairs.push(0);
        self.meet_attempts.push(0);
        self.meet_successes.push(0);
        self.meet_failures.push(0);
        self.meet_unique_pairs.push(0);
        self.fixpoint_producer_starts.push(0);
        self.fixpoint_verification_starts.push(0);
        self.fixpoint_verification_steps.push(0);
        self.or_spine_walks.push(0);
        self.or_spine_total_siblings.push(0);
        self.or_spine_max_siblings.push(0);
    }

    fn push(&mut self, c: &ExecutionCounters) {
        self.engine_steps.push(c.engine_steps);
        self.engine_emits.push(c.engine_emits);
        self.engine_continues.push(c.engine_continues);
        self.engine_exhausted.push(c.engine_exhausted);
        self.compose_attempts.push(c.compose_attempts);
        self.compose_successes.push(c.compose_successes);
        self.compose_failures.push(c.compose_failures);
        self.compose_unique_pairs.push(c.compose_unique_pairs);
        self.meet_attempts.push(c.meet_attempts);
        self.meet_successes.push(c.meet_successes);
        self.meet_failures.push(c.meet_failures);
        self.meet_unique_pairs.push(c.meet_unique_pairs);
        self.fixpoint_producer_starts
            .push(c.fixpoint_producer_starts);
        self.fixpoint_verification_starts
            .push(c.fixpoint_verification_starts);
        self.fixpoint_verification_steps
            .push(c.fixpoint_verification_steps);
        self.or_spine_walks.push(c.or_spine_walks);
        self.or_spine_total_siblings.push(c.or_spine_total_siblings);
        self.or_spine_max_siblings.push(c.or_spine_max_siblings);
    }

    fn medians(&mut self) -> Medians {
        Medians {
            engine_steps: median_u64(&mut self.engine_steps),
            engine_emits: median_u64(&mut self.engine_emits),
            engine_continues: median_u64(&mut self.engine_continues),
            engine_exhausted: median_u64(&mut self.engine_exhausted),
            compose_attempts: median_u64(&mut self.compose_attempts),
            compose_successes: median_u64(&mut self.compose_successes),
            compose_failures: median_u64(&mut self.compose_failures),
            compose_unique_pairs: median_u64(&mut self.compose_unique_pairs),
            meet_attempts: median_u64(&mut self.meet_attempts),
            meet_successes: median_u64(&mut self.meet_successes),
            meet_failures: median_u64(&mut self.meet_failures),
            meet_unique_pairs: median_u64(&mut self.meet_unique_pairs),
            fixpoint_producer_starts: median_u64(&mut self.fixpoint_producer_starts),
            fixpoint_verification_starts: median_u64(&mut self.fixpoint_verification_starts),
            fixpoint_verification_steps: median_u64(&mut self.fixpoint_verification_steps),
            or_spine_walks: median_u64(&mut self.or_spine_walks),
            or_spine_total_siblings: median_u64(&mut self.or_spine_total_siblings),
            or_spine_max_siblings: median_u64(&mut self.or_spine_max_siblings),
        }
    }
}

struct Medians {
    engine_steps: u64,
    engine_emits: u64,
    engine_continues: u64,
    engine_exhausted: u64,
    compose_attempts: u64,
    compose_successes: u64,
    compose_failures: u64,
    compose_unique_pairs: u64,
    meet_attempts: u64,
    meet_successes: u64,
    meet_failures: u64,
    meet_unique_pairs: u64,
    fixpoint_producer_starts: u64,
    fixpoint_verification_starts: u64,
    fixpoint_verification_steps: u64,
    or_spine_walks: u64,
    or_spine_total_siblings: u64,
    or_spine_max_siblings: u64,
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
        println!();
    }

    let mut rows = Vec::new();

    for case in &cases {
        let mut samples_ns = Vec::with_capacity(iters);
        let mut last_answers = 0usize;
        let mut acc = CounterAccumulator::new(iters);

        for _ in 0..iters {
            let start = Instant::now();
            match phase {
                Phase::Parse => {
                    let prepared = prepare_case(case);
                    std::hint::black_box(prepared);
                    acc.push_zeros();
                }
                Phase::Compile => {
                    let prepared = prepare_case(case);
                    let mid = Instant::now();
                    let engine = compile_prepared(prepared);
                    std::hint::black_box(engine);
                    acc.push_zeros();
                    let elapsed = mid.elapsed();
                    samples_ns.push(elapsed.as_nanos() as u64);
                    continue;
                }
                Phase::Execute => {
                    let prepared = prepare_case(case);
                    let engine = compile_prepared(prepared);
                    let mid = Instant::now();
                    let stats = run_compiled_with_stats(case, engine);
                    last_answers = stats.answers;
                    acc.push(&stats.counters);
                    let elapsed = mid.elapsed();
                    samples_ns.push(elapsed.as_nanos() as u64);
                    continue;
                }
                Phase::EndToEnd => {
                    let prepared = prepare_case(case);
                    let stats = run_prepared_with_stats(case, prepared);
                    last_answers = stats.answers;
                    acc.push(&stats.counters);
                }
            }
            samples_ns.push(start.elapsed().as_nanos() as u64);
        }

        samples_ns.sort_unstable();
        let median = samples_ns[samples_ns.len() / 2];
        let p95_idx = ((samples_ns.len() as f64) * 0.95).ceil() as usize - 1;
        let p95 = samples_ns[p95_idx.min(samples_ns.len() - 1)];
        let m = acc.medians();
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
            engine_steps: m.engine_steps,
            engine_emits: m.engine_emits,
            engine_continues: m.engine_continues,
            engine_exhausted: m.engine_exhausted,
            compose_attempts: m.compose_attempts,
            compose_successes: m.compose_successes,
            compose_failures: m.compose_failures,
            compose_unique_pairs: m.compose_unique_pairs,
            meet_attempts: m.meet_attempts,
            meet_successes: m.meet_successes,
            meet_failures: m.meet_failures,
            meet_unique_pairs: m.meet_unique_pairs,
            fixpoint_producer_starts: m.fixpoint_producer_starts,
            fixpoint_verification_starts: m.fixpoint_verification_starts,
            fixpoint_verification_steps: m.fixpoint_verification_steps,
            or_spine_walks: m.or_spine_walks,
            or_spine_total_siblings: m.or_spine_total_siblings,
            or_spine_max_siblings: m.or_spine_max_siblings,
        };
        if !json && !csv {
            print_case_row(&row);
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
        print_csv(&rows, &env);
        return;
    }

    // Default text mode: print breakdown after per-case rows
    if rows.len() > 1 {
        println!();
        print_breakdown(&rows);
    }
}

fn print_case_row(r: &RunRow) {
    print!(
        "  {:<40} {:>10.1} us  steps={:<8} compose={:<6} meet={:<6}",
        r.id, r.median_us, r.engine_steps, r.compose_attempts, r.meet_attempts,
    );
    if r.fixpoint_producer_starts > 0 {
        print!("  fix={}", r.fixpoint_producer_starts);
    }
    if r.or_spine_walks > 0 {
        print!("  or_spine={}", r.or_spine_walks);
    }
    println!();
}

fn print_breakdown(rows: &[RunRow]) {
    let total_us: f64 = rows.iter().map(|r| r.median_us).sum();
    let total_steps: u64 = rows.iter().map(|r| r.engine_steps).sum();
    let total_compose: u64 = rows.iter().map(|r| r.compose_attempts).sum();
    let total_compose_succ: u64 = rows.iter().map(|r| r.compose_successes).sum();
    let total_compose_fail: u64 = rows.iter().map(|r| r.compose_failures).sum();
    let total_meet: u64 = rows.iter().map(|r| r.meet_attempts).sum();
    let total_meet_succ: u64 = rows.iter().map(|r| r.meet_successes).sum();
    let total_meet_fail: u64 = rows.iter().map(|r| r.meet_failures).sum();
    let total_fixpoint_starts: u64 = rows.iter().map(|r| r.fixpoint_producer_starts).sum();
    let total_fixpoint_verif: u64 = rows.iter().map(|r| r.fixpoint_verification_starts).sum();
    let total_fixpoint_vsteps: u64 = rows.iter().map(|r| r.fixpoint_verification_steps).sum();
    let total_or_walks: u64 = rows.iter().map(|r| r.or_spine_walks).sum();
    let total_or_siblings: u64 = rows.iter().map(|r| r.or_spine_total_siblings).sum();
    let max_or_siblings: u64 = rows
        .iter()
        .map(|r| r.or_spine_max_siblings)
        .max()
        .unwrap_or(0);
    let total_emits: u64 = rows.iter().map(|r| r.engine_emits).sum();
    let total_exhausted: u64 = rows.iter().map(|r| r.engine_exhausted).sum();

    // === CATEGORY BREAKDOWN ===
    println!("=== BY CATEGORY ===");
    println!();

    struct CatStats {
        count: usize,
        time_us: f64,
        steps: u64,
        compose: u64,
        meet: u64,
        fixpoint: u64,
        or_spine: u64,
    }

    let mut by_cat: BTreeMap<&str, CatStats> = BTreeMap::new();
    for r in rows {
        let e = by_cat.entry(&r.category).or_insert(CatStats {
            count: 0,
            time_us: 0.0,
            steps: 0,
            compose: 0,
            meet: 0,
            fixpoint: 0,
            or_spine: 0,
        });
        e.count += 1;
        e.time_us += r.median_us;
        e.steps += r.engine_steps;
        e.compose += r.compose_attempts;
        e.meet += r.meet_attempts;
        e.fixpoint += r.fixpoint_producer_starts;
        e.or_spine += r.or_spine_walks;
    }

    let mut cat_entries: Vec<_> = by_cat.iter().collect();
    cat_entries.sort_by(|a, b| b.1.time_us.partial_cmp(&a.1.time_us).unwrap());

    for (cat, s) in &cat_entries {
        let pct = if total_us > 0.0 {
            s.time_us / total_us * 100.0
        } else {
            0.0
        };
        print!(
            "  {:<18} {:>2} cases {:>10.1} us ({:>5.1}%)  steps={:<8} compose={:<6} meet={:<6}",
            cat, s.count, s.time_us, pct, s.steps, s.compose, s.meet,
        );
        if s.fixpoint > 0 {
            print!("  fix={}", s.fixpoint);
        }
        if s.or_spine > 0 {
            print!("  or_spine={}", s.or_spine);
        }
        println!();
    }

    // === TIER BREAKDOWN ===
    println!();
    println!("=== BY TIER ===");
    println!();

    let mut by_tier: BTreeMap<&str, (usize, f64, u64)> = BTreeMap::new();
    for r in rows {
        let e = by_tier.entry(&r.tier).or_insert((0, 0.0, 0));
        e.0 += 1;
        e.1 += r.median_us;
        e.2 += r.engine_steps;
    }
    let mut tier_entries: Vec<_> = by_tier.iter().collect();
    tier_entries.sort_by(|a, b| b.1 .1.partial_cmp(&a.1 .1).unwrap());
    for (tier, (count, time, steps)) in &tier_entries {
        let pct = if total_us > 0.0 {
            time / total_us * 100.0
        } else {
            0.0
        };
        println!(
            "  {:<10} {:>2} cases {:>10.1} us ({:>5.1}%)  steps={}",
            tier, count, time, pct, steps
        );
    }

    // === ENGINE PROFILE ===
    println!();
    println!("=== ENGINE PROFILE ===");
    println!();
    println!("  total_time     = {:.1} us", total_us);
    println!("  total_steps    = {}", total_steps);
    println!("  total_emits    = {}", total_emits);
    println!("  total_exhausted= {}", total_exhausted);
    println!();

    let compose_pct = if total_steps > 0 {
        total_compose as f64 / total_steps as f64 * 100.0
    } else {
        0.0
    };
    let meet_pct = if total_steps > 0 {
        total_meet as f64 / total_steps as f64 * 100.0
    } else {
        0.0
    };
    println!(
        "  compose: {} attempts ({} success, {} fail) — {:.1}% of steps",
        total_compose, total_compose_succ, total_compose_fail, compose_pct,
    );
    println!(
        "  meet:    {} attempts ({} success, {} fail) — {:.1}% of steps",
        total_meet, total_meet_succ, total_meet_fail, meet_pct,
    );

    if total_fixpoint_starts > 0 || total_fixpoint_verif > 0 {
        println!(
            "  fixpoint: {} producers, {} verifications, {} verification steps",
            total_fixpoint_starts, total_fixpoint_verif, total_fixpoint_vsteps,
        );
    }
    if total_or_walks > 0 {
        let avg_siblings = if total_or_walks > 0 {
            total_or_siblings as f64 / total_or_walks as f64
        } else {
            0.0
        };
        println!(
            "  or_spine: {} walks, avg {:.1} siblings/walk, max {}",
            total_or_walks, avg_siblings, max_or_siblings,
        );
    }

    // === HOTSPOTS ===
    println!();
    println!("=== HOTSPOTS BY TIME ===");
    println!();
    let mut by_time: Vec<_> = rows.iter().collect();
    by_time.sort_by(|a, b| b.median_us.partial_cmp(&a.median_us).unwrap());
    for (i, r) in by_time.iter().take(10).enumerate() {
        let pct = if total_us > 0.0 {
            r.median_us / total_us * 100.0
        } else {
            0.0
        };
        println!(
            "  {:>2}. {:<40} {:>10.1} us ({:>5.1}%)  compose={:<6} meet={:<6} fix={:<4} or={}",
            i + 1,
            r.id,
            r.median_us,
            pct,
            r.compose_attempts,
            r.meet_attempts,
            r.fixpoint_producer_starts,
            r.or_spine_walks,
        );
    }

    if total_compose > 0 {
        println!();
        println!("=== HOTSPOTS BY COMPOSE ===");
        println!();
        let mut by_compose: Vec<_> = rows.iter().filter(|r| r.compose_attempts > 0).collect();
        by_compose.sort_by_key(|r| std::cmp::Reverse(r.compose_attempts));
        for (i, r) in by_compose.iter().take(10).enumerate() {
            let pct = r.compose_attempts as f64 / total_compose as f64 * 100.0;
            println!(
                "  {:>2}. {:<40} {:>8} ({:>5.1}%)  unique_pairs={} success_rate={:.0}%",
                i + 1,
                r.id,
                r.compose_attempts,
                pct,
                r.compose_unique_pairs,
                if r.compose_attempts > 0 {
                    r.compose_successes as f64 / r.compose_attempts as f64 * 100.0
                } else {
                    0.0
                },
            );
        }
    }

    if total_meet > 0 {
        println!();
        println!("=== HOTSPOTS BY MEET ===");
        println!();
        let mut by_meet: Vec<_> = rows.iter().filter(|r| r.meet_attempts > 0).collect();
        by_meet.sort_by_key(|r| std::cmp::Reverse(r.meet_attempts));
        for (i, r) in by_meet.iter().take(10).enumerate() {
            let pct = r.meet_attempts as f64 / total_meet as f64 * 100.0;
            println!(
                "  {:>2}. {:<40} {:>8} ({:>5.1}%)  unique_pairs={} success_rate={:.0}%",
                i + 1,
                r.id,
                r.meet_attempts,
                pct,
                r.meet_unique_pairs,
                if r.meet_attempts > 0 {
                    r.meet_successes as f64 / r.meet_attempts as f64 * 100.0
                } else {
                    0.0
                },
            );
        }
    }

    if total_fixpoint_starts > 0 {
        println!();
        println!("=== HOTSPOTS BY FIXPOINT ===");
        println!();
        let mut by_fix: Vec<_> = rows
            .iter()
            .filter(|r| r.fixpoint_producer_starts > 0)
            .collect();
        by_fix.sort_by_key(|r| std::cmp::Reverse(r.fixpoint_verification_steps));
        for (i, r) in by_fix.iter().take(10).enumerate() {
            println!(
                "  {:>2}. {:<40} producers={:<4} verifications={:<4} verification_steps={}",
                i + 1,
                r.id,
                r.fixpoint_producer_starts,
                r.fixpoint_verification_starts,
                r.fixpoint_verification_steps,
            );
        }
    }

    if total_or_walks > 0 {
        println!();
        println!("=== HOTSPOTS BY OR-SPINE ===");
        println!();
        let mut by_or: Vec<_> = rows.iter().filter(|r| r.or_spine_walks > 0).collect();
        by_or.sort_by_key(|r| std::cmp::Reverse(r.or_spine_total_siblings));
        for (i, r) in by_or.iter().take(10).enumerate() {
            let avg = if r.or_spine_walks > 0 {
                r.or_spine_total_siblings as f64 / r.or_spine_walks as f64
            } else {
                0.0
            };
            println!(
                "  {:>2}. {:<40} walks={:<8} avg_siblings={:<6.1} max_siblings={}",
                i + 1,
                r.id,
                r.or_spine_walks,
                avg,
                r.or_spine_max_siblings,
            );
        }
    }
}

fn print_csv(rows: &[RunRow], env: &EnvironmentFingerprint) {
    println!(
        "id,tier,category,phase,mode,answers,iters,median_us,p95_us,\
         engine_steps,engine_emits,engine_continues,engine_exhausted,\
         compose_attempts,compose_successes,compose_failures,compose_unique_pairs,\
         meet_attempts,meet_successes,meet_failures,meet_unique_pairs,\
         fixpoint_producer_starts,fixpoint_verification_starts,fixpoint_verification_steps,\
         or_spine_walks,or_spine_total_siblings,or_spine_max_siblings,\
         env_os,env_arch,env_cpu,env_rustc,env_rustflags,env_timestamp_unix_s,env_git_sha,env_run_id"
    );
    for r in rows {
        println!(
            "{},{},{},{},{},{},{},{:.3},{:.3},\
             {},{},{},{},\
             {},{},{},{},\
             {},{},{},{},\
             {},{},{},\
             {},{},{},\
             {},{},{},{},{},{},{},{}",
            csv_escape(&r.id),
            csv_escape(&r.tier),
            csv_escape(&r.category),
            csv_escape(&r.phase),
            csv_escape(&r.mode),
            r.answers,
            r.iters,
            r.median_us,
            r.p95_us,
            r.engine_steps,
            r.engine_emits,
            r.engine_continues,
            r.engine_exhausted,
            r.compose_attempts,
            r.compose_successes,
            r.compose_failures,
            r.compose_unique_pairs,
            r.meet_attempts,
            r.meet_successes,
            r.meet_failures,
            r.meet_unique_pairs,
            r.fixpoint_producer_starts,
            r.fixpoint_verification_starts,
            r.fixpoint_verification_steps,
            r.or_spine_walks,
            r.or_spine_total_siblings,
            r.or_spine_max_siblings,
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
