//! Profiling harness: runs a corpus workload in a tight loop for `perf record`.
//!
//! Unlike `alloc_profile --perf`, this binary uses the system allocator
//! (no counting overhead) and runs for a time-based duration to guarantee
//! sufficient samples for reliable profiling.
//!
//! Usage:
//!   cargo build --release --bin perf_profile
//!   perf record -g --call-graph dwarf ./target/release/perf_profile
//!   perf report
//!
//! On hybrid CPUs (Intel 12th+), specify the performance core event:
//!   perf record -e cpu_core/cycles/P -g --call-graph dwarf ./target/release/perf_profile
//!
//! Options:
//!   --id <case_id>    Corpus case to run (default: recursive_even_backward_first64)
//!   --secs <n>        Duration in seconds (default: 5)

use rwlog::perf_corpus::{
    apply_filters, load_cases, prepare_case, run_prepared, sort_cases, CorpusFilters,
};
use std::time::{Duration, Instant};

fn get_case(id: &str) -> rwlog::perf_corpus::CorpusCase {
    let filters = CorpusFilters::from_env();
    let mut cases = apply_filters(load_cases(), &filters);
    sort_cases(&mut cases);
    cases
        .into_iter()
        .find(|c| c.id == id)
        .unwrap_or_else(|| panic!("case '{}' not found", id))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let case_id = args
        .iter()
        .position(|a| a == "--id")
        .and_then(|i| args.get(i + 1))
        .map(|s| s.as_str())
        .unwrap_or("recursive_even_backward_first64");
    let secs: u64 = args
        .iter()
        .position(|a| a == "--secs")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
        .unwrap_or(5);

    let case = get_case(case_id);
    let duration = Duration::from_secs(secs);

    // Warmup: one iteration to fill caches, trigger JIT-like effects
    {
        let prepared = prepare_case(&case);
        let n = run_prepared(&case, prepared);
        std::hint::black_box(n);
    }

    eprintln!("Profiling '{}' for {}s...", case_id, secs);

    let start = Instant::now();
    let mut iters = 0u64;
    while start.elapsed() < duration {
        let prepared = prepare_case(&case);
        let n = run_prepared(&case, prepared);
        std::hint::black_box(n);
        iters += 1;
    }
    let elapsed = start.elapsed();

    eprintln!(
        "Done: {} iterations in {:.2}s ({:.2}ms/iter)",
        iters,
        elapsed.as_secs_f64(),
        elapsed.as_secs_f64() / iters as f64 * 1000.0
    );
}
