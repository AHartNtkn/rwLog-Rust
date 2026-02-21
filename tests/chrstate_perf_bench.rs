/// Micro-benchmark: ChrState clone/hash/eq performance.
/// Runs corpus cases and reports timing.
///
/// Run with: cargo test --test chrstate_perf_bench --release -- --nocapture
use rwlog::perf_corpus::{self, CorpusFilters, TierFilter};
use std::time::Instant;

#[test]
#[ignore] // Benchmark: only meaningful in --release mode
fn chrstate_perf_comparison() {
    // Use a thread with a larger stack to avoid overflow on deep recursion cases
    let builder = std::thread::Builder::new().stack_size(32 * 1024 * 1024);
    let handle = builder.spawn(run_benchmark).unwrap();
    handle.join().unwrap();
}

fn run_benchmark() {
    let cases = perf_corpus::load_cases();
    let filters = CorpusFilters {
        tier: TierFilter::All,
        ..Default::default()
    };
    let cases = perf_corpus::apply_filters(cases, &filters);

    println!();
    println!(
        "{:<45} {:>6}  {:>10}  {:>10}",
        "Case", "Steps", "Time(ms)", "µs/step"
    );
    println!("{:-<80}", "");

    for case in &cases {
        let prepared = perf_corpus::prepare_case(case);
        let start = Instant::now();
        let (_answers, snap) =
            rwlog::perf_counters::capture(|| perf_corpus::run_prepared(case, prepared));
        let elapsed = start.elapsed();
        let us_per_step = if snap.engine_steps > 0 {
            elapsed.as_micros() as f64 / snap.engine_steps as f64
        } else {
            0.0
        };
        println!(
            "{:<45} {:>6}  {:>10.2}  {:>10.1}",
            case.id,
            snap.engine_steps,
            elapsed.as_micros() as f64 / 1000.0,
            us_per_step
        );
    }
    println!("{:-<80}", "");

    // Focused measurement: run recursive_even_backward_first64 5 times
    let target_id = "recursive_even_backward_first64";
    if let Some(target) = cases.iter().find(|c| c.id == target_id) {
        let mut timings = Vec::new();
        let n_runs = 5;
        for _ in 0..n_runs {
            let prepared = perf_corpus::prepare_case(target);
            let start = Instant::now();
            let (_answers, snap) =
                rwlog::perf_counters::capture(|| perf_corpus::run_prepared(target, prepared));
            let elapsed = start.elapsed();
            let us_per_step = elapsed.as_micros() as f64 / snap.engine_steps as f64;
            timings.push((elapsed, snap.engine_steps, us_per_step, _answers));
        }

        timings.sort_by_key(|a| a.0);
        let median = &timings[n_runs / 2];

        println!("\n=== {} (5 runs) ===", target_id);
        println!("Steps: {}", median.1);
        println!("Answers: {}", median.3);
        println!(
            "Median: {:.2}ms ({:.1} µs/step)",
            median.0.as_micros() as f64 / 1000.0,
            median.2
        );
        println!(
            "Min:    {:.2}ms ({:.1} µs/step)",
            timings[0].0.as_micros() as f64 / 1000.0,
            timings[0].2
        );
        println!(
            "Max:    {:.2}ms ({:.1} µs/step)",
            timings[n_runs - 1].0.as_micros() as f64 / 1000.0,
            timings[n_runs - 1].2
        );
    }
}
