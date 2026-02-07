/// Investigation: Measure Or tree spine walk costs across the performance corpus.
///
/// Tracks: number of Or spine walks, total siblings traversed, peak siblings
/// in a single walk. This quantifies the O(n) per-step overhead from binary
/// Or tree rotation.
///
/// Run with: cargo test --test or_tree_investigation --release -- --nocapture
use rwlog::perf_corpus::{self, CorpusFilters, TierFilter};

#[test]
fn measure_or_spine_costs() {
    let cases = perf_corpus::load_cases();
    let filters = CorpusFilters {
        tier: TierFilter::All,
        ..Default::default()
    };
    let cases = perf_corpus::apply_filters(cases, &filters);

    println!("\n{:-<150}", "");
    println!(
        "{:<40} {:>8} {:>8} {:>8} {:>10} {:>10} {:>10} {:>10} {:>8}",
        "Case", "Steps", "Emits", "OrWalks", "TotalSibs", "MaxSibs", "AvgSibs", "SibSteps%", "µs/step"
    );
    println!("{:-<150}", "");

    let mut grand_steps = 0u64;
    let mut grand_or_walks = 0u64;
    let mut grand_total_siblings = 0u64;
    let mut grand_max_siblings = 0u64;

    for case in &cases {
        let prepared = perf_corpus::prepare_case(case);

        let start = std::time::Instant::now();
        let (_answers, snap) = rwlog::perf_counters::capture(|| {
            perf_corpus::run_prepared(case, prepared)
        });
        let elapsed = start.elapsed();

        grand_steps += snap.engine_steps;
        grand_or_walks += snap.or_spine_walks;
        grand_total_siblings += snap.or_spine_total_siblings;
        if snap.or_spine_max_siblings > grand_max_siblings {
            grand_max_siblings = snap.or_spine_max_siblings;
        }

        let avg_siblings = if snap.or_spine_walks > 0 {
            snap.or_spine_total_siblings as f64 / snap.or_spine_walks as f64
        } else {
            0.0
        };

        // Sibling steps as % of total engine steps: how much work is pure Or overhead
        let sib_pct = if snap.engine_steps > 0 {
            snap.or_spine_total_siblings as f64 / snap.engine_steps as f64 * 100.0
        } else {
            0.0
        };

        let us_per_step = if snap.engine_steps > 0 {
            elapsed.as_micros() as f64 / snap.engine_steps as f64
        } else {
            0.0
        };

        println!(
            "{:<40} {:>8} {:>8} {:>8} {:>10} {:>10} {:>10.1} {:>9.1}% {:>8.1}",
            case.id,
            snap.engine_steps,
            snap.engine_emits,
            snap.or_spine_walks,
            snap.or_spine_total_siblings,
            snap.or_spine_max_siblings,
            avg_siblings,
            sib_pct,
            us_per_step,
        );
    }

    println!("{:-<150}", "");
    let grand_avg = if grand_or_walks > 0 {
        grand_total_siblings as f64 / grand_or_walks as f64
    } else {
        0.0
    };
    let grand_sib_pct = if grand_steps > 0 {
        grand_total_siblings as f64 / grand_steps as f64 * 100.0
    } else {
        0.0
    };
    println!(
        "{:<40} {:>8} {:>8} {:>8} {:>10} {:>10} {:>10.1} {:>9.1}%",
        "TOTAL",
        grand_steps,
        "-",
        grand_or_walks,
        grand_total_siblings,
        grand_max_siblings,
        grand_avg,
        grand_sib_pct,
    );
    println!("{:-<150}", "");

    println!("\nKey metrics:");
    println!("  Total engine steps: {}", grand_steps);
    println!("  Total Or spine walks: {} ({:.1}% of steps are Or rotations)",
        grand_or_walks,
        if grand_steps > 0 { grand_or_walks as f64 / grand_steps as f64 * 100.0 } else { 0.0 });
    println!("  Total sibling nodes traversed: {} (avg {:.1} per walk)",
        grand_total_siblings, grand_avg);
    println!("  Peak siblings in single walk: {}", grand_max_siblings);
    println!("  Sibling traversals as fraction of engine steps: {:.1}x",
        if grand_steps > 0 { grand_total_siblings as f64 / grand_steps as f64 } else { 0.0 });
}
