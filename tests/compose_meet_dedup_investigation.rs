/// Investigation: Measure compose_nf/meet_nf input pair duplication rates
/// across the performance corpus to assess caching potential.
///
/// Run with: cargo test --test compose_meet_dedup_investigation --release -- --nocapture
use rwlog::perf_corpus::{self, CorpusFilters, TierFilter};

#[test]
#[ignore] // Investigation benchmark: only meaningful in --release mode
fn measure_compose_meet_duplication() {
    let cases = perf_corpus::load_cases();
    let filters = CorpusFilters {
        tier: TierFilter::All,
        ..Default::default()
    };
    let cases = perf_corpus::apply_filters(cases, &filters);

    println!("\n{:-<140}", "");
    println!(
        "{:<40} {:>8} {:>8} {:>8} {:>8} {:>6} {:>8} {:>8} {:>6}",
        "Case", "Steps", "Emits", "Compose", "Uniq_C", "Dup%", "Meet", "Uniq_M", "Dup%"
    );
    println!("{:-<140}", "");

    let mut total_steps = 0u64;
    let mut total_compose = 0u64;
    let mut total_compose_unique = 0u64;
    let mut total_meet = 0u64;
    let mut total_meet_unique = 0u64;

    for case in &cases {
        let prepared = perf_corpus::prepare_case(case);
        let (_answers, snap) =
            rwlog::perf_counters::capture(|| perf_corpus::run_prepared(case, prepared));

        total_steps += snap.engine_steps;
        total_compose += snap.compose_attempts;
        total_compose_unique += snap.compose_unique_pairs;
        total_meet += snap.meet_attempts;
        total_meet_unique += snap.meet_unique_pairs;

        let compose_dup_pct = if snap.compose_attempts > 0 {
            100.0 * (1.0 - snap.compose_unique_pairs as f64 / snap.compose_attempts as f64)
        } else {
            0.0
        };
        let meet_dup_pct = if snap.meet_attempts > 0 {
            100.0 * (1.0 - snap.meet_unique_pairs as f64 / snap.meet_attempts as f64)
        } else {
            0.0
        };

        println!(
            "{:<40} {:>8} {:>8} {:>8} {:>8} {:>5.1}% {:>8} {:>8} {:>5.1}%",
            case.id,
            snap.engine_steps,
            snap.engine_emits,
            snap.compose_attempts,
            snap.compose_unique_pairs,
            compose_dup_pct,
            snap.meet_attempts,
            snap.meet_unique_pairs,
            meet_dup_pct,
        );

        // Show frequency distribution for cases with compose duplication
        if snap.compose_attempts > 10 && snap.compose_unique_pairs < snap.compose_attempts {
            let (compose_hist, _) = rwlog::perf_counters::pair_frequency_histograms();
            if !compose_hist.is_empty() {
                print!("    freq: ");
                for (count, num_pairs) in &compose_hist {
                    print!("{}x={} ", count, num_pairs);
                }
                println!();
            }
        }
    }

    println!("{:-<140}", "");
    let total_compose_dup = if total_compose > 0 {
        100.0 * (1.0 - total_compose_unique as f64 / total_compose as f64)
    } else {
        0.0
    };
    let total_meet_dup = if total_meet > 0 {
        100.0 * (1.0 - total_meet_unique as f64 / total_meet as f64)
    } else {
        0.0
    };
    println!(
        "{:<40} {:>8} {:>8} {:>8} {:>8} {:>5.1}% {:>8} {:>8} {:>5.1}%",
        "TOTAL",
        total_steps,
        "-",
        total_compose,
        total_compose_unique,
        total_compose_dup,
        total_meet,
        total_meet_unique,
        total_meet_dup,
    );
    println!("{:-<140}", "");
    println!(
        "\nCompose calls as % of engine steps: {:.2}%",
        if total_steps > 0 {
            total_compose as f64 / total_steps as f64 * 100.0
        } else {
            0.0
        }
    );
    println!(
        "Duplicate compose calls saved by cache: {} ({:.1}% of total compose)",
        total_compose - total_compose_unique,
        if total_compose > 0 {
            (total_compose - total_compose_unique) as f64 / total_compose as f64 * 100.0
        } else {
            0.0
        }
    );
}
