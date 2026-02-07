//! Performance corpus benchmarks.
//!
//! Case definitions are loaded from `benches/perf_corpus_cases.toml`.
//!
//! Optional filters:
//! - `RWLOG_CORPUS_TIER=quick|stress|all` (default: all)
//! - `RWLOG_CORPUS_CATEGORY=finite_det,recursive,...`
//! - `RWLOG_CORPUS_FILTER=<substring>`
//! - `RWLOG_CORPUS_MAX_CASES=<n>`
//! - `RWLOG_CORPUS_DETERMINISM=deterministic|nondeterministic`
//! - `RWLOG_CORPUS_ANSWER_SHAPE=single|finite|prefix_stream`
//! - `RWLOG_CORPUS_TAGS=tag1,tag2`

use criterion::{black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use rwlog::perf_corpus::{
    apply_filters, case_bench_id, prepare_case, run_prepared, sort_cases, summary_string,
    validate_cases, CorpusCase, CorpusFilters, RunMode,
};
use std::sync::OnceLock;

fn selected_cases() -> &'static [CorpusCase] {
    static CASES: OnceLock<Vec<CorpusCase>> = OnceLock::new();
    CASES.get_or_init(|| {
        let filters = CorpusFilters::from_env();
        let mut cases = apply_filters(rwlog::perf_corpus::load_cases(), &filters);
        sort_cases(&mut cases);
        assert!(
            !cases.is_empty(),
            "no corpus cases selected after filtering"
        );
        eprintln!("{}", summary_string(&cases, &filters));
        validate_cases(&cases).expect("corpus case validation");
        cases
    })
}

fn mode_suffix(mode: RunMode) -> &'static str {
    match mode {
        RunMode::FirstAnswer => "first_answer",
        RunMode::FirstN(_) => "first_n",
        RunMode::Exhaust => "exhaust",
    }
}

fn bench_corpus_execute(c: &mut Criterion) {
    for mode in [RunMode::FirstAnswer, RunMode::FirstN(1), RunMode::Exhaust] {
        let mode_name = mode_suffix(mode);
        let mut group = c.benchmark_group(format!("corpus_execute_{mode_name}"));
        for case in selected_cases() {
            if mode_suffix(case.mode) != mode_name {
                continue;
            }
            group.bench_with_input(
                BenchmarkId::from_parameter(case_bench_id(case)),
                case,
                |b, case| {
                    b.iter_batched(
                        || prepare_case(case),
                        |prepared| black_box(run_prepared(case, prepared)),
                        BatchSize::SmallInput,
                    );
                },
            );
        }
        group.finish();
    }
}

fn bench_corpus_parse(c: &mut Criterion) {
    let mut group = c.benchmark_group("corpus_parse");
    for case in selected_cases() {
        group.bench_with_input(
            BenchmarkId::new(mode_suffix(case.mode), case_bench_id(case)),
            case,
            |b, case| {
                b.iter(|| black_box(prepare_case(case)));
            },
        );
    }
    group.finish();
}

fn bench_corpus_end_to_end(c: &mut Criterion) {
    for mode in [RunMode::FirstAnswer, RunMode::FirstN(1), RunMode::Exhaust] {
        let mode_name = mode_suffix(mode);
        let mut group = c.benchmark_group(format!("corpus_end_to_end_{mode_name}"));
        for case in selected_cases() {
            if mode_suffix(case.mode) != mode_name {
                continue;
            }
            group.bench_with_input(
                BenchmarkId::from_parameter(case_bench_id(case)),
                case,
                |b, case| {
                    b.iter(|| {
                        let prepared = prepare_case(case);
                        black_box(run_prepared(case, prepared))
                    });
                },
            );
        }
        group.finish();
    }
}

criterion_group!(
    perf_corpus_benches,
    bench_corpus_execute,
    bench_corpus_parse,
    bench_corpus_end_to_end
);
criterion_main!(perf_corpus_benches);
