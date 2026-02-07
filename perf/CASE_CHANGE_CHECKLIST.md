# Corpus Case Change Checklist

Use this checklist for PRs that add/remove/edit corpus cases.

## Case Semantics

- [ ] Case asserts meaningful semantic behavior (not internal representation quirks).
- [ ] `expected_kind` and `expected_value` are correct and validated locally.
- [ ] Mode is appropriate (`first_answer`, `first_n`, or `exhaust`).

## Metadata Quality

- [ ] `title` and `description` are specific and non-empty.
- [ ] `tags` include searchable intent keywords.
- [ ] `determinism`, `answer_shape`, and `infinite_stream` are accurate.
- [ ] Category and tier assignment match intended workload.

## Gate Policy

- [ ] If `tier = "quick"`, set `quick_gate_max_median_us` and `quick_gate_max_p95_us`.
- [ ] If `tier = "stress"`, no quick gate thresholds are present.
- [ ] Threshold values are justified by measured data.

## Validation Commands

- [ ] `cargo test --no-run 2>&1`
- [ ] `timeout 30 cargo test 2>&1`
- [ ] `RWLOG_CORPUS_TIER=quick cargo run --release --bin perf_corpus_sanity -- --lint --json`
- [ ] `cargo run --release --bin perf_corpus_gate -- --json`

## Review Notes

- [ ] PR description explains why the case improves corpus coverage.
- [ ] Any deletions justify lost coverage and replacement strategy.
