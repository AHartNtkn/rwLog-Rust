# Corpus Ownership And Threshold Policy

## Corpus Ownership

- Corpus schema and lint policy owner: performance corpus maintainers.
- Case content owner: subsystem owner for each workload category.
- Gate threshold owner: performance corpus maintainers with subsystem sign-off.

## Threshold Source Of Truth

- Quick gate thresholds are defined only in `benches/perf_corpus_cases.toml`:
  - `quick_gate_max_median_us`
  - `quick_gate_max_p95_us`
- `perf/quick_gate.toml` controls sampling policy only (`samples`, `warmup`, `tolerance_pct`).

## Threshold Change Rules

- Every threshold change must include:
  - affected case ids
  - measured old/new medians and p95
  - root-cause summary (workload drift, algorithm change, infra variance, or bug fix)
- Increasing thresholds requires explicit justification and reviewer sign-off from a corpus maintainer.
- Decreasing thresholds is encouraged when stable improvements are observed.

## Completeness Rules

- All `quick` tier cases must define both quick gate thresholds.
- `stress` tier cases must not define quick gate thresholds.
- Lint failures on these rules block corpus tooling and CI usage.

## Reviewer Checklist

- Verify no threshold changed without matching performance evidence.
- Verify threshold changes are scoped to intended cases.
- Verify gate still covers all quick cases.
