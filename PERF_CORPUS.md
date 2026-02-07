# Performance Corpus Architecture

This repository now has a dedicated benchmark corpus in:

- `benches/perf_corpus.rs` (loader + benchmark harness)
- `benches/perf_corpus_cases.toml` (machine-readable case inventory)

## Purpose

The corpus is intended to prevent one-dimensional tuning and force performance work to be evaluated across multiple scenario classes.
It is designed to answer:

1. Did this change help deterministic pipelines?
2. Did it help nondeterministic branching?
3. Did it help recursion/tabling behavior?
4. Did it help CHR/constraint-heavy paths?
5. Did it help deep-term structural matching?
6. Did it help wide search trees?

## Current Harness Shape

Each corpus case includes:

- `id`: stable name for reports
- `title`: human-friendly label
- `description`: one-line intent
- `tier`: `quick` or `stress`
- `category`: workload class
- `program`: relation/theory definitions
- `query`: query expression
- `mode`:
  - `FirstAnswer`
  - `FirstN(k)`
  - `Exhaust`
- `expected`: basic validity check (`Exact(n)` or `AtLeast(n)`)
- `tags`: optional searchable metadata
- `determinism`: `deterministic` or `nondeterministic`
- `answer_shape`: `single`, `finite`, or `prefix_stream`
- `infinite_stream`: whether the unconstrained relation is expected to stream indefinitely
- `quick_gate_max_median_us` / `quick_gate_max_p95_us`: quick-tier gate budgets (required for `quick`, absent for `stress`)
- `noise_target_cv_pct` / `noise_flaky_cv_pct`: per-case noise policy for quick gate and trend confidence logic
- `adaptive_min_samples` / `adaptive_max_samples`: per-case adaptive sampling bounds for quick gate
- `notes`: optional case-specific context

The harness runs three benchmark families:

1. `corpus_execute`: parse/setup excluded from timing (`iter_batched` setup).
2. `corpus_parse`: parse/prepare cost only.
3. `corpus_end_to_end`: parse + execute measured together.

## Why These Three Families

- `corpus_execute` isolates engine and normalization behavior.
- `corpus_parse` isolates parser/definition ingestion and environment setup.
- `corpus_end_to_end` captures user-perceived total latency.

Optimizations can improve one and hurt another; this split makes tradeoffs visible.

## Existing Scenario Coverage

The initial corpus includes:

- deterministic identity and long sequence chain
- wide disjunction cases (16 and 64 branches)
- selective conjunction intersection
- deep nested term matching
- recursive Peano addition (forward and backward)
- mutual recursion stream prefix (`even ; @yes`)
- CHR guard-based constraints (`nonzero`, `between`)
- tree calculus scenarios from `examples/treecalc.txt`
- quick and stress tiers for most categories

## Filters and Selection

You can slice the corpus with environment variables:

```bash
# default: all tiers
cargo bench --bench perf_corpus

# quick-only
RWLOG_CORPUS_TIER=quick cargo bench --bench perf_corpus

# stress-only recursive cases
RWLOG_CORPUS_TIER=stress RWLOG_CORPUS_CATEGORY=recursive cargo bench --bench perf_corpus

# case-id substring filter
RWLOG_CORPUS_FILTER=treecalc cargo bench --bench perf_corpus

# cap number of selected cases
RWLOG_CORPUS_MAX_CASES=5 cargo bench --bench perf_corpus

# determinism filter
RWLOG_CORPUS_DETERMINISM=deterministic cargo bench --bench perf_corpus

# answer shape filter
RWLOG_CORPUS_ANSWER_SHAPE=prefix_stream cargo bench --bench perf_corpus

# tag filter (any match)
RWLOG_CORPUS_TAGS=treecalc,stress cargo bench --bench perf_corpus
```

During startup, the harness prints:

- selected case count
- tier/category counts
- a case inventory line per selected case with mode, expectations, tags, and description

## Running

```bash
cargo bench --bench perf_corpus
```

Quick and stress helper scripts:

```bash
scripts/perf/quick.sh
scripts/perf/stress.sh
```

Pinned environment wrapper for better run-to-run stability:

```bash
scripts/perf/pinned_env.sh cargo bench --bench perf_corpus
```

Case-level runner:

```bash
cargo run --release --bin perf_corpus_run -- --id treecalc --phase execute --iters 30
```

Allocation visibility (parse vs execute):

```bash
cargo run --release --bin perf_corpus_alloc -- --iters 5
```

Corpus sanity/inventory:

```bash
cargo run --release --bin perf_corpus_sanity
cargo run --release --bin perf_corpus_sanity -- --lint
cargo run --release --bin perf_corpus_sanity -- --validate
cargo run --release --bin perf_corpus_sanity -- --lint --validate --json
cargo run --release --bin perf_corpus_sanity -- --lint --validate --csv
```

Case-level runner (text or JSON):

```bash
cargo run --release --bin perf_corpus_run -- --id treecalc --phase execute --iters 30
cargo run --release --bin perf_corpus_run -- --phase end_to_end --iters 20 --json
cargo run --release --bin perf_corpus_run -- --phase end_to_end --iters 20 --csv
```

`perf_corpus_run` includes median internal execution counters per case:

- `engine_steps`, `engine_emits`, `engine_continues`
- `compose_attempts`, `compose_successes`
- `meet_attempts`, `meet_successes`

Allocation visibility (text or JSON):

```bash
cargo run --release --bin perf_corpus_alloc -- --iters 5
cargo run --release --bin perf_corpus_alloc -- --iters 5 --json
cargo run --release --bin perf_corpus_alloc -- --iters 5 --csv
```

`perf_corpus_alloc` includes the same execute-phase counters (median values) next to allocation metrics.

Quick gate (text or JSON):

```bash
cargo run --release --bin perf_corpus_gate
cargo run --release --bin perf_corpus_gate -- --json
cargo run --release --bin perf_corpus_gate -- --csv
```

`perf_corpus_gate` now records per-case variance metrics (`cv_pct`, `mad_pct`, `ci95_halfwidth_pct`), adaptive sample counts, and flaky/noisy flags.

Baseline snapshot + comparison:

```bash
scripts/perf/save_baseline.sh main
scripts/perf/compare_baseline.sh main
```

Diff threshold tuning:

```bash
RWLOG_REGRESS_THRESHOLD_PCT=3 scripts/perf/compare_baseline.sh main
```

Recommend updated quick gate thresholds from fresh measurements:

```bash
cargo run --release --bin perf_corpus_recommend_gate -- --headroom-pct 20
cargo run --release --bin perf_corpus_recommend_gate -- --json
cargo run --release --bin perf_corpus_recommend_gate -- --headroom-pct 20 --apply
```

Apply recommendations to a copied cases file first (dry-run safety pattern):

```bash
cp benches/perf_corpus_cases.toml /tmp/perf_cases.toml
cargo run --release --bin perf_corpus_recommend_gate -- \
  --headroom-pct 20 \
  --apply \
  --apply-file /tmp/perf_cases.toml
```

Generate CI markdown summary from JSON artifacts:

```bash
cargo run --release --bin perf_corpus_ci_summary -- \
  --title "Perf Corpus Quick Gate" \
  --sanity-json perf-artifacts/quick_sanity.json \
  --gate-json perf-artifacts/quick_gate.json \
  --probe-json perf-artifacts/quick_probe.json \
  --status-json-out perf-artifacts/quick_status.json \
  --out perf-artifacts/quick_summary.md
```

`--status-json-out` writes a machine-readable status report intended for dashboards and PR annotation tooling.

Capture a timestamped history snapshot:

```bash
scripts/perf/capture_snapshot.sh --tier quick --iters 10 --label local
scripts/perf/capture_snapshot.sh --tier stress --iters 3 --max-cases 8 --label nightly
```

Import downloaded CI artifacts into local history:

```bash
scripts/perf/import_artifacts_snapshot.sh \
  --name quick_run_1234 \
  --from perf-artifacts

scripts/perf/prune_history.sh \
  --history-dir perf/history \
  --keep-last 60 \
  --apply
```

Trend analysis across snapshots:

```bash
cargo run --release --bin perf_corpus_trend -- --history-dir perf/history --source all --metric all
cargo run --release --bin perf_corpus_trend -- --history-dir perf/history --source probe --metric p95 --top 20
cargo run --release --bin perf_corpus_trend -- --history-dir perf/history --env-compat fail
cargo run --release --bin perf_corpus_trend -- --history-dir perf/history --fail-regressions-pct 10 --min-regression-confidence 1.5
scripts/perf/trend.sh --source gate --metric median --top 30
```

`--env-compat` controls cross-snapshot environment checks:
- `warn` (default): print mismatch warning and continue.
- `fail`: exit non-zero when snapshot environments differ.
- `off`: skip environment-compat checks.

Trend regression gate on recent snapshots:

```bash
cargo run --release --bin perf_corpus_trend -- \
  --history-dir perf/history \
  --window 2 \
  --source all \
  --metric median \
  --fail-regressions-pct 10

scripts/perf/trend_gate.sh
```

`perf_corpus_trend` exits non-zero when `--fail-regressions-pct` is set and at least one row exceeds the effective threshold with sufficient regression confidence.
Effective threshold is noise-aware: base threshold plus any variance above per-case `noise_target_cv_pct`.

Periodic corpus-health audit:

```bash
cargo run --release --bin perf_corpus_health -- --history-dir perf/history --source all --window 30
cargo run --release --bin perf_corpus_health -- --history-dir perf/history --source all --window 30 --json
scripts/perf/health_audit.sh
```

`perf_corpus_health` reports:
- stale cases (insufficient history points or absent from latest snapshot)
- noisy cases (CV above threshold)
- redundant pairs (highly correlated case series within the same source/metric)

Flamegraph a specific case:

```bash
scripts/perf/flamegraph_case.sh recursive_add_forward_n8 40
```

## Adding a New Case

1. Add a new `[[case]]` entry in `benches/perf_corpus_cases.toml`.
2. Choose the right `tier` and `category`.
3. Choose a run mode matching intended behavior:
   - finite query: `Exhaust`
   - streaming/infinite query: `FirstN(k)` or `FirstAnswer`
4. Set `expected_kind` + `expected_value` so invalid cases fail fast.
5. Keep the case semantics-focused and representative of a real workload pattern.
6. Use template directives where helpful:
   - `{{PEANO:n}}`
   - `{{NESTED:base:depth}}`
   - `{{OR_PROGRAM:n}}`
   - `{{CHAIN_PROGRAM:n}}`
   - `{{CHAIN_QUERY:n}}`
   - `{{PROGRAM_ADD}}`, `{{PROGRAM_EVEN_ODD}}`, `{{PROGRAM_EQ_NEQ}}`, `{{PROGRAM_RANGES}}`, `{{PROGRAM_PEEL}}`, `{{PROGRAM_TREECALC}}`
7. Annotate `determinism`, `answer_shape`, and `infinite_stream` for all new cases.
8. For `quick` tier cases, set `quick_gate_max_median_us` and `quick_gate_max_p95_us`.
9. For `quick` tier cases, set noise/adaptive metadata:
   - `noise_target_cv_pct`, `noise_flaky_cv_pct`
   - `adaptive_min_samples`, `adaptive_max_samples`

## Case Design Rules

1. Prefer semantic workload patterns over implementation-internal artifacts.
2. Avoid synthetic micro-cases unless they isolate a known bottleneck.
3. Include both finite and streaming query behavior.
4. Include both rule-only and theory/constraint paths.
5. Keep query text readable and reproducible.
6. Put heavy cases in `stress` unless they are core daily checks.

## Gate and CI

Quick-tier gating is configured in:

- `perf/quick_gate.toml` (sampling/warmup/tolerance policy)
- `benches/perf_corpus_cases.toml` (canonical per-case quick thresholds)
- `src/bin/perf_corpus_gate.rs` (gate runner)
- `src/bin/perf_corpus_recommend_gate.rs` (threshold recommendation helper)
- `src/bin/perf_corpus_ci_summary.rs` (artifact-to-markdown summarizer)
- `src/bin/perf_corpus_trend.rs` (historical trend analysis)
- `.github/workflows/perf-corpus-quick.yml` (CI workflow)
- `.github/workflows/perf-corpus-stress-nightly.yml` (nightly stress + artifacts)
- `scripts/perf/capture_snapshot.sh` (local snapshot capture into `perf/history/`)
- `scripts/perf/import_artifacts_snapshot.sh` (import CI artifact bundle into history)
- `scripts/perf/prune_history.sh` (history retention/pruning)
- `scripts/perf/trend.sh` (wrapper for local trend analysis)
- `scripts/perf/trend_gate.sh` (history-based slowdown gate wrapper)
- `scripts/perf/health_audit.sh` (history-based stale/noisy/redundant audit wrapper)

Run locally:

```bash
cargo run --release --bin perf_corpus_gate
```

## Governance Docs

- Baseline lifecycle: `perf/BASELINE_POLICY.md`
- Corpus ownership and threshold policy: `perf/OWNERSHIP_AND_THRESHOLDS.md`
- Case PR checklist: `perf/CASE_CHANGE_CHECKLIST.md`
- Periodic review checklist: `perf/PERIODIC_REVIEW_CHECKLIST.md`
- Gate/trend failure runbook: `perf/GATE_TREND_RUNBOOK.md`

## Notes

- Criterion baseline comparison data lives under `target/criterion`.
- `perf_corpus_diff` reads `target/criterion/**/change/estimates.json`, so run a baseline comparison first.
- Structured outputs include an environment fingerprint (OS/arch/CPU/rustc/RUSTFLAGS/timestamp + git SHA + CI/run metadata when available).
