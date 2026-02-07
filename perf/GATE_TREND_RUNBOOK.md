# Perf Gate and Trend Failure Runbook

This runbook is for failures from:

- `perf_corpus_gate`
- `perf_corpus_trend --fail-regressions-pct ...`
- `scripts/perf/trend_gate.sh`

## 1. Classify the Failure

1. Capture artifacts (`*_sanity.json`, `*_gate.json`, `*_probe.json`, `*_trend.json`, summary markdown).
2. Check whether this is:
   - quick gate budget breach (`gate.failed = true`)
   - trend regression threshold breach (non-zero regressions over threshold)
   - environment mismatch (`env_mismatch_fields` non-empty, especially in `--env-compat fail` mode)
3. Confirm corpus scope and config used in CI:
   - tier/filter env vars
   - `perf/quick_gate.toml`
   - history window / threshold values passed to trend gate

## 2. Reproduce Locally (Pinned Environment)

Run in repo root:

```bash
scripts/perf/pinned_env.sh cargo test --no-run
scripts/perf/pinned_env.sh timeout 30 cargo test
scripts/perf/pinned_env.sh cargo run --release --bin perf_corpus_sanity -- --lint --validate --json > /tmp/sanity.json
scripts/perf/pinned_env.sh cargo run --release --bin perf_corpus_gate -- --json > /tmp/gate.json
scripts/perf/pinned_env.sh cargo run --release --bin perf_corpus_run -- --phase end_to_end --iters 10 --json > /tmp/probe.json
scripts/perf/pinned_env.sh cargo run --release --bin perf_corpus_trend -- --history-dir perf/history --source all --metric median --window 20 --fail-regressions-pct 10 --json > /tmp/trend.json
```

If local reproduction is unstable, run the same command 3-5 times and compare median/p95 variance before changing thresholds.

## 3. Triage Decision

Use this decision policy:

1. If failure reproduces consistently and has semantic cause (new algorithm/code path): treat as real regression, fix code first.
2. If failure does not reproduce and environment differs: treat as measurement noise or environment drift, fix environment comparability first.
3. If failure is isolated to one historically noisy case: collect repeated measurements and evaluate whether case should be marked noisy or sampled more deeply.
4. If multiple unrelated cases regress together: suspect global effects (allocator, parser path, normalization changes, compiler flags).

## 4. Rerun Commands for Confirm/Refute

```bash
# quick gate
cargo run --release --bin perf_corpus_gate -- --json

# targeted probe reruns
RWLOG_CORPUS_FILTER=<case_id> cargo run --release --bin perf_corpus_run -- --phase end_to_end --iters 20 --json

# trend with stricter environment checks
cargo run --release --bin perf_corpus_trend -- --history-dir perf/history --env-compat fail --source all --metric median --window 20 --json
```

## 5. Threshold Adjustment Policy

Threshold changes are allowed only when all are true:

1. No semantic/code regression can be identified.
2. Repeated runs show stable measurements around the new level.
3. The adjustment is minimal and justified in PR notes.
4. `perf_corpus_recommend_gate` output is reviewed, not auto-accepted blindly.

Recommended flow:

```bash
cargo run --release --bin perf_corpus_recommend_gate -- --headroom-pct 20 --json > /tmp/recommend.json
cp benches/perf_corpus_cases.toml /tmp/perf_corpus_cases.toml
cargo run --release --bin perf_corpus_recommend_gate -- --headroom-pct 20 --apply --apply-file /tmp/perf_corpus_cases.toml --json
```

Review diffs case-by-case before applying to `benches/perf_corpus_cases.toml`.

## 6. Post-Incident Hygiene

1. Import CI artifacts into local history.
2. Re-run trend to ensure no unresolved regressions:

```bash
scripts/perf/import_artifacts_snapshot.sh --name <snapshot_name> --from <artifact_dir>
scripts/perf/trend.sh --source all --metric all --window 20 --top 200
```

3. Prune history to retention target:

```bash
scripts/perf/prune_history.sh --history-dir perf/history --keep-last 60 --apply
```

4. Add/adjust corpus case metadata or sampling policy if recurring noise is observed.
