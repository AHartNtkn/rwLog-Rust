# Performance Baseline Lifecycle Policy

## Scope

This policy governs Criterion baseline snapshots used by:

- `scripts/perf/save_baseline.sh`
- `scripts/perf/compare_baseline.sh`
- `src/bin/perf_corpus_diff.rs`

## Baseline Sources

- `main`: primary team baseline used for day-to-day PR checks.
- `release/*`: optional release hardening baselines.
- feature branches: temporary local-only baselines for investigation.

## Refresh Cadence

- Refresh `main` baseline weekly.
- Refresh `main` baseline immediately after large expected performance shifts.
- Refresh release baselines only during release stabilization windows.

## Ownership

- Primary owner: performance corpus maintainers.
- Backup owner: on-call release engineer for urgent regressions.

## PR Policy

- Do not refresh baseline in the same PR that introduces performance-risky logic unless explicitly required.
- If baseline refresh is required, include:
  - before/after corpus diff summary
  - reason for expected shift
  - case-level deltas with threshold impact
- Separate "logic change" and "baseline refresh" commits when possible.

## Regression Triage

- First compare against current baseline without refreshing.
- If regression is real, fix or justify with explicit tradeoff analysis.
- Only refresh baseline after regression is understood and accepted.

## Retention

- Keep baseline artifacts for at least 30 days in CI artifact storage.
- For releases, keep artifacts until end-of-life for that release line.
