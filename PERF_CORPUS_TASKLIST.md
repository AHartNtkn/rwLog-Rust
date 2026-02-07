# Performance Corpus Completion Task List

This is the implementation tracker for making the corpus feature “complete enough” for ongoing optimization work.

## Phase 1: Foundation and Policy

- [x] Shared corpus module used by benches and utilities (`src/perf_corpus.rs`)
- [x] Machine-readable corpus file with case metadata (`benches/perf_corpus_cases.toml`)
- [x] Quick/stress tier split with filterable selection
- [x] Dedicated sanity command (`perf_corpus_sanity`)
- [x] Schema versioning and strict corpus linting
- [x] Corpus policy checks (minimum tier/category coverage; realistic-case requirements)
- [x] Enforce required metadata quality (non-empty tags, descriptions, consistency checks)

## Phase 2: Measurement and Visibility

- [x] Parse / execute / end-to-end measurement separation
- [x] Mode-partitioned bench groups (`first_answer`, `first_n`, `exhaust`)
- [x] Case-level runner with median/p95 (`perf_corpus_run`)
- [x] Allocation visibility command (`perf_corpus_alloc`)
- [x] Structured JSON/CSV output for runners (sanity/run/alloc/gate)
- [x] Environment fingerprint capture in structured outputs (OS/arch/rustc/time/run metadata)
- [x] Include engine internal counters (steps/backtracks/compose/meet attempts) in tool outputs

## Phase 3: Baselines and Regression Control

- [x] Baseline save/compare scripts
- [x] Criterion change parser and threshold checker (`perf_corpus_diff`)
- [x] Quick gate config and runner (`perf/quick_gate.toml`, `perf_corpus_gate`)
- [x] Per-case thresholds in one canonical source and validation of gate config completeness
- [x] Explicit baseline lifecycle docs (refresh cadence, ownership, and PR policy)

## Phase 4: Reproducibility and CI

- [x] Pinned environment helper script (`scripts/perf/pinned_env.sh`)
- [x] Quick-tier CI workflow (`.github/workflows/perf-corpus-quick.yml`)
- [x] Nightly stress workflow with artifact upload
- [x] CI markdown summary artifact/report generation for quick gate and nightly stress
- [x] Environment fingerprint capture in run outputs (CPU/rustc/RUSTFLAGS/git SHA)

## Phase 5: Governance and Maintenance

- [x] Corpus architecture docs (`PERF_CORPUS.md`)
- [x] README discoverability section
- [x] Corpus ownership and threshold-change policy docs
- [x] Case change template/checklist for PRs
- [x] Periodic corpus review checklist (deprecate noisy cases, add realistic gaps)

## Phase 6: Historical Analysis and Threshold Maintenance

- [x] Gate threshold recommender apply mode (`perf_corpus_recommend_gate --apply`)
- [x] Historical trend analyzer (`perf_corpus_trend`)
- [x] Local snapshot capture script (`scripts/perf/capture_snapshot.sh`)
- [x] CI artifact import script (`scripts/perf/import_artifacts_snapshot.sh`)
- [x] Trend wrapper script (`scripts/perf/trend.sh`)
- [x] Trend regression gate wrapper (`scripts/perf/trend_gate.sh`)
- [x] Trend tool supports history windowing and threshold-based non-zero exit
- [x] Usage docs for apply mode and history/trend workflow

## Phase 7: V2 Hardening (No Ownership/Codeowners Scope)

- [x] Add integration tests for all perf binaries (`perf_corpus_sanity`, `perf_corpus_run`, `perf_corpus_alloc`, `perf_corpus_gate`, `perf_corpus_recommend_gate`, `perf_corpus_trend`, `perf_corpus_ci_summary`, `perf_corpus_diff`)
- [x] Add script-level integration tests for snapshot/trend workflow (`capture_snapshot.sh`, `import_artifacts_snapshot.sh`, `trend.sh`, `trend_gate.sh`)
- [x] Add fixture-based compatibility tests for JSON/CSV outputs (schema stability + parse-back checks)
- [x] Harden file writes for mutating tools (`perf_corpus_recommend_gate --apply`, artifact import) with atomic-write semantics
- [x] Add noise-aware regression checks (confidence intervals or robust variance gates) in addition to simple `% delta` thresholds
- [x] Add case-level noise metadata and flaky-case detection/reporting
- [x] Add adaptive sampling for noisy cases in gate/trend checks
- [x] Enforce compare-with-like environment checks for history/trend analysis (warn/fail on mismatched CPU/arch/rustc unless explicitly overridden)
- [x] Add retention/pruning tooling for `perf/history` snapshots
- [x] Add machine-readable status output suitable for CI dashboards/PR annotations
- [x] Wire trend regression gate into CI as an enforceable check
- [x] Add automated periodic corpus-health audit output (stale/noisy/redundant case detection)
- [x] Add failure recovery runbook for perf gate/trend regressions (triage flow, rerun commands, threshold-adjust policy)

## V2 Done Criteria

1. No flaky quick-gate/trend-gate failures across repeated CI runs on unchanged code.
2. Full integration-test coverage for perf binaries and scripts listed in Phase 7.
3. Trend regression gate is enforced in CI with clear failure diagnostics.
4. Runbooks exist for gate/trend failures and are validated by dry-run drills.

## Current Work Order

1. Execute Phase 7 V2 hardening tasks.
2. Continue using new bottleneck findings and CI signal quality to prioritize within Phase 7.
