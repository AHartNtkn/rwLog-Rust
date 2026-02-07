#!/usr/bin/env bash
set -euo pipefail

history_dir="${RWLOG_PERF_HISTORY_DIR:-perf/history}"
threshold_pct="${RWLOG_TREND_REGRESSION_PCT:-10}"
window="${RWLOG_TREND_WINDOW:-2}"
source_filter="${RWLOG_TREND_SOURCE:-all}"
metric_filter="${RWLOG_TREND_METRIC:-median}"
top="${RWLOG_TREND_TOP:-50}"
min_confidence="${RWLOG_TREND_MIN_CONFIDENCE:-1.0}"
default_noise_target_cv_pct="${RWLOG_TREND_DEFAULT_NOISE_TARGET_CV_PCT:-35.0}"

if [[ "$#" -gt 0 ]]; then
  cargo run --release --bin perf_corpus_trend -- "$@"
  exit 0
fi

cargo run --release --bin perf_corpus_trend -- \
  --history-dir "$history_dir" \
  --source "$source_filter" \
  --metric "$metric_filter" \
  --window "$window" \
  --top "$top" \
  --min-regression-confidence "$min_confidence" \
  --default-noise-target-cv-pct "$default_noise_target_cv_pct" \
  --fail-regressions-pct "$threshold_pct"
