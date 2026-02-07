#!/usr/bin/env bash
set -euo pipefail

history_dir="${RWLOG_PERF_HISTORY_DIR:-perf/history}"

has_history_arg=0
for arg in "$@"; do
  if [[ "$arg" == "--history-dir" || "$arg" == --history-dir=* ]]; then
    has_history_arg=1
    break
  fi
done

if [[ "$has_history_arg" -eq 1 ]]; then
  cargo run --release --bin perf_corpus_trend -- "$@"
  exit 0
fi

cargo run --release --bin perf_corpus_trend -- \
  --history-dir "$history_dir" \
  --min-regression-confidence "${RWLOG_TREND_MIN_CONFIDENCE:-1.0}" \
  --default-noise-target-cv-pct "${RWLOG_TREND_DEFAULT_NOISE_TARGET_CV_PCT:-35.0}" \
  "$@"
