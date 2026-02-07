#!/usr/bin/env bash
set -euo pipefail

history_dir="${RWLOG_PERF_HISTORY_DIR:-perf/history}"
source_filter="${RWLOG_HEALTH_SOURCE:-all}"
window="${RWLOG_HEALTH_WINDOW:-30}"
min_points="${RWLOG_HEALTH_MIN_POINTS:-3}"
noisy_cv_pct="${RWLOG_HEALTH_NOISY_CV_PCT:-25}"
redundancy_corr_min="${RWLOG_HEALTH_REDUNDANCY_CORR_MIN:-0.995}"
top_redundant="${RWLOG_HEALTH_TOP_REDUNDANT:-50}"

if [[ "$#" -gt 0 ]]; then
  cargo run --release --bin perf_corpus_health -- "$@"
  exit 0
fi

cargo run --release --bin perf_corpus_health -- \
  --history-dir "$history_dir" \
  --source "$source_filter" \
  --window "$window" \
  --min-points "$min_points" \
  --noisy-cv-pct "$noisy_cv_pct" \
  --redundancy-corr-min "$redundancy_corr_min" \
  --top-redundant "$top_redundant"
