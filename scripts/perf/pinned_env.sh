#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -eq 0 ]]; then
  echo "Usage: $0 <command...>" >&2
  exit 2
fi

export CARGO_INCREMENTAL=0
export RUSTFLAGS="${RUSTFLAGS:-} -Ccodegen-units=1"
export RWLOG_PERF_RUN_ID="${RWLOG_PERF_RUN_ID:-$(date +%Y%m%d_%H%M%S)}"

if command -v taskset >/dev/null 2>&1; then
  cpu="${RWLOG_PERF_CPU:-0}"
  exec taskset -c "$cpu" "$@"
else
  exec "$@"
fi
