#!/usr/bin/env bash
set -euo pipefail

case_id="${1:-}"
iters="${2:-30}"
if [[ -z "$case_id" ]]; then
  echo "Usage: $0 <case-id-substring> [iters]" >&2
  exit 2
fi

if ! command -v perf >/dev/null 2>&1; then
  echo "perf is required" >&2
  exit 2
fi
if ! command -v inferno-collapse-perf >/dev/null 2>&1 || ! command -v inferno-flamegraph >/dev/null 2>&1; then
  echo "inferno tools are required: inferno-collapse-perf, inferno-flamegraph" >&2
  exit 2
fi

out="flamegraph_${case_id}_$(date +%Y%m%d_%H%M%S).svg"
perf record -g -- \
  cargo run --release --bin perf_corpus_run -- --id "$case_id" --phase execute --iters "$iters"
perf script | inferno-collapse-perf | inferno-flamegraph > "$out"
echo "wrote $out"
