#!/usr/bin/env bash
set -euo pipefail

name="${1:-}"
if [[ -z "$name" ]]; then
  echo "Usage: $0 <baseline-name> [extra criterion args...]" >&2
  echo "Env: RWLOG_PERF_BENCH_SHARDS (comma list or 'all')" >&2
  echo "Env: RWLOG_CRITERION_SAMPLE_SIZE (default: 30 if not passed)" >&2
  echo "Env: RWLOG_CRITERION_NO_PLOT_DEFAULT (default: 1)" >&2
  exit 2
fi
shift || true

criterion_args=("$@")

has_flag() {
  local flag="$1"
  local arg
  for arg in "${criterion_args[@]}"; do
    if [[ "$arg" == "$flag" || "$arg" == "$flag="* ]]; then
      return 0
    fi
  done
  return 1
}

if ! has_flag "--sample-size"; then
  criterion_args+=("--sample-size" "${RWLOG_CRITERION_SAMPLE_SIZE:-30}")
fi

if [[ "${RWLOG_CRITERION_NO_PLOT_DEFAULT:-1}" == "1" ]] && ! has_flag "--noplot"; then
  criterion_args+=("--noplot")
fi

shards_raw="${RWLOG_PERF_BENCH_SHARDS:-corpus_parse,corpus_execute_first_answer,corpus_execute_first_n,corpus_execute_exhaust,corpus_end_to_end_first_answer,corpus_end_to_end_first_n,corpus_end_to_end_exhaust}"

if [[ "$shards_raw" == "all" ]]; then
  echo "==> saving baseline '${name}' in single process"
  cargo bench --bench perf_corpus -- --save-baseline "$name" "${criterion_args[@]}"
  exit 0
fi

IFS=',' read -r -a shards <<< "$shards_raw"
failed=()

for raw_shard in "${shards[@]}"; do
  shard="${raw_shard//[[:space:]]/}"
  if [[ -z "$shard" ]]; then
    continue
  fi
  echo "==> saving baseline '${name}' shard='${shard}'"
  if ! cargo bench --bench perf_corpus -- "$shard" --save-baseline "$name" "${criterion_args[@]}"; then
    failed+=("$shard")
  fi
done

if (( ${#failed[@]} > 0 )); then
  echo "baseline save failed for shard(s): ${failed[*]}" >&2
  exit 1
fi
