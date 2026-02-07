#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/perf/capture_snapshot.sh [options]

Options:
  --tier <quick|stress>      Corpus tier to capture (default: quick)
  --iters <N>                Probe iterations for perf_corpus_run (default: 10 quick, 3 stress)
  --max-cases <N>            Optional RWLOG_CORPUS_MAX_CASES for probe run
  --history-dir <PATH>       Snapshot history directory (default: perf/history)
  --label <TEXT>             Optional suffix for snapshot directory name
  -h, --help                 Show this help

Environment overrides:
  RWLOG_CORPUS_TIER
  RWLOG_CORPUS_ITERS
  RWLOG_CORPUS_MAX_CASES
  RWLOG_PERF_HISTORY_DIR

Snapshot output:
  <history-dir>/<timestamp>_<tier>[_label]/
    sanity.json
    gate.json                 # quick tier only
    probe.json
    summary.md
    perf_corpus_cases.toml
    quick_gate.toml           # when present
    git_sha.txt               # when available
EOF
}

tier="${RWLOG_CORPUS_TIER:-quick}"
iters="${RWLOG_CORPUS_ITERS:-}"
max_cases="${RWLOG_CORPUS_MAX_CASES:-}"
history_dir="${RWLOG_PERF_HISTORY_DIR:-perf/history}"
label=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --tier)
      tier="${2:-}"
      shift 2
      ;;
    --iters)
      iters="${2:-}"
      shift 2
      ;;
    --max-cases)
      max_cases="${2:-}"
      shift 2
      ;;
    --history-dir)
      history_dir="${2:-}"
      shift 2
      ;;
    --label)
      label="${2:-}"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "Unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [[ "$tier" != "quick" && "$tier" != "stress" ]]; then
  echo "--tier must be quick or stress (got '$tier')" >&2
  exit 2
fi

if [[ -z "$iters" ]]; then
  if [[ "$tier" == "quick" ]]; then
    iters=10
  else
    iters=3
  fi
fi

if ! [[ "$iters" =~ ^[0-9]+$ ]] || [[ "$iters" -eq 0 ]]; then
  echo "--iters must be a positive integer (got '$iters')" >&2
  exit 2
fi

if [[ -n "$max_cases" ]] && { ! [[ "$max_cases" =~ ^[0-9]+$ ]] || [[ "$max_cases" -eq 0 ]]; }; then
  echo "--max-cases must be a positive integer when set (got '$max_cases')" >&2
  exit 2
fi

stamp="$(date -u +%Y%m%dT%H%M%SZ)"
safe_label="$(printf '%s' "$label" | tr -cs '[:alnum:]_-' '_' | sed -E 's/^_+//; s/_+$//')"
snap_dir="${history_dir}/${stamp}_${tier}"
if [[ -n "$safe_label" ]]; then
  snap_dir="${snap_dir}_${safe_label}"
fi

mkdir -p "$snap_dir"

echo "Capturing perf corpus snapshot:"
echo "  tier=$tier iters=$iters max_cases=${max_cases:-<none>}"
echo "  output=$snap_dir"

RWLOG_CORPUS_TIER="$tier" cargo run --release --bin perf_corpus_sanity -- --lint --validate --json > "$snap_dir/sanity.json"

if [[ "$tier" == "quick" ]]; then
  cargo run --release --bin perf_corpus_gate -- --json > "$snap_dir/gate.json"
fi

if [[ -n "$max_cases" ]]; then
  RWLOG_CORPUS_TIER="$tier" RWLOG_CORPUS_MAX_CASES="$max_cases" \
    cargo run --release --bin perf_corpus_run -- --phase end_to_end --iters "$iters" --json > "$snap_dir/probe.json"
else
  RWLOG_CORPUS_TIER="$tier" \
    cargo run --release --bin perf_corpus_run -- --phase end_to_end --iters "$iters" --json > "$snap_dir/probe.json"
fi

summary_args=(
  --title "Perf Corpus Snapshot (${tier})"
  --sanity-json "$snap_dir/sanity.json"
  --probe-json "$snap_dir/probe.json"
  --out "$snap_dir/summary.md"
)
if [[ "$tier" == "quick" ]]; then
  summary_args+=(--gate-json "$snap_dir/gate.json")
fi
cargo run --release --bin perf_corpus_ci_summary -- "${summary_args[@]}"

cp benches/perf_corpus_cases.toml "$snap_dir/perf_corpus_cases.toml"
if [[ -f perf/quick_gate.toml ]]; then
  cp perf/quick_gate.toml "$snap_dir/quick_gate.toml"
fi
if git rev-parse HEAD >/dev/null 2>&1; then
  git rev-parse HEAD > "$snap_dir/git_sha.txt"
fi

echo "Snapshot complete: $snap_dir"
