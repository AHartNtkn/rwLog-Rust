#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/perf/import_artifacts_snapshot.sh --name <snapshot_name> --from <artifact_dir> [--history-dir <path>]

Expected files in <artifact_dir>:
  quick_sanity.json or stress_sanity.json
  quick_gate.json (optional)
  quick_probe.json or stress_probe.json
  *_summary.md (optional)
EOF
}

name=""
from_dir=""
history_dir="${RWLOG_PERF_HISTORY_DIR:-perf/history}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --name)
      name="${2:-}"
      shift 2
      ;;
    --from)
      from_dir="${2:-}"
      shift 2
      ;;
    --history-dir)
      history_dir="${2:-}"
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

if [[ -z "$name" || -z "$from_dir" ]]; then
  usage >&2
  exit 2
fi

if [[ ! -d "$from_dir" ]]; then
  echo "artifact directory not found: $from_dir" >&2
  exit 2
fi

if [[ "$name" =~ [^[:alnum:]_.-] ]]; then
  echo "--name may only contain letters, numbers, '_', '-', '.'" >&2
  exit 2
fi

dest="${history_dir}/${name}"
if [[ -e "$dest" ]]; then
  echo "destination already exists: $dest" >&2
  exit 2
fi

mkdir -p "$history_dir"
staging="${history_dir}/.${name}.tmp.$$"
cleanup() {
  rm -rf "$staging"
}
trap cleanup EXIT
mkdir -p "$staging"

if [[ -f "$from_dir/quick_sanity.json" ]]; then
  cp "$from_dir/quick_sanity.json" "$staging/sanity.json"
elif [[ -f "$from_dir/stress_sanity.json" ]]; then
  cp "$from_dir/stress_sanity.json" "$staging/sanity.json"
else
  echo "missing sanity json in $from_dir" >&2
  exit 2
fi

if [[ -f "$from_dir/quick_gate.json" ]]; then
  cp "$from_dir/quick_gate.json" "$staging/gate.json"
fi

if [[ -f "$from_dir/quick_probe.json" ]]; then
  cp "$from_dir/quick_probe.json" "$staging/probe.json"
elif [[ -f "$from_dir/stress_probe.json" ]]; then
  cp "$from_dir/stress_probe.json" "$staging/probe.json"
else
  echo "missing probe json in $from_dir" >&2
  exit 2
fi

if [[ -f "$from_dir/quick_summary.md" ]]; then
  cp "$from_dir/quick_summary.md" "$staging/summary.md"
elif [[ -f "$from_dir/stress_summary.md" ]]; then
  cp "$from_dir/stress_summary.md" "$staging/summary.md"
fi

mv "$staging" "$dest"
trap - EXIT

echo "Imported snapshot: $dest"
