#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/perf/prune_history.sh [options]

Options:
  --history-dir <PATH>       Snapshot history directory (default: perf/history)
  --keep-last <N>            Keep newest N snapshots (default: 30)
  --apply                    Delete selected old snapshots (default: dry-run)
  --json                     Emit JSON summary
  -h, --help                 Show this help

Environment overrides:
  RWLOG_PERF_HISTORY_DIR
  RWLOG_PERF_KEEP_LAST

Notes:
  - Snapshot directories are ordered lexicographically by name.
  - Without --apply, this command only reports what would be deleted.
EOF
}

history_dir="${RWLOG_PERF_HISTORY_DIR:-perf/history}"
keep_last="${RWLOG_PERF_KEEP_LAST:-30}"
apply=0
json=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --history-dir)
      history_dir="${2:-}"
      shift 2
      ;;
    --keep-last)
      keep_last="${2:-}"
      shift 2
      ;;
    --apply)
      apply=1
      shift
      ;;
    --json)
      json=1
      shift
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

if ! [[ "$keep_last" =~ ^[0-9]+$ ]]; then
  echo "--keep-last must be a non-negative integer (got '$keep_last')" >&2
  exit 2
fi

if [[ ! -d "$history_dir" ]]; then
  echo "history dir does not exist: $history_dir" >&2
  exit 2
fi

mapfile -t dirs < <(find "$history_dir" -mindepth 1 -maxdepth 1 -type d -printf '%f\n' | sort)
total="${#dirs[@]}"
keep_count="$keep_last"
if [[ "$keep_count" -gt "$total" ]]; then
  keep_count="$total"
fi
delete_count=$(( total - keep_count ))

to_delete=()
to_keep=()
if [[ "$delete_count" -gt 0 ]]; then
  for ((i = 0; i < delete_count; i++)); do
    to_delete+=("${dirs[$i]}")
  done
fi
for ((i = delete_count; i < total; i++)); do
  to_keep+=("${dirs[$i]}")
done

deleted=()
if [[ "$apply" -eq 1 ]]; then
  for name in "${to_delete[@]}"; do
    rm -rf -- "$history_dir/$name"
    deleted+=("$name")
  done
fi

json_escape() {
  local s="$1"
  s="${s//\\/\\\\}"
  s="${s//\"/\\\"}"
  s="${s//$'\n'/\\n}"
  s="${s//$'\r'/\\r}"
  s="${s//$'\t'/\\t}"
  printf '%s' "$s"
}

json_array() {
  local -n arr_ref="$1"
  printf '['
  local first=1
  for item in "${arr_ref[@]}"; do
    if [[ "$first" -eq 0 ]]; then
      printf ','
    fi
    first=0
    printf '"%s"' "$(json_escape "$item")"
  done
  printf ']'
}

if [[ "$json" -eq 1 ]]; then
  printf '{\n'
  printf '  "history_dir": "%s",\n' "$(json_escape "$history_dir")"
  printf '  "total_snapshots": %s,\n' "$total"
  printf '  "keep_last": %s,\n' "$keep_last"
  printf '  "delete_count": %s,\n' "$delete_count"
  printf '  "applied": %s,\n' "$( [[ "$apply" -eq 1 ]] && echo "true" || echo "false" )"
  printf '  "would_delete": '
  json_array to_delete
  printf ',\n'
  printf '  "deleted": '
  json_array deleted
  printf ',\n'
  printf '  "kept": '
  json_array to_keep
  printf '\n}\n'
  exit 0
fi

echo "Perf history prune:"
echo "  history_dir=$history_dir"
echo "  total_snapshots=$total keep_last=$keep_last delete_count=$delete_count applied=$apply"
if [[ "$delete_count" -gt 0 ]]; then
  echo "  to_delete:"
  for name in "${to_delete[@]}"; do
    echo "    - $name"
  done
else
  echo "  to_delete: <none>"
fi

