#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-.}"
OUT="${2:-stitched.rs}"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: rg (ripgrep) is required" >&2
  exit 1
fi

OUT_ABS=$(python - "$OUT" <<'PY'
import os, sys
print(os.path.abspath(sys.argv[1]))
PY
)

mapfile -t files < <(
  rg --files "$ROOT" \
    -g '*.rs' \
    -g '!target/**' \
    -g '!benches/**' \
    -g '!examples/**' \
    -g '!tests/**' \
    -g '!src/bin/**' \
    -g '!src/jupyter.rs' \
    -g '!src/test_utils.rs' \
    -g '!src/repl.rs' \
    -g '!src/metrics.rs' \
    -g '!src/trace.rs' \
    -g '!**/tests/**' \
    -g '!**/tests.rs' \
  | sort
)

: > "$OUT"
for f in "${files[@]}"; do
  f_abs=$(python - "$f" <<'PY'
import os, sys
print(os.path.abspath(sys.argv[1]))
PY
)
  if [[ "$f_abs" == "$OUT_ABS" ]]; then
    continue
  fi
  printf "// ===== %s =====\n" "${f#./}" >> "$OUT"
  cat "$f" >> "$OUT"
  printf "\n\n" >> "$OUT"
done
