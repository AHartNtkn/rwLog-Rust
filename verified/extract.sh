#!/usr/bin/env bash
# Regenerate lean/RwlogCore from rust/src with Charon and Aeneas.
#
# Needs `charon` and `aeneas` on PATH, built from the Aeneas commit pinned in
# lean/lakefile.toml (and the Charon commit in that checkout's `charon-pin`).
# The generated files are committed; the Lean build does not need the tools.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
cd "$here/rust"
charon cargo --preset=aeneas --dest-file "$here/rust/target/rwlog_core.llbc"
aeneas -backend lean "$here/rust/target/rwlog_core.llbc" \
  -dest "$here/lean/RwlogCore" -split-files -no-progress-bar
