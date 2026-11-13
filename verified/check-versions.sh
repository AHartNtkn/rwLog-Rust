#!/usr/bin/env bash
# Check that every file that names a version agrees with versions.env, and
# that the recorded versions are the ones the recorded Aeneas commit asks for.
#
# Needs `git` and `jq`, and network access to fetch the Aeneas commit.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/.." && pwd)"
# shellcheck source=versions.env
. "$here/versions.env"

failed=0
expect() { # expect <what> <found> <recorded>
  if [[ "$2" != "$3" ]]; then
    echo "MISMATCH: $1 is '$2', versions.env records '$3'"
    failed=1
  else
    echo "ok: $1 is $2"
  fi
}

# The revision a lakefile.toml requires for a package.
required_rev() { # required_rev <lakefile.toml> <package>
  awk -v pkg="$2" '
    /^\[\[/ { in_pkg = 0 }
    $0 == "name = \"" pkg "\"" { in_pkg = 1 }
    in_pkg && /^rev = / { gsub(/^rev = "|"$/, ""); print }
  ' "$1"
}
# A field of a package's entry in a lake-manifest.json.
manifest() { # manifest <lake-manifest.json> <package> <field>
  jq -r --arg p "$2" --arg f "$3" '.packages[] | select(.name == $p) | .[$f]' "$1"
}

lean="leanprover/lean4:$LEAN_VERSION"
expect "lean/lean-toolchain" "$(cat "$root/lean/lean-toolchain")" "$lean"
expect "verified/lean/lean-toolchain" "$(cat "$root/verified/lean/lean-toolchain")" "$lean"
expect "mathlib in lean/lakefile.toml" \
  "$(required_rev "$root/lean/lakefile.toml" mathlib)" "$MATHLIB_VERSION"
expect "mathlib in lean/lake-manifest.json" \
  "$(manifest "$root/lean/lake-manifest.json" mathlib inputRev)" "$MATHLIB_VERSION"
expect "mathlib in verified/lean/lake-manifest.json" \
  "$(manifest "$root/verified/lean/lake-manifest.json" mathlib inputRev)" "$MATHLIB_VERSION"
expect "the mathlib commit in verified/lean/lake-manifest.json" \
  "$(manifest "$root/verified/lean/lake-manifest.json" mathlib rev)" \
  "$(manifest "$root/lean/lake-manifest.json" mathlib rev)"
expect "aeneas in verified/lean/lakefile.toml" \
  "$(required_rev "$root/verified/lean/lakefile.toml" aeneas)" "$AENEAS_COMMIT"
expect "aeneas in verified/lean/lake-manifest.json" \
  "$(manifest "$root/verified/lean/lake-manifest.json" aeneas rev)" "$AENEAS_COMMIT"

# What the recorded Aeneas commit itself asks for.
aeneas="$(mktemp -d)"
trap 'rm -rf "$aeneas"' EXIT
git -C "$aeneas" init -q
git -C "$aeneas" fetch -q --depth 1 https://github.com/AeneasVerif/aeneas "$AENEAS_COMMIT"
show() { git -C "$aeneas" show "FETCH_HEAD:$1"; }
expect "the Charon commit in Aeneas's charon-pin" \
  "$(show charon-pin | tail -n 1)" "$CHARON_COMMIT"
expect "the Charon commit in Aeneas's flake.lock" \
  "$(show flake.lock | jq -r .nodes.charon.locked.rev)" "$CHARON_COMMIT"
expect "the Lean version of Aeneas's Lean library" \
  "$(show backends/lean/lean-toolchain)" "$lean"
expect "the mathlib version of Aeneas's Lean library" \
  "$(show backends/lean/lake-manifest.json | jq -r '.packages[] | select(.name == "mathlib") | .inputRev')" \
  "$MATHLIB_VERSION"

exit "$failed"
