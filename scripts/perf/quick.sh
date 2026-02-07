#!/usr/bin/env bash
set -euo pipefail

export RWLOG_CORPUS_TIER=quick
cargo bench --bench perf_corpus "$@"
