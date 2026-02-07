#!/usr/bin/env bash
set -euo pipefail

export RWLOG_CORPUS_TIER=stress
cargo bench --bench perf_corpus "$@"
