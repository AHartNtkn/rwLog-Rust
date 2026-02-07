# rwlog

rwlog is a relational/logic programming system built on term rewriting. It takes relations described in an algebraic language of relations and normalizes them into (possibly infinite) unions of atomic spans of pattern rewrites. It provides a CLI REPL and an optional Jupyter kernel.

## Features

- Define relations with `rel name { ... }`.
- Query relations interactively (`<expr>`).
- Composition (`;`), disjunction (`|`), and conjunction (`&`).
- Term literals as relations via `@term`.
- Recursive relations via named calls.
- Jupyter notebook integration (text-only outputs).

## Build

```bash
cargo build
```

Jupyter kernel support:

```bash
cargo build --features jupyter --release
```

## Performance Corpus

rwlog includes a performance corpus benchmark harness with quick and stress tiers.

Run the full corpus:

```bash
cargo bench --bench perf_corpus
```

Run quick-only:

```bash
RWLOG_CORPUS_TIER=quick cargo bench --bench perf_corpus
```

Run stress recursive cases only:

```bash
RWLOG_CORPUS_TIER=stress RWLOG_CORPUS_CATEGORY=recursive cargo bench --bench perf_corpus
```

Filter by case id/title substring:

```bash
RWLOG_CORPUS_FILTER=treecalc cargo bench --bench perf_corpus
```

Limit number of selected cases:

```bash
RWLOG_CORPUS_MAX_CASES=5 cargo bench --bench perf_corpus
```

Detailed corpus docs: `PERF_CORPUS.md`  
Case inventory: `benches/perf_corpus_cases.toml`

Sanity/validation:

```bash
cargo run --release --bin perf_corpus_sanity
cargo run --release --bin perf_corpus_sanity -- --lint
cargo run --release --bin perf_corpus_sanity -- --validate
cargo run --release --bin perf_corpus_sanity -- --lint --validate --json
```

Quick perf gate:

```bash
cargo run --release --bin perf_corpus_gate
cargo run --release --bin perf_corpus_gate -- --json
cargo run --release --bin perf_corpus_gate -- --csv
```

Quick gate threshold recommendations:

```bash
cargo run --release --bin perf_corpus_recommend_gate -- --headroom-pct 20
cargo run --release --bin perf_corpus_recommend_gate -- --json
cargo run --release --bin perf_corpus_recommend_gate -- --headroom-pct 20 --apply
```

Allocation visibility (parse vs execute):

```bash
cargo run --release --bin perf_corpus_alloc -- --iters 5
cargo run --release --bin perf_corpus_alloc -- --iters 5 --json
cargo run --release --bin perf_corpus_alloc -- --iters 5 --csv
```

Case-level timing report:

```bash
cargo run --release --bin perf_corpus_run -- --phase end_to_end --iters 20 --json
cargo run --release --bin perf_corpus_run -- --phase end_to_end --iters 20 --csv
```

CI markdown summary from JSON artifacts:

```bash
cargo run --release --bin perf_corpus_ci_summary -- \
  --sanity-json perf-artifacts/quick_sanity.json \
  --gate-json perf-artifacts/quick_gate.json \
  --probe-json perf-artifacts/quick_probe.json \
  --status-json-out perf-artifacts/quick_status.json \
  --out perf-artifacts/quick_summary.md
```

Trend analysis from historical snapshots:

```bash
cargo run --release --bin perf_corpus_trend -- --history-dir perf/history --source all --metric all
scripts/perf/trend.sh --source probe --metric p95 --top 20
cargo run --release --bin perf_corpus_trend -- --history-dir perf/history --window 2 --fail-regressions-pct 10
cargo run --release --bin perf_corpus_trend -- --history-dir perf/history --env-compat fail
cargo run --release --bin perf_corpus_trend -- --history-dir perf/history --fail-regressions-pct 10 --min-regression-confidence 1.5
scripts/perf/trend_gate.sh
```

Periodic corpus-health audit:

```bash
cargo run --release --bin perf_corpus_health -- --history-dir perf/history --source all --window 30 --json
scripts/perf/health_audit.sh
```

Helper scripts:

```bash
scripts/perf/quick.sh
scripts/perf/stress.sh
scripts/perf/save_baseline.sh main
scripts/perf/compare_baseline.sh main
scripts/perf/capture_snapshot.sh --tier quick --iters 10 --label local
scripts/perf/import_artifacts_snapshot.sh --name quick_run_1234 --from perf-artifacts
scripts/perf/trend.sh --source all --metric all
scripts/perf/trend_gate.sh
scripts/perf/health_audit.sh
scripts/perf/prune_history.sh --history-dir perf/history --keep-last 60 --apply
```

## CLI Usage

Start the REPL:

```bash
rwlog
```

Help:

```bash
rwlog help
```

## REPL Commands

- `load <file>`: Load relation definitions from a file.
- `list`: List defined relations.
- `<query>`: Run a query.
- `next`: Show the next answer from the active query.
- `more <n>`: Show the next N answers.
- `reset`: Clear the active query.
- `help`: Show REPL help.
- `quit` / `exit`: Exit.

## Language Syntax

Relations:

```text
rel add { ... }
```

Rules:

```text
lhs -> rhs
```

Composition, disjunction, conjunction:

```text
a ; b
a | b
a & b
```

Grouping:

```text
[a ; b]
```

Terms:

```text
z
(s z)
(cons z (s z))
$x
```

Term literal (identity relation at a term):

```text
@term
```

Example queries:

```text
add ; @(cons z (s z))
@(cons (s z) z) ; add
```

## Recursive Relations

Recursive relations are defined using named `rel` blocks and invoked by name. Example (Peano addition):

```text
rel add {
    (cons z $y) -> $y
    |
    [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
}
```

## Jupyter Notebook Support

Build and install the kernel:

```bash
cargo build --features jupyter --release
./target/release/rwlog kernel install
```

Then launch Jupyter and select the `rwlog` kernel.

Example notebook:

```bash
jupyter notebook examples/addition.ipynb
```

Notes:

- Notebook cells can contain multiple lines; comment lines starting with `#` are ignored.
- Outputs are returned as plain text (execute_result).

## Examples

Definitions and notebooks live in `examples/`, including `examples/addition.txt` and `examples/addition.ipynb`.
