# rwlog

rwlog is a relational/logic programming system built on term rewriting. It takes relations described in an algebraic language of relations and normalizes them into (possibly infinite) unions of atomic spans of pattern rewrites. It provides a CLI REPL and an optional Jupyter kernel.

## Features

- Define relations with `rel name { ... }`.
- Query relations interactively (`?- <expr>` or bare `<expr>`).
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
- `?- <query>`: Run a query.
- `<query>`: Bare query (same as `?- <query>`).
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
?- add ; @(cons z (s z))
?- @(cons (s z) z) ; add
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
