# rwlog

A relational/logic programming system built on term rewriting. Relations are inherently bidirectional: the same definition runs forwards, backwards, or enumerates all input/output pairs.

## Key Idea: Bidirectional Relations

Every relation in rwlog maps input terms to output terms via rewrite rules. Because the semantics are based on tensor relations (not unification), every relation automatically works in both directions.

Define addition once:

```
rel add {
    (cons z $y) -> $y
    |
    [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
}
```

Run it **forward** (2 + 1 = ?):

```
rwlog> @(cons (s (s z)) (s z)) ; add
1. (cons (s (s z)) (s z)) -> (s (s (s z)))
```

Run it **backward** (? + ? = 2):

```
rwlog> add ; @(s (s z))
1. (cons z (s (s z))) -> (s (s z))

rwlog> next
2. (cons (s z) (s z)) -> (s (s z))

rwlog> next
3. (cons (s (s z)) z) -> (s (s z))

rwlog> next
No more answers.
```

No special syntax, no mode switching. The same `add` definition does both.

## Quick Start

```bash
cargo build
cargo run
```

```
rwlog> load examples/addition.txt
Loaded 1 relation(s) from 'examples/addition.txt'

rwlog> @(cons (s z) (s z)) ; add
1. (cons (s z) (s z)) -> (s (s z))

rwlog> add ; @(s (s (s z)))
1. (cons z (s (s (s z)))) -> (s (s (s z)))

rwlog> next 3
2. (cons (s z) (s (s z))) -> (s (s (s z)))
3. (cons (s (s z)) (s z)) -> (s (s (s z)))
4. (cons (s (s (s z))) z) -> (s (s (s z)))

rwlog> quit
```

## Language Reference

### Terms

**Atoms** are simple identifiers:

```
z        nil      true     leaf
```

**Compound terms** are a functor applied to arguments in parentheses:

```
(s z)                  # successor of zero (1 in Peano arithmetic)
(cons a b)             # cons cell
(cons (s z) nil)       # nested: cons of 1 and nil
```

**Variables** start with `$` and are scoped to a single rule:

```
$x   $head   $tail   $result
```

Within a rule, repeated variable names must match the same value: `(cons $x $x) -> $x` only matches cons cells where both elements are identical.

### Rewrite Rules

A rule transforms an input pattern to an output pattern:

```
pattern -> pattern
```

Examples:

```
a -> b                                # constant to constant
(cons $x $y) -> $x                    # extract head of cons cell
(cons (s $x) $y) -> (cons $x $y)     # decrement first element
(pair $x $y) -> (pair $y $x)         # swap pair elements
```

Variables appearing only on the right side are existentially quantified (fresh):

```
$x -> (pair $x $y)    # $y is fresh -- can be anything
```

### Operators

From lowest to highest precedence:

| Precedence | Operator | Name | Meaning |
|------------|----------|------|---------|
| Lowest | `\|` | Disjunction | Either alternative (creates choice points) |
| Middle | `;` | Composition | Output of left feeds into right |
| Highest | `&` | Conjunction | Both must hold simultaneously |

```
a | b ; c & d     parses as     a | (b ; (c & d))
```

**Composition** (`;`) chains relations sequentially:

```
@(cons z (s z)) ; [(cons $x $y) -> (cons $y $x)]
```

**Disjunction** (`|`) creates alternatives (used to separate cases in `rel` blocks):

```
rel color { x -> red | x -> green | x -> blue }
```

**Conjunction** (`&`) requires both sides to hold. Useful for parallel computation -- both branches run concurrently, and their results are combined via matching:

```
[
    [$x -> $x ; process1 ; $r -> (pair $r $s)]
    &
    [$x -> $x ; process2 ; $r -> (pair $t $r)]
]
```

### Grouping

Use `[...]` to group expressions and override precedence:

```
[a | b] ; c             # disjunction first, then compose with c
[(s $x) -> $x ; countdown]  # rule followed by recursive call
```

### Term Literals

The `@` prefix creates an identity relation at a specific term -- it accepts only that term and outputs it unchanged:

```
@(cons z (s z)) ; add      # pass (cons z (s z)) as input to add
add ; @(s (s z))            # constrain add's output to (s (s z))
```

This is the mechanism for running relations forward (`@input ; rel`) and backward (`rel ; @output`).

### Relation Definitions

Named relations group rules with disjunction:

```
rel name {
    rule1
    |
    rule2
}
```

### Recursive Relations

Relations call themselves by name. Every recursive relation needs base case(s) and recursive case(s) that make progress:

```
rel length {
    nil -> z
    |
    [(cons $h $t) -> $t ; length ; $n -> (s $n)]
}
```

The recursive case follows a common pattern: decompose input, recurse, post-process result.

### Constraint Guards and Theories

**Theory blocks** define Constraint Handling Rules (CHR):

```
theory eq_neq {
    constraint eq/2
    constraint neq/2

    (eq $x $x) <=> .
    (eq z (s $x)) <=> fail.
    (eq (s $x) (s $y)) <=> (eq $x $y).
    (neq $x $x) <=> fail.
    (eq $x $y), (neq $x $y) <=> fail.
}
```

Rule types:
- **Simplification** (`<=>`) -- replaces the constraint (`.` = satisfied, `fail` = contradiction)
- **Propagation** (`==>`) -- keeps the constraint and adds new ones
- **Multi-head** -- matches multiple constraints at once: `(c1), (c2) <=> body.`
- **Guarded** -- adds a condition: `(pred $x) <=> guard | body.`

**Guards** in rewrite rules use constraints in curly braces:

```
rel same {
    (pair $x $y) { (eq $x $y) } -> $x
}
```

The rule only fires when all constraints in the guard are satisfiable.

## REPL Commands

| Command | Description |
|---------|-------------|
| `load <file>` | Load relation/theory definitions from a file |
| `list` | List defined relations |
| `<query>` | Run a query (shows first result) |
| `next [N]` | Show the next N answers (default 1) |
| `reset` | Clear the active query |
| `help` | Show REPL help |
| `quit` / `exit` | Exit |

Relations and theories can also be defined directly in the REPL:

```
rwlog> rel double {
    z -> z
    |
    [(s $n) -> $n ; double ; $m -> (s (s $m))]
}
```

## Jupyter Notebook Support

Build and install the kernel:

```bash
cargo build --features jupyter --release
./target/release/rwlog kernel install
```

Then launch Jupyter and select the `rwlog` kernel. Cells can contain multiple lines; comment lines starting with `#` are ignored. Outputs are returned as plain text.

## Examples

Example definitions and notebooks live in `examples/`:

| File | Demonstrates |
|------|-------------|
| `addition.txt` | Peano addition with bidirectional queries |
| `equality_constraints.txt` | CHR theory for equality/inequality over Peano numbers |
| `range_sets.txt` | Integer range sets with open/closed endpoints and constraints |
| `treecalc.txt` | Tree calculus application rules with composition |
| `addition.ipynb` | Interactive addition demo (forward and backward) |
| `evenOdd.ipynb` | Mutual recursion (even/odd predicates) |
| `Lambda.ipynb` | Lambda calculus with bound variable theory |
| `polysimp.ipynb` | Polynomial simplification |
| `ProofSynth.ipynb` | Proof synthesis |
| `program_synth.ipynb` | Program synthesis via tree calculus |

## Performance Corpus

rwlog includes a benchmark harness with quick and stress tiers. Run with:

```bash
cargo bench --bench perf_corpus                                      # full corpus
RWLOG_CORPUS_TIER=quick cargo bench --bench perf_corpus              # quick only
RWLOG_CORPUS_FILTER=treecalc cargo bench --bench perf_corpus         # filter by name
```

Case inventory: `benches/perf_corpus_cases.toml`. See `scripts/perf/` for helper scripts (baselines, trend analysis, CI gates).

## Build

```bash
cargo build                              # default (no optional features)
cargo build --features jupyter --release # with Jupyter kernel
cargo build --features tracing           # with evaluation tracing
```

Feature flags:
- `jupyter` -- Jupyter kernel support (requires zmq)
- `tracing` -- detailed evaluation traces via `RUST_LOG=debug` / `RUST_LOG=trace`
