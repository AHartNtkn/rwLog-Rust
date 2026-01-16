# Evaluation Model Nontermination (Not a Backtracking Bug)

## Summary

The infinite loop observed in backward queries like `add ; (s z)` is **not** a bug in the choicepoint/backtracking mechanism. It is the expected behavior of the current "enumerate then filter" evaluation model when applied to relations with infinitely many spans.

The correct fix requires switching to **expression-level normalization** where constraints are pushed into recursive calls *before* enumeration, not tested afterward.

## Test Case

```
?- add ; (s z)
```

This backward query should find exactly 2 pairs that sum to 1:
- `(cons z (s z)) -> (s z)` (0 + 1 = 1)
- `(cons (s z) z) -> (s z)` (1 + 0 = 1)

## Internal Encoding of `add`

### Source Syntax

From `examples/addition.txt`:
```
rel add {
    # Base case: 0 + Y = Y
    (cons z $y) -> $y
    |
    # Recursive case: S(X) + Y = S(X + Y)
    [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
}
```

### Compiled Goal Structure

The relation compiles to these Goals (IDs are illustrative):

```
Goal 8: Seq([6, 7])           -- The full query: add ; constraint
Goal 7: Rule(3)               -- Constraint: (s z) -> (s z)
Goal 6: Fix(rel=0, body=5)    -- Fix point for recursion
Goal 5: Alt([0, 4])           -- Choice: base case OR recursive case
Goal 4: Seq([1, 2, 3])        -- Recursive case: peel ; call ; wrap
Goal 3: Rule(2)               -- Wrap: $z -> (s $z)
Goal 2: Call(rel=0)           -- Recursive call to add
Goal 1: Rule(1)               -- Peel: (cons (s $x) $y) -> (cons $x $y)
Goal 0: Rule(0)               -- Base: (cons z $y) -> $y
```

### NF Representations

Each Rule goal references an NF (Normal Form) with match patterns, build patterns, and a wire:

**Rule 0 - Base case**: `(cons z $y) -> $y`
```
NF {
    match_pats: [(cons z $0)]    -- Match a pair where first element is z
    build_pats: [$0]             -- Output the second element
    wire: {in: 1, out: 1, map: [(0,0)]}  -- Route variable $0
}
```

**Rule 1 - Peel**: `(cons (s $x) $y) -> (cons $x $y)`
```
NF {
    match_pats: [(cons (s $0) $1)]  -- Match pair with successor first element
    build_pats: [(cons $0 $1)]     -- Output pair with decremented first element
    wire: {in: 2, out: 2, map: [(0,0), (1,1)]}  -- Route both variables
}
```

**Rule 2 - Wrap**: `$z -> (s $z)`
```
NF {
    match_pats: [$0]       -- Match anything
    build_pats: [(s $0)]   -- Wrap in successor
    wire: {in: 1, out: 1, map: [(0,0)]}
}
```

**Rule 3 - Constraint**: `(s z) -> (s z)`
```
NF {
    match_pats: [(s z)]    -- Match exactly (s z)
    build_pats: [(s z)]    -- Output exactly (s z)
    wire: {in: 0, out: 0, map: []}  -- No variables (ground term)
}
```

## Observed Behavior

From tracing with `RUST_LOG=info`:

```
query_complete step_count=10000 answers=2 backtrack_count=2 max_kont_depth=136 exhausted=false hit_max_steps=true
```

Key observations:
1. **answers=2** - Both correct answers ARE found
2. **backtrack_count=2** - Only 2 backtracks (one per answer)
3. **max_kont_depth=136** - Kont grows to 136 frames
4. **exhausted=false** - Search never completes
5. **hit_max_steps=true** - Hits 10000 step limit

Progress over time (`RUST_LOG=debug`):
```
step=1000  answers=2 backtracks=2 kont_depth=39
step=2000  answers=2 backtracks=2 kont_depth=58
step=3000  answers=2 backtracks=2 kont_depth=72
...
step=10000 answers=2 backtracks=2 kont_depth=136
```

## Root Cause Analysis

### Why This Is NOT a Backtracking Bug

The nontermination is **expected** given the current evaluation model. Here's why:

1. **`add` has infinitely many spans** - it's a fixpoint unfolding a recursive clause
2. The current evaluator **enumerates spans of `add` without knowing the output must be `(s z)`**
3. The constraint `id_(s z)` is only tested **after** generating each span
4. This kills almost all spans, but there are still infinitely many to try
5. After finding the 2 survivors, search continues forever trying larger recursive unfoldings and rejecting them

### The Missing Pruning

The failure `unify(z, s X)` that should prune deeper recursion **does not exist** in the recursive call's local state. It only occurs at the outermost `... ; id_(s z)` composition *after* spans from deep recursion have already been generated.

There is nothing to "share" across deeper branches because the pruning constraint is not present at the point those branches are created.

## What Goal-Directed Narrowing Achieves

The evaluator needs to push constraints arising at the "right end" of a composition into recursive calls *before* enumerating their spans.

### The Concrete Rewrite That Makes `add ; id_(s z)` Finite

Write `add` as a fixpoint equation:
```
add = μX. base ∪ (peel ; X ; wrap)
```

Query is:
```
Q = add ; id_(s z)
```

Expand once (using distributivity of `;` over `∪` and associativity):
```
Q = (base ∪ (peel ; add ; wrap)) ; id_(s z)
  = (base ; id_(s z)) ∪ (peel ; add ; wrap ; id_(s z))
  = (base ; id_(s z)) ∪ (peel ; add ; (wrap ; id_(s z)))
```

Now **fuse the adjacent atoms** `(wrap ; id_(s z))`:

- `wrap` is `$u -> s u`
- Post-composing with `id_(s z)` forces `s u = s z`, hence `u = z`

So:
```
wrap ; id_(s z)  ==>  id_z
```

Therefore:
```
Q = (base ; id_(s z)) ∪ (peel ; add ; id_z)
```

Now look at the recursive branch of `add ; id_z`. Expanding `add` again introduces `wrap ; id_z`, which **fails immediately** because it requires unifying `s _` with `z`.

**This is the pruning that should happen at depth 1, not after generating infinite spans.**

The current evaluator never performs the crucial normalization step: "associate to make `wrap` adjacent to `id_(s z)` and fuse before enumerating `add`".

## Why the Current `Task { input, goal, kont }` Model Cannot Work

The current machine has a directional asymmetry:
- `task.input` is a **left** composition context
- The "rest of the sequence" lives in continuations as a **right** context

This is why `add ; id_(s z)` behaves differently from its dual:
- **Dual query**: `id_(s z) ; dual(add)` puts the restriction on the **left** (where the machine is strong), so recursion is bounded
- **Original query**: The restriction is on the **right**, and the machine cannot push it inward - it can only test after generation

Requirements that cannot be met by this model:
- No privileged "input side"
- Evaluation behavior invariant under dual
- Kanren-style interleaving (rotation), not BFS

## The Correct Fix: Expression-Level Evaluation

The evaluator must work on **relational expressions** where `Comp/Or/And/Fix` are first-class, normalized by local rewrites that are closed under dual.

### Minimal Self-Dual IR

```rust
enum Exp {
    Fail,
    Atom(NF),
    Or(Box<Exp>, Box<Exp>),
    And(Box<Exp>, Box<Exp>),
    Comp(Deque<Exp>),  // n-ary composition, not binary
    Fix(RelId, Box<Exp>),
    Call(RelId),
}
```

### "One Step" of Search: Normalize + Rotate

Define `pull : Env -> Exp -> Option<(NF, Exp)>` with:

1. **Comp normalization (direction-agnostic)**
   - Maintain `Comp` as a deque
   - Repeatedly fuse any adjacent `Atom(a), Atom(b)` by `compose_nf(a, b)`
   - Closed under dual: `dual(compose(a,b)) = compose(dual(b), dual(a))`

2. **Lazy distribution through Or with rotation (kanren mplus)**
   ```
   pull(Or(a, b)) =
     match pull(a) {
       Some(ans, a') => Some(ans, Or(b, a')),  // rotate after yielding
       None => pull(b),                         // left exhausted
     }
   ```

3. **And fairness (kanren bind)**
   - Pull one answer from one side
   - Meet with the other side's current answers
   - Rotate the work

4. **Fix/Call**
   - `Call(rel)` resolves to current `Fix` binding
   - **Critical**: Unfold under the current surrounding `Comp` context so atoms like `wrap ; id_(s z)` become adjacent and fuse *before* the next recursive `Call` is created

## Immediate Changes (Before Full Rewrite)

### 1. Map `Call(rel)` to `body`, not `fix_goal`

Currently `Call` jumps to `Fix`, which pushes a new env frame every time. This is wasted work.

`Fix` is a binder; the "call target" is the body under that binder. `Call` should not re-enter `Fix`.

### 2. Remove `saved_kont` from `EnvNode`

A choicepoint must snapshot the **current** consumer kont at Alt entry. The "saved_kont from enclosing Fix" idea is unnecessary now that `handle_alt` uses `task.kont.clone()`. Delete the redundant env field.

## Direction-Agnostic Invariant (Test Criterion)

Once expression-level evaluation is implemented, require:

```
map(dual, enumerate(R)) == enumerate(dual(R))
```

(Equality as streams - same interleaving order modulo dual.)

If step rules are closed under dual and the scheduler (Or/And rotation) is defined structurally, this holds automatically.

The current `task.input` + `SeqNext` model cannot satisfy this invariant because it privileges left composition.

## Files Involved

- `src/eval.rs` - `handle_alt`, `backtrack`, `resume_after_yield`, `step`
- `src/task.rs` - `KontStack`, `ChoiceStack`, `ChoicePoint`, `Env`
- `src/api.rs` - Query loop
- `src/kernel/compose.rs` - `compose_nf`

## Reproduction

```bash
RUST_LOG=info cargo test --features tracing symmetry_backward_query_sum_1 -- --nocapture
```

## Bottom Line

The infinite loop is the expected result of a directional "enumerate then filter" interpreter on an infinite relation. The only correct fix (that also satisfies the self-dual + kanren-interleaving requirements) is to switch to **expression-level normalization with Or-rotation**, so that fusions like `wrap ; id_(s z) -> id_z` happen *before* recursive calls are expanded.
