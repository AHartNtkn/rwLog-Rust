# rwlog - Relational/Logic Programming via Term Rewriting

## PRIMARY EDICT: Tests Must Verify Correct Behavior

**TESTS MUST NEVER EXPECT OR CODIFY BROKEN BEHAVIOR.**

A test that expects incorrect output is a lie. It is a machine designed to deceive. When a test passes because it expects broken behavior, it actively prevents detecting bugs and masks the true state of the system.

**Rules:**
1. Every test must verify the CORRECT expected behavior
2. If a test fails after a fix, the test was WRONG - update it to expect correct behavior
3. Never write a test that "passes" by expecting an incorrect result
4. Never describe a test as "expecting broken behavior" - that is not a test, it is sabotage
5. If you discover a test expecting wrong behavior, DELETE IT or FIX IT immediately

**The only valid test outcomes:**
- Test passes: system behaves correctly
- Test fails: system has a bug that needs fixing

There is no third category of "test passes because it expects the bug."

## Architecture Overview

rwlog is a relational/logic programming system built on term rewriting. It uses Free monads over functors to represent terms, with a constraint system for extensibility.

## Semantic Foundation

### Tensor Relations

The semantic domain is **tensor relations**: relations between lists of ground terms.

```
TRel = [Term] -> [Term] -> Prop
```

Key operations:
- `empty`: the empty relation (bottom)
- `union R S`: disjunction (R union S)
- `inter R S`: conjunction (R intersection S)
- `comp R S`: sequential composition (R ; S)
- `dual R`: converse relation (swap inputs and outputs)

### Span Semantics

A **span** `Rw lhs rhs` denotes a relation where:
- Input is a singleton list [t]
- Output is a singleton list [s]
- There exists a substitution sigma such that lhs[sigma] = t and rhs[sigma] = s

```
[[Rw lhs rhs]] [t] [s]  <=>  exists sigma. lhs[sigma] = t and rhs[sigma] = s
```

## Internal Representation

User-facing `Rw` nodes are **factored** into three internal forms before execution:

```
Rw lhs rhs c  ~=  RwL [normLhs] ; Wire w ; RwR [normRhs]
```

This separation isolates:
- **RwL**: Pattern matching (decomposition)
- **Wire**: Variable routing
- **RwR**: Term construction (composition)

### RwL - Left Tensor (Decomposition)

`RwL [p1, p2, ...]` matches input terms against patterns and extracts variable bindings.

**Semantics:**
```
[[RwL patterns]] inp out  <=>
  exists sigma. patterns.map(.[sigma]) = inp and
      out = sortedDistinctVars(patterns).map(sigma)
```

- Input: list of terms to match against patterns
- Output: list of variable values in sorted order of variable indices

### RwR - Right Tensor (Composition)

`RwR [p1, p2, ...]` takes variable values and constructs output terms.

**Semantics:**
```
[[RwR patterns]] inp out  <=>
  exists sigma. inp = sortedDistinctVars(patterns).map(sigma) and
      patterns.map(.[sigma]) = out
```

- Input: list of variable values in sorted order
- Output: list of terms constructed from patterns

**Duality:** RwL and RwR are perfect duals: `[[RwR ps]] = dual([[RwL ps]])`

### Wire - Variable Routing

Wire specifies how variables flow from input to output.

**Intuition:** Start with a tuple of n values, drop some, keep k, add fresh values, end with m values. There are no swaps or reorderings - just drop and add.

- Start with n input values
- **Drop** (n - k) values: the ones NOT selected by domain
- **Keep** k values: the ones selected by domain
- **Add** (m - k) fresh values: existentially quantified
- Result is m output values

**Representation:** A monotone partial injection - list of (input_pos, output_pos) pairs, strictly increasing in both coordinates.

```rust
struct Wire<C> {
    in_arity: u32,
    out_arity: u32,
    map: SmallVec<[(u32, u32); 4]>,  // strictly increasing in both coords
    constraint: C,
}
```

**Semantics:**
```
[[Wire w]] inp out  <=>
    length inp = w.in_arity and
    length out = w.out_arity and
    forall (i, j) in w.map. inp[i] = out[j]
```

## Factoring Algorithm

Given `Rw lhs rhs c`:

1. **Extract variables** from each side independently (order of first appearance):
   ```
   lhsVars = nub (collectVarsOrdered lhs)  -- e.g., [2, 0, 5]
   rhsVars = nub (collectVarsOrdered rhs)  -- e.g., [0, 3, 5]
   ```

2. **Renumber** each side to use consecutive indices starting at 0:
   ```
   normLhs uses vars 0..n-1 (where n = length lhsVars)
   normRhs uses vars 0..m-1 (where m = length rhsVars)
   ```

3. **Build labels** for Wire:
   ```
   lhsLabels = [0, 1, ..., n-1]
   rhsLabels = for each (j, v) in enumerate(rhsVars):
                 if v in lhsVars at position i: label = i
                 else: label = n + j  (fresh, unique)
   ```

4. **Construct Wire** from matching labels:
   - Shared variables: where lhsLabels[i] = rhsLabels[j]
   - map contains (i, j) pairs for shared variables

## Fusion Rules (Kernel Operations)

The kernel has two primary operations:

### compose_nf: Sequential Composition

Fuses `NF1 ; NF2` into a single NF.

**Homogeneous Fusion:**

`RwL ; RwL` - Substitute inner terms into outer patterns:
```
RwL [p1, p2, ...] ; RwL [q1, q2, ...] -> RwL [p1[q/vars], p2[q/vars], ...]
```

`RwR ; RwR` - Substitute outer terms into inner patterns:
```
RwR [p1, p2, ...] ; RwR [q1, q2, ...] -> RwR [q1[p/vars], q2[p/vars], ...]
```

**Heterogeneous Fusion:**

`RwR ; RwL` - Unification at the interface:

This fusion **ALWAYS** produces `RwL ; Wire ; RwR` (never just a Wire):
```
RwR [p1, ...] ; RwL [q1, ...] ->
  if unify(pi, qi) succeeds with sigma:
    RwL [varsOf(p)[sigma], ...] ; Wire w ; RwR [varsOf(q)[sigma], ...]
  else:
    Fail
```

**CRITICAL:** The result RwL/RwR contain the **variable lists** with unifier applied, NOT the original patterns.

**Example:** `RwR [B(0,1)] ; RwL [B(A(2),3)]`
1. Unify B(0,1) with B(A(2),3): sigma = {0 -> A(2), 1 -> 3}
2. RwR has vars [0, 1] -> apply sigma -> [A(2), 3]
3. RwL has vars [2, 3] -> apply sigma -> [2, 3] (unchanged)
4. Result: `RwL [A(2), 3] ; Wire(identity 2->2) ; RwR [2, 3]`

**Common mistake to avoid:** The fact that patterns become identical after unification says nothing about whether the operation is identity. The actual transformation is determined by the *variable structure*, not pattern equality.

### meet_nf: Conjunction/Intersection

Fuses `And(NF1, NF2)` into a single NF.

Implementation:
1. Convert each NF to "direct rule" form (lhs_terms, rhs_terms, constraint)
2. Rename-apart vars of the second side
3. Unify lhs lists, unify rhs lists; combine constraints; normalize
4. Factor back into NF

This eliminates looping behavior because `meet_nf` is a single terminating function, not a rewriting schema.

## Normalization Principle

The universal principle for normalization is:
- **RwL always moves left**
- **RwR always moves right**
- **Wire moves left** (arbitrary choice, but consistent)

### And Normalization

For `And (RwL x ; rest) other`, we pull RwL left:
```
And (RwL x ; rest) other  ->  RwL x ; And rest (RwR x ; other)
```

**Why this is correct:** RwL x and RwR x are converses:
```
a (RwL x) c  <=>  c (RwR x) a
```

## Search Strategy

### Or nodes as search trees

Or nodes represent a search tree. There is no explicit search tree separate from the Or nodes.

Key principles:
- Add atomic relations to the search tree ONLY when one of its branches is normalized
- Only propagate up the branch to the leaf that is normalized
- Distribute lazily (copying across Ors could be unnecessary since most branches get pruned)
- Every time we take a step on an Or, we step into the left branch and rotate the Or

This mechanism mimics miniKanren-style interleaving search through Or rewrites. Treating Ors this way maintains separate search trees where components not distributed to either are shared between the trees.

### And fairness

Similar rotation system for And for the sake of And fairness.

## Normal Form (NF)

The kernel operates on a single compact canonical form:

```rust
struct NF<C> {
    // Match: patterns to decompose input
    match_pats: SmallVec<[TermId; 1]>,
    wire: Wire<C>,
    // Build: patterns to construct output
    build_pats: SmallVec<[TermId; 1]>,
}
```

Invariant: each NF is *fully normalized* (all adjacent fusions already done; identity Match/Build already folded away).

## Worked Example: Composing B(A(x),y)->B(x,y) with Itself

Initial: `Rw (B(A(x),y)) (B(x,y)) ; Rw (B(A(u),v)) (B(u,v))`

After factoring (with disjoint variables):
```
RwL [B(A(0),1)] ; W1 ; RwR [B(0,1)] ; RwL [B(A(2),3)] ; W2 ; RwR [B(2,3)]
```

Step 1 - RwR;RwL fusion on `RwR [B(0,1)] ; RwL [B(A(2),3)]`:
- Unify: 0 = A(2), 1 = 3
- RwR vars [0,1] -> [A(2), 3]
- RwL vars [2,3] -> [2, 3]
- Result: `RwL [A(2), 3] ; W_id ; RwR [2, 3]`

After step 1:
```
RwL [B(A(0),1)] ; W1 ; RwL [A(2), 3] ; W_id ; RwR [2, 3] ; W2 ; RwR [B(2,3)]
```

Step 2 - W1;RwL fusion: W1 passes through unchanged (identity)

Step 3 - RwL;RwL fusion on `RwL [B(A(0),1)] ; RwL [A(2), 3]`:
- Substitute: var 0 -> A(2), var 1 -> 3
- B(A(0), 1) becomes B(A(A(2)), 3)
- Result: `RwL [B(A(A(2)), 3)]`

Step 4-6: Continue fusing Wires and RwRs

Final result:
```
RwL [B(A(A(2)), 3)] ; W_final ; RwR [B(2,3)]
```

Collected as: `Rw B(A(A(0)),1) B(0,1)`

This correctly represents composing the "decrement" operation twice.

## Tracing and Profiling

### Feature Flag: `tracing`

rwlog has a `tracing` feature flag that enables detailed evaluation traces with zero overhead when disabled.

```bash
# Run tests with tracing enabled
RUST_LOG=debug cargo test --features tracing

# Run with trace-level detail
RUST_LOG=trace cargo test --features tracing

# Run benchmarks
cargo bench

# Generate flamegraph (requires perf and inferno)
RUSTFLAGS="-C force-frame-pointers=yes" cargo build --release --features tracing
perf record -g ./target/release/rwlog
perf script | inferno-collapse-perf | inferno-flamegraph > flamegraph.svg
```

### What Gets Traced

When tracing is enabled, the following are instrumented:

**Priority 1 (DEBUG/TRACE level):**
- `step()` - Main eval dispatch (task_id, goal_id, kont_depth)
- `backtrack()` - Search backtracking (initial_depth, kont types popped)
- `resume_after_yield()` - Answer flow through continuations
- `compose_nf()` - Rule composition (arities, unification result)

**Priority 2 (TRACE level):**
- `handle_rule/alt/seq/both/call()` - Individual goal handlers
- `meet_nf()` - Conjunction/intersection
- `push_kont()/pop_kont()` - Continuation stack operations

### Metrics

The `EvalMetrics` struct collects aggregate statistics:
- Step counts
- Composition attempts (success/failure)
- Backtrack events
- Maximum continuation stack depth

### Log Levels

- `error` - Critical failures only
- `warn` - Unexpected but recoverable conditions
- `info` - High-level operation summaries
- `debug` - Detailed operation flow
- `trace` - Fine-grained step-by-step detail

## Development Methodology: Test-Driven Development

All implementation follows strict TDD:

1. **Write failing tests FIRST** - Before writing any implementation code
2. **Tests must be thorough and nontrivial** - Not just basic happy-path tests
3. **Test both success and specific failures** - Happy path AND unhappy path with specific expected failures
4. **Tests are verbose for debugging** - Include enough output to diagnose failures
5. **Write code to make tests pass** - Only after tests exist and fail

### Test Categories for Each Component

For each module, tests should cover:

**Happy Path:**
- Normal operation with valid inputs
- Edge cases within valid bounds
- Multiple valid input combinations

**Unhappy Path (Specific Failures):**
- Invalid inputs that should cause specific errors
- Boundary violations
- Malformed data
- Resource exhaustion scenarios where applicable

### Example Test Structure

```rust
#[cfg(test)]
mod tests {
    use super::*;

    // Happy path tests
    #[test]
    fn unify_identical_terms_succeeds() { ... }

    #[test]
    fn unify_compatible_terms_produces_correct_substitution() { ... }

    // Unhappy path tests - specific expected failures
    #[test]
    fn unify_incompatible_constructors_fails() { ... }

    #[test]
    fn unify_occurs_check_prevents_infinite_term() { ... }

    #[test]
    fn unify_arity_mismatch_fails() { ... }
}
```

### No Mocking

Tests use real implementations, not mocks. This ensures tests reflect actual behavior.

### Bug-First Testing

**EVERY time a bug is identified, ALWAYS work to add *failing* tests that detect the bug FIRST. Then fix the bug.**

The workflow is:
1. Identify the bug
2. Write a test that fails because of the bug
3. Verify the test fails for the right reason
4. Fix the bug
5. Verify the test now passes

This ensures:
- The bug is well-understood before attempting a fix
- The fix actually addresses the root cause
- Regression protection is in place immediately
- The test suite grows to cover real-world failure modes

### Writing Minimal Bug-Demonstrating Tests

A bug-demonstrating test must **isolate the exact condition that triggers the bug**. This is different from a test that merely detects the bug exists somewhere in the stack.

**Principles:**
1. **Use the lowest-level API possible** - If the bug is in `eval.rs`, write the test in `eval.rs`, not in `repl.rs` which calls through 5 layers
2. **Set up only the minimal state needed** - Don't load files, parse strings, or initialize full systems when you can construct the exact data structure directly
3. **Assert on the specific broken behavior** - The assertion should fail for exactly the reason the bug exists, not a downstream symptom
4. **Name the test after the bug pattern** - e.g., `resume_after_yield_alt_over_seq_must_continue` not `backward_query_test`

**Example - BAD (detects but doesn't demonstrate):**
```rust
fn test_backward_query_bug() {
    let mut repl = Repl::new();
    repl.process_line("load examples/addition.txt").unwrap();
    let result = repl.process_line("?- add ; z").unwrap();
    assert!(result.contains("(cons z z) -> z"));  // Fails, but WHY?
}
```

**Example - GOOD (demonstrates the exact bug):**
```rust
fn resume_after_yield_with_seq_below_alt_must_continue() {
    // Set up exact stack state: SeqNext below AltNext
    let mut task = make_task(0);
    task.push_kont(Kont::SeqNext { remaining: smallvec![constraint_goal] });
    task.push_kont(Kont::AltNext { remaining: smallvec![alt2] });

    // This is the exact call that misbehaves
    let result = resume_after_yield(&mut task, answer, &mut ctx);

    // The bug: returns Yielded when it should Continue through SeqNext
    assert_eq!(result, StepResult::Continue,
        "BUG: Alt yield must flow through SeqNext, not be treated as final");
}
```

The good test will fail with a message that explains the bug. The bad test just says "expected X got Y" with no insight into the cause.
