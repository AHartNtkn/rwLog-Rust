Whenever you are asked to edit AGENTS.md, do not take these as litteral, step-by-step instructions. Think about the spirit of the request and edit the file to meet that spirit.

# rwlog - Relational/Logic Programming via Term Rewriting

## Misalignment Fix Protocol (User-Specified)

- When the user says a requirement is vague/misaligned, stop work and do three steps in order:
  1) Translate it into a precise, checkable rule using the user's wording (no paraphrased or "improved" structure).
  2) Add that rule to AGENTS.md before doing any other work.
- Do not introduce alternative structures or "helpful" reframes unless the user asks.
- You should capture the spirit of the requirement; not preserve it in amber. You MUST think CRITICALLY about what the requirement is and *why*, in context, it exists. Capture that in full; not merely its form.
- Avoid literal, rule‑lawyer interpretations that create busywork or miss the user's intent. Optimize for the best final result within the requested scope, even when that requires large changes.

## Symmetry and Semantics (User-Specified)

- NEVER EVER EVER DIRECTLY QUOTE THE USER IN AGENTS.md!
- The system has only relations; nothing more.
- The system normalizes relations into (possibly infinite) unions of spans.
- There are no inputs.
- There are no outputs.
- There is no directionality.
- Every test should have a dual version (if it is not already symmetric).
- Dual tests should output duals of the same spans; ordering does not need to match.

## Constraints and Substitution (User-Specified)

- If a variable is fully instantiated, then the constraint doesn't drop, the instance gets substituted for the variable. Whether or not the constraint should drop will depend on what ground term it becomes.

## User Interaction (User-Specified)

- Run tests after code changes that can affect behavior. Do not ask the user to run tests.
- Do not run tests for instruction-only edits, documentation-only edits, or git-only changes (branch/worktree/checkout/reset).
- When running tests, run `cargo test --no-run` in the same profile (debug/release) first.

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

## **ABSOLUTELY FORBIDDEN: TEMPORARY OR HACKY IMPLEMENTATIONS**

# NEVER EVER EVER EVER MAKE TEMPORARY IMPLEMENTATIONS!
# NEVER INTENTIONALLY MAKE AN IMPLEMENTATION THAT YOU KNOW IS WRONG AND WILL HAVE TO BE REPLACED!
# NEVER EVER EVER INTRODUCE A HACK, EVER!

**This is non-negotiable.** If you find yourself writing:
- "for now"
- "band-aid fix"
- "temporary workaround"
- "this loses context but prevents..."
- "simple fix for now"

**STOP IMMEDIATELY.** You are about to commit sabotage.

If you don't know how to implement something correctly:
1. **ASK** the user for clarification
2. **RESEARCH** the correct approach
3. **PLAN** before coding

But NEVER write code you know is wrong. Wrong code is worse than no code because:
- It introduces bugs that must be debugged later
- It creates technical debt
- It masks the real problem
- It wastes everyone's time

**The only acceptable implementation is a CORRECT implementation.**

## Interactive Walkthrough Requirements (User-Specified)

These apply to the walkthrough blog post work:

1. **Thorough coverage**: cover every aspect of development, data representation, engine, and computation.
2. **Per-concept interactables**: each concept gets its own interactable; do not limit to one per "unit."
3. **Examples are interactive**: any example that would benefit from interaction should be an interactable.
4. **Depth over basics**: avoid shallow, repetitive, or purely textual demos; use visuals that build intuition about data structure and algorithm flow.
5. **Incremental delivery**: work segment-by-segment; finish the interactable for the current segment before moving on.
6. **Brainstorming-first**: spend time exploring multiple presentation ideas for each segment before implementing the chosen interactable.
7. **Concept inventory first**: before drafting a section's structure or text, enumerate distinct concepts for that section and use that inventory to drive the interactables.
8. **Hierarchical inventory workflow and outline format**: build the walkthrough hierarchy incrementally from the code and record it in `walkthrough/index.html` as an outline:
   - **Layer 1**: one `<h2>` per source file/module.
   - **Layer 2** (one file at a time): immediately under that file’s `<h2>`, add
     `<h3>Types</h3><ul><li>...</li></ul>` and `<h3>Functions / Methods</h3><ul><li>...</li></ul>`.
     Do not add other content until all files have Layer 2.
   - **Layer 3**: after all Layer 2 sections exist, expand **one Layer 2 item at a time**
     (a single `<li>` entry under Types or Functions), and add a nested concept list
     **under that item only**:
     `<li>Thing<ul><li>Concept: ... | Explanation stub | Interactable stub</li></ul></li>`.
     Do not expand multiple items in the same pass. If an item has no concepts, remove
     it from Layer 2 instead of skipping.
     Each concept item becomes a single‑concept segment + its own interactable.
   - No other prose or UI until all files have Layers 1-3 placeholders.
   - End state: a granular, full‑coverage concept list across all files.
9. **Concept quality rules**: before expanding any Layer 2 item, explicitly brainstorm
   the mechanics and edge-case examples that need coverage, then convert that list into
   concepts. This is a tutorial on how the system works, so lead
   each concept list with internal representation/encoding and mechanism details
   (e.g., interner layout, id scheme). Do not restate the Layer 2 item as a “concept.”
   Instead, brainstorm concrete examples that expose mechanics and edge cases.
   Each distinct mechanic or edge case is its own concept.
10. **Interactable quality rule**: each interactable must be a complete, ambitious,
    intuitive, and visual exploration that builds a full mental model of the concept.
    It is not a dressed‑up example; it should eliminate gaps and ambiguities in understanding.
11. **Expanding each concept in separate edits but proceeding continuously without waiting**:
    do not pause for approval or status updates between concepts; limit the scope
    of each edit to a single concept and keep moving automatically to the next.

Walkthrough content directives:
Visual communication: use SVGs and other mechanisms to communicate visually throughout.
Layout rule: avoid multi-column exposition; keep text single-column and give diagrams full-width space.


## CRITICAL: Always Use Timeouts When Running Tests

**NEVER run tests without a timeout.** If tests don't ALL finish in less than 180 seconds, there's an infinite loop bug.

**Always use:**
```bash
cargo test --no-run 2>&1
timeout 180 cargo test 2>&1
```

**Never use:**
```bash
cargo test 2>&1  # WRONG - will hang forever on infinite loop
```

This applies to ALL test commands - full suite, filtered tests, individual tests. No exceptions.

## TDD Test Coverage Requirements

**When implementing a new feature using TDD, you MUST write comprehensive failing tests FIRST.**

A single vague test like "this feature doesn't work" is USELESS. It doesn't guide implementation, doesn't document expected behavior, and doesn't catch regressions.

**Before implementing ANY feature:**

1. **Analyze the feature** using a subagent to identify ALL edge cases
2. **Write a failing test for EVERY edge case** identified
3. Each test must be:
   - **Specific**: Tests exactly ONE behavior or edge case
   - **Named descriptively**: The test name documents the expected behavior
   - **Minimal**: Sets up only the state needed to test that specific case
   - **Assertive**: Makes precise assertions about expected outcomes

**Example of BAD TDD:**
```rust
#[test]
fn feature_doesnt_work() {
    // One vague test that says "ya, this isn't implemented"
    assert!(feature.works(), "BUG: Feature not implemented");
}
```

**Example of GOOD TDD:**
```rust
#[test]
fn feature_handles_empty_input() { /* specific test */ }

#[test]
fn feature_handles_single_element() { /* specific test */ }

#[test]
fn feature_handles_boundary_value_zero() { /* specific test */ }

#[test]
fn feature_handles_boundary_value_max() { /* specific test */ }

#[test]
fn feature_rejects_invalid_input_gracefully() { /* specific test */ }

#[test]
fn feature_terminates_on_recursive_case() { /* specific test */ }

// ... one test per edge case identified in analysis
```

**The number of failing tests should reflect the complexity of the feature.** A complex feature like Fix/Call with tabling should have 20-50 failing tests covering:
- Basic happy path cases
- Boundary values (0, MAX, empty, single, many)
- Error cases (undefined references, invalid states)
- Termination cases (recursive patterns that must terminate)
- Interaction with other features
- State transitions
- Concurrency/coordination (if applicable)

**DO NOT proceed to implementation until you have comprehensive failing tests.**

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
Rw lhs rhs c  ~=  RwL [normLhs] ; DropFresh w ; RwR [normRhs]
```

This separation isolates:
- **RwL**: Pattern matching (decomposition)
- **DropFresh**: Variable routing
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

### DropFresh - Variable Routing

DropFresh specifies how variables flow from input to output.

**Intuition:** Start with a tuple of n values, drop some, keep k, add fresh values, end with m values. There are no swaps or reorderings - just drop and add.

- Start with n input values
- **Drop** (n - k) values: the ones NOT selected by domain
- **Keep** k values: the ones selected by domain
- **Add** (m - k) fresh values: existentially quantified
- Result is m output values

**Representation:** A monotone partial injection - list of (input_pos, output_pos) pairs, strictly increasing in both coordinates.

```rust
struct DropFresh<C> {
    in_arity: u32,
    out_arity: u32,
    map: SmallVec<[(u32, u32); 4]>,  // strictly increasing in both coords
    constraint: C,
}
```

**Semantics:**
```
[[DropFresh w]] inp out  <=>
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

3. **Build labels** for DropFresh:
   ```
   lhsLabels = [0, 1, ..., n-1]
   rhsLabels = for each (j, v) in enumerate(rhsVars):
                 if v in lhsVars at position i: label = i
                 else: label = n + j  (fresh, unique)
   ```

4. **Construct DropFresh** from matching labels:
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

This fusion **ALWAYS** produces `RwL ; DropFresh ; RwR` (never just a DropFresh):
```
RwR [p1, ...] ; RwL [q1, ...] ->
  if unify(pi, qi) succeeds with sigma:
    RwL [varsOf(p)[sigma], ...] ; DropFresh w ; RwR [varsOf(q)[sigma], ...]
  else:
    Fail
```

**CRITICAL:** The result RwL/RwR contain the **variable lists** with unifier applied, NOT the original patterns.

**Example:** `RwR [B(0,1)] ; RwL [B(A(2),3)]`
1. Unify B(0,1) with B(A(2),3): sigma = {0 -> A(2), 1 -> 3}
2. RwR vars [0,1] -> [A(2), 3]
3. RwL vars [2,3] -> [2, 3] (unchanged)
4. Result: `RwL [A(2), 3] ; DropFresh(identity 2->2) ; RwR [2, 3]`

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
- **DropFresh moves left** (arbitrary choice, but consistent)

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
    drop_fresh: DropFresh<C>,
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

Step 4-6: Continue fusing DropFreshs and RwRs

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

### Refactoring and Deletion

**When a plan includes deletion or removal of old code, perform deletions as one of the earliest tasks.**

Rationale:
- Old code lying around creates confusion and technical debt
- Stubs and compatibility layers accumulate complexity
- Deleting first forces a clean break and reveals true dependencies
- It's easier to build new code on a clean foundation than to maintain two systems

Approach:
1. Delete the old files immediately
2. Update module declarations to remove references
3. Fix compilation errors by building new code, not by adding stubs
4. Never maintain "legacy" or "backwards compatibility" code

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
    let result = repl.process_line("add ; z").unwrap();
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
