# Bug: treecalc_app_example_11 hangs after first answer

## Current Understanding

The test `repl_treecalc_app_example_11_next_exhausts` hangs forever after producing the first answer.

**Query:** `@(f (f (b l) l) l) ; app`
**First answer produced:** `(f (f (b l) l) l) -> (f l (b l))`
**Expected behavior:** Should return "No more answers" after the first answer
**Actual behavior:** Hangs indefinitely when requesting next answer

## IMPORTANT CLARIFICATION

### What the bug IS NOT

The bug is **NOT** about producing wrong answers. The answers produced are semantically correct.

### What the bug IS

The bug is a **termination failure**: after producing the correct answer(s), the system hangs instead of returning "No more answers".

### Variable Scoping is Correct

Variables in different atomic relations are **supposed** to be independent. This is by design:
- `(pair $x $y) -> $x ; xform ; $r -> (out $r $y)`
- is equivalent to: `(pair $x $y1) -> $x ; xform ; $r -> (out $r $y2)`
- The two `$y` variables are in different scopes and are NOT the same

This is analogous to lambda calculus: in `(\r -> (r, y)) (xform (\(x, y) -> x))`, the two `y`s are different variables in different scopes.

### Derivation showing `(out result result)` is CORRECT

```
@(pair p q) ; [
    [(pair $x $y) -> $x ; xform ; $r -> (out $r $y)]
    &
    [(pair $x $y) -> $y ; xform ; $r -> (out $x $r)]
]

= rwL (pair p q) ; dropFresh [] ; rwR (pair p q) ; [branch1 & branch2]
= rwL (pair p q) ; rwR (pair p q) ; [branch1 & branch2]
= rwL (pair p q) ; [[rwR (pair p q) ; (pair $x $y) -> $x ; xform ; $r -> (out $r $y)]
                  & [rwR (pair p q) ; (pair $x $y) -> $y ; xform ; $r -> (out $x $r)]]
= rwL (pair p q) ; [[rwR p ; xform ; $r -> (out $r $y)]
                  & [rwR q ; xform ; $r -> (out $x $r)]]
= rwL (pair p q) ; [[rwR p ; $a -> result ; $r -> (out $r $y)]
                  & [rwR q ; $a -> result ; $r -> (out $x $r)]]
= rwL (pair p q) ; [[rwR result ; $r -> (out $r $y)]
                  & [rwR result ; $r -> (out $x $r)]]
= rwL (pair p q) ; [[rwR (out result $y)] & [rwR (out $x result)]]
= rwL (pair p q) ; rwR (out result result)
= (pair p q) -> (out result result)
```

The fresh variables `$y` and `$x` in the final rwR patterns match to `result` during the And intersection, giving the correct answer `(out result result)`.

---

## Investigation History (for reference)

## Hypotheses

1. **And emits without intersection** - The And operation is emitting answers from individual branches without verifying they satisfy ALL branches - Status: **PLAUSIBLE** (evidence: answer matches only Branch 2, not Branch 1)
2. **And + Fix interaction bug** - When an And has multiple Fix calls, something causes infinite looping - Status: untested
3. **Producer iteration never reaches fixed point** - The table producer keeps iterating without detecting that no new answers are being produced - Status: untested
4. **meet_nf not being called** - The kernel's meet_nf (which computes And of two NFs) might not be invoked correctly - Status: untested

## Investigation Log

### Step 1: Establish baseline
**Tried:** Run test `repl_treecalc_app_example_11_next_exhausts`
**Observed:** Test times out after 2 seconds waiting for `next` to return
**Conclusion:** Confirmed - the hang happens on the second answer request, not the first

### Step 2: Capture first answer
**Tried:** Added test `repl_treecalc_app_example_11_first_answer` to print first answer
**Observed:** First answer is `(f (f (b l) l) l) -> (f l (b l))`
**Conclusion:** One answer IS produced. The answer matches only Branch 2 of the And, not Branch 1. This is suspicious - the And should either:
  - Produce no answers (if branches disagree)
  - Produce an answer that satisfies BOTH branches

### Step 3: Test basic And semantics
**Tried:** Created tests `and_of_different_outputs_produces_no_answers` and `and_of_same_outputs_produces_one_answer`
**Observed:** Both tests PASS
- Different outputs -> No answers (correct)
- Same outputs -> One answer (correct)
**Conclusion:** Basic And semantics are correct. The bug must be in the interaction with Fix/Call (tabled recursive calls).

### Step 4: Test And with recursive calls (simple structure)
**Tried:** Tests `and_with_recursive_calls_different_outputs` and `and_with_recursive_calls_same_outputs`
**Observed:** Both PASS - And with recursive calls works correctly in simple cases
**Conclusion:** The issue is more specific than just "And + recursion"

### Step 5: Test treecalc-like structure
**Tried:** Test `and_treecalc_rule5_structure` mimicking Rule 5's variable structure
**Observed:** FAILS!
- Expected: "No more answers" (branches should produce different outputs)
- Actual: `(f (f (b l) l) l) -> (f (b l) (b l))`
**Conclusion:** **BUG FOUND!** The output `(f (b l) (b l))` is NEITHER branch's expected output:
- Branch 1 should produce: `(f (b l) l)`
- Branch 2 should produce: `(f l (b l))`
- Actual: `(f (b l) (b l))` - has `(b l)` in BOTH positions!

This suggests the And is computing something unexpected - possibly:
- Pattern-level intersection before recursive calls resolve
- Variable scoping issue across And branches
- The two $r variables (one per branch) are being incorrectly unified

### Step 6: Isolate the bug with simpler test
**Tried:** Test `and_shared_pattern_with_call` - both branches call same relation, capture into $r
**Observed:** BUG REPRODUCED!
- Input: `(pair p q)`
- Branch 1 should produce: `(out result q)` (result from xform, q from initial match)
- Branch 2 should produce: `(out p result)` (p from initial match, result from xform)
- Expected intersection: EMPTY (different terms)
- **ACTUAL OUTPUT:** `(out result result)` - has `result` in BOTH positions!

**Conclusion:** **ROOT CAUSE IDENTIFIED!**

When both And branches:
1. Share an initial pattern (extracting $x, $y)
2. Call a relation (like xform)
3. Capture the result into a variable ($r)
4. Use that variable in the final output

The $r variables from BOTH branches are being incorrectly unified/shared, causing the intersection to produce a term with `result` in positions where one branch expected the original pattern variable.

## Step 7: Add debug assertions to meet_nf and compose_nf
**Tried:** Added `debug_assert_vars_disjoint` calls after variable shifting in both functions
**Observed:** Assertions did NOT fire! Variables ARE disjoint after shifting.
**Conclusion:** The bug is NOT in meet_nf or compose_nf's variable handling

## Step 8: Trace actual NF composition through sequences
**Tried:** Manually traced what happens when `$r -> (out $r $y)` is parsed and composed
**Observed:** Each rule is parsed with its OWN var_map (src/parser.rs:383)
**Conclusion:** **ACTUAL ROOT CAUSE FOUND!**

## TRUE ROOT CAUSE

The issue is NOT a variable collision bug. It's a **semantic design issue** in how variables work across sequences.

### What Actually Happens

For `$r -> (out $r $y)`:
- LHS has vars: [$r] (index 0)
- RHS has vars: [$r, $y] (indices 0, 1)
- Since $y is NOT on LHS, it's a **FRESH (existentially quantified) variable**

When composing `(pair $x $y) -> $x ; xform ; $r -> (out $r $y)`:
1. Rule 1 `(pair $x $y) -> $x`: matches input, produces first component
2. xform: transforms to `result`
3. Rule 3 `$r -> (out $r $y)`: matches result, produces `(out result ?fresh)`
   - The $y is **NOT** the same as rule 1's $y - it's a new variable
   - Since it's not bound by the LHS ($r), it's existentially quantified

So Branch 1 produces: `(out result fresh1)` for ANY `fresh1`
And Branch 2 produces: `(out fresh2 result)` for ANY `fresh2`

The meet of these IS `(out result result)` - this is **semantically correct** given the fresh variable semantics!

### The `meet_unifies_fresh_outputs` test confirms this is expected behavior

The test at `src/kernel/meet.rs:232` explicitly tests and expects:
- NF1: input -> `f(f(l, c(0)), var(0))` where var(0) is fresh
- NF2: input -> `f(var(0), b(c(0)))` where var(0) is fresh
- Meet: input -> `f(f(l, c(0)), b(c(0)))` - fresh vars unified

This is the SAME behavior we see in the bug case!

### The Real Problem

The user EXPECTED `$y` in `$r -> (out $r $y)` to refer back to the `$y` from `(pair $x $y) -> $x`. But because each rule is parsed independently with its own variable namespace (src/parser.rs:383), `$y` in rule 3 is a NEW fresh variable.

This is a mismatch between:
1. **User expectation**: Variables thread across rules in a sequence
2. **Actual implementation**: Each rule has independent variable scope

## Disproven Theories
- **Hypothesis 1 (And emits without intersection)**: DISPROVEN - meet_nf works correctly
- **Hypothesis 5 (Variable collision in meet)**: DISPROVEN - assertions prove vars are disjoint

## Actual Issue: Semantic Design Decision

Variables do NOT thread across rules in a sequence. Each rule is parsed independently.

For the user's intended semantics to work, one of these changes is needed:
1. **Parser change**: Share var_map across rules in a sequence
2. **Syntax change**: Add explicit syntax for referencing outer variables
3. **Documentation**: Clarify that variables don't thread (may not match user expectations)

## Why This Causes the Hang

The wrong intersection produces unexpected answers. The tabling system sees these unexpected answers, tries to find more, and enters an inconsistent state leading to infinite looping.

---

# CONFIRMED ROOT CAUSE: Infinite Table Proliferation in ReplayOnly Mode

## Bug Location

**File:** `src/work.rs:991-1016` (`handle_call` function)

## Root Cause

When in `ReplayOnly` mode and the call key doesn't match the replay key, the code **falls through to normal behavior** and creates a new table. This leads to infinite table proliferation.

## The Buggy Code Pattern

```rust
if let CallMode::ReplayOnly(replay_key) = &self.call_mode {
    if replay_key.as_ref() == &key {
        // Use existing table (CORRECT)
        return ...;
    }
    // BUG: Falls through here when keys don't match!
}
// Creates new table (WRONG for ReplayOnly mode)
let table = self.tables.get_or_create(key.clone());
```

**Expected behavior:** ReplayOnly mode should prevent table creation entirely, not just for the matching key.

## Step-by-Step Mechanical Walkthrough

1. **Initial Query:** `@(f (f (b l) l) l) ; app`
   - Creates Table #1 for `app` with `key1 = CallKey(app, left=Some(RwL[(f (f (b l) l) l)]), right=None)`
   - Table #1's producer starts with `call_mode = ReplayOnly(key1)`

2. **Producer Runs:**
   - Producer executes `app`'s body, which involves composing rules
   - As rules compose, the boundary context changes (variables get added through composition)
   - Eventually makes a recursive call to `app`

3. **Recursive Call (BUG POINT):**
   - At `src/work.rs:991`, code checks: `if replay_key.as_ref() == &key`
   - `replay_key` = key1 (left_arity=0)
   - Current `key` = key2 (left_arity=4, because composition added variables)
   - **key1 ≠ key2** → `keys_match=false`
   - Code falls through to line 1016: `self.tables.get_or_create(key.clone())` → **Creates Table #2**

4. **Table #2 Triggers Same Bug:**
   - Table #2's producer starts with `call_mode = ReplayOnly(key2)`
   - Producer runs, boundaries change, makes recursive call with key3
   - key3 ≠ key2 → Creates Table #3

5. **Infinite Loop:**
   - Each new table creates a producer in ReplayOnly mode
   - Each producer's recursive calls have different boundary contexts
   - Each different context creates a new table
   - Tables proliferate indefinitely: 1 → 2 → 3 → 4 → ...

## Evidence from Debug Instrumentation

```
[TABLE 1] mode=Normal left_arity=Some(0) right_arity=None
[TABLE 2] mode=Replay left_arity=Some(0) right_arity=Some(1)
[BUG TRIGGER] ReplayOnly mode creating NEW table!
  replay_key left_arity=Some(0)
  new_key left_arity=Some(4)
[TABLE 3] mode=Replay left_arity=None right_arity=None
[BUG TRIGGER] ReplayOnly mode creating NEW table!
  replay_key left_arity=Some(0)
  new_key left_arity=None
...continues indefinitely...
```

## Why Boundaries Change

Boundaries change due to composition with surrounding rules. When the producer runs `app`'s body:
1. Body contains rules like `(f $x $y) -> $x ; app ; ...`
2. Composition with `(f $x $y) -> $x` changes the boundary from `RwL[(f (f (b l) l) l)]` (0 vars) to `RwL[$x, $y, ...]` (multiple vars)
3. Recursive call to `app` now has different boundary → different CallKey

## Fix Strategy

In ReplayOnly mode, when the call is to the **same relation** as the replay key (same RelId and BindId), use the replay table regardless of boundary context. This prevents infinite proliferation while maintaining correct tabling semantics for mutual recursion.

---

# VERIFIED WITH INSTRUMENTATION (January 2026)

## Confirmed Evidence

### 1. Table Proliferation Verified
```
[TABLE_CREATE #1] new table, total=1, rel=0, bind=1, left_arity=Some(1), right_arity=None
[TABLE_CREATE #2] new table, total=2, rel=0, bind=1, left_arity=Some(0), right_arity=Some(1)
[TABLE_CREATE #3] new table, total=3, rel=0, bind=1, left_arity=None, right_arity=None
...
[TABLE_CREATE #30] new table, total=30, rel=0, bind=1, left_arity=Some(1), right_arity=None
```
**30 tables created** for the SAME relation (`rel=0`) with SAME binding (`bind=1`) but DIFFERENT boundary arities.

### 2. ReplayOnly Mismatch Confirmed
```
[REPLAY_MISMATCH #1] ReplayOnly mode creating NEW table! replay_rel=0 new_rel=0
[REPLAY_MISMATCH #2] ReplayOnly mode creating NEW table! replay_rel=0 new_rel=0
...
[REPLAY_MISMATCH #100] ReplayOnly mode creating NEW table! replay_rel=0 new_rel=0
```
**100+ mismatches** where `replay_rel == new_rel` but boundaries differ, causing new table creation.

### 3. Table Answer Accumulation
```
[TABLE_ADD #1] was_new=true, table_len=1, match_len=1, build_len=1, in_arity=3, out_arity=1
[TABLE_ADD #20] was_new=true, table_len=9, match_len=1, build_len=1, in_arity=4, out_arity=2
[TABLE_ADD #500] was_new=true, table_len=157
[TABLE_ADD #1000] was_new=true, table_len=319
```
Tables accumulate **hundreds of intermediate states** (not final answers), with `in_arity` up to 7.

### 4. Combinatorial Explosion in ComposeWork
```
[COMPOSE 12000] left=Work::Fix right=Fail seen_l=200 seen_r=1 pending=0 pair_queue=0
[COMPOSE 24000] left=Work::Fix right=Fail seen_l=325 seen_r=1 pending=0 pair_queue=0
[COMPOSE 25000] left=Work::Fix right=Fail seen_l=566 seen_r=1 pending=0 pair_queue=0
```
ComposeWork pulls **570+ answers** from tables via Fix, creating O(n²) pair combinations.

### 5. Tables Never Fully Exhaust
```
[TABLE_ITER #1] exhausted: start=0, end=1, has_new=true
[TABLE_ITER #2] exhausted: start=0, end=1, has_new=true
[TABLE_ITER #3] exhausted: start=1, end=1, has_new=false
[TABLE_ITER #4] exhausted: start=1, end=1, has_new=false
```
Only **4 exhaustion events** for 30 tables - most producers never finish before search explodes.

## Exact Bug Location

**File:** `src/work.rs` lines 973-1010

```rust
if let CallMode::ReplayOnly(replay_key) = &self.call_mode {
    if replay_key.as_ref() == &key {
        // Uses existing table (CORRECT)
        return ...;
    }
    // BUG: Falls through when boundaries differ!
    // Should use replay table for same (rel, bind_id)
}
// Creates NEW table (WRONG in ReplayOnly mode for same relation)
let table = self.tables.get_or_create(key.clone());
```

## Mechanical Explanation

1. Query `@(f (f (b l) l) l) ; app` → Table #1 created for `app` with key1
2. Table #1's producer runs in `ReplayOnly(key1)` mode
3. Producer encounters recursive `app` call with different boundary context → key2
4. `key1 != key2` (boundaries differ) → ReplayOnly check fails
5. Code falls through to `get_or_create(key2)` → Table #2 created
6. Table #2's producer in `ReplayOnly(key2)` triggers same bug → Table #3
7. Cascade continues: 30 tables, each with 100s of intermediate answers
8. ComposeWork tries to combine all answers → exponential work → hang

## Why First Answer Works

The first answer is produced through eager/greedy evaluation before the tabling system accumulates enough intermediate states to cause combinatorial explosion. The `next()` call triggers exhaustive search through the accumulated mess.

---

# NEW BUG: Rearchitecture Attempt Failure (January 2026)

## What Was Attempted

Changed ReplayOnly mode to match on `(rel, bind_id)` only (ignoring boundary context), with adaptation via `adapt_prefix_suffix_full`. This was meant to prevent infinite table proliferation by reusing a single table for all recursive calls.

## The New Bug

**21 tests fail with "no answers produced"** instead of infinite tables.

## Root Cause

When ReplayOnly mode finds a matching `(rel, bind_id)` but the table has **0 answers**:

1. `table.all_answers()` returns empty vec
2. `node_from_answers([])` returns `Node::Fail`
3. `ComposeWork(Fail, pipe)` is created
4. `ComposeWork.step()` sees left is Fail, seen_l is empty
5. Returns `WorkStep::Done` immediately (line 1627-1629)
6. Producer iteration exhausts with 0 answers
7. Table never gets seeded with base case answers

## Evidence

```
[HANDLE_CALL] call_mode=false rel=0 bind_id=1 call_left=true call_right=false
[TABLE_CREATE #1] new table, total=1, rel=0, bind=1
[HANDLE_CALL] call_mode=true rel=0 bind_id=1 call_left=true call_right=true
[HANDLE_CALL] ReplayOnly match! Looking up table...
[HANDLE_CALL] Table found, answers_len=0
[HANDLE_CALL] adapt_prefix_suffix_full succeeded: left_prefix=false right_suffix=true
[COMPOSE] Done: left_exhausted with no seen_l
[COMPOSE] Done: left_exhausted with no seen_l
[TABLE_ITER #1] exhausted: start=0, end=0, has_new=false
```

## Mechanical Trace

1. Query: `(cons (s (s (s z))) (s (s z))) ; add`
2. First `handle_call` (Normal): Creates Table for `add` with context A
3. Producer body: `[(cons z $y) -> $y] | [(cons (s $x) $y) -> ... ; add]`
4. Base case `(cons z $y)` doesn't match input `(cons (s ...) ...)`
5. Recursive case matches, produces intermediate, then calls `add`
6. Second `handle_call` (ReplayOnly): Context B (different boundaries)
7. Matches on `(rel, bind_id)` only → uses same table
8. Table has 0 answers → `node_from_answers([])` = `Node::Fail`
9. `ComposeWork(Fail, ...)` returns `WorkStep::Done` immediately
10. Producer exhausts with 0 answers - **base case never reached**

## Why This Approach Fundamentally Fails

The "one table per (rel, bind_id) with adaptation" strategy requires:
- Answers in the table to adapt to different contexts
- When table is empty, there's **nothing to adapt**
- The ComposeWork with Fail returns Done, blocking progress

In contrast, per-context tables allow:
- Each context to explore independently
- The chain of recursive calls eventually reaches a base case
- Answers propagate back up the chain

## Dilemma

**Option A (old behavior)**: Per-context tables → infinite tables for recursive relations
**Option B (new attempt)**: Shared table with adaptation → 0 answers when table starts empty

Neither approach works correctly. A proper solution needs:
1. A way to "wait" when the table is empty (not fail permanently)
2. Or a fundamentally different tabling strategy (e.g., SLG resolution with proper suspension)

## Critical Code Location

`src/work.rs` lines 1627-1629:
```rust
if left_exhausted && self.seen_l.is_empty() && self.pair_queue.is_empty() {
    return WorkStep::Done;  // BUG: Should return "waiting" not "done"
}
```
