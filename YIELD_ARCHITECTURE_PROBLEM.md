# Yield Processing Architecture and Current Problems

## Overview

This document describes the continuation-passing architecture for query evaluation in rwRust, and the specific bug being encountered with backward queries.

## Core Components

### 1. Task and Continuation Stack (task.rs)

A `Task` represents an in-progress evaluation with:
- `goal`: The current goal being evaluated
- `input`: The current NF (normal form) being transformed
- `kont`: A stack of continuations (Vec<Kont>)
- `state`: Ready, Yielded(NF), Blocked(RelId), or Done

### 2. Continuation Types (Kont)

```rust
enum Kont<C> {
    SeqNext { left_answers: Vec<NF<C>>, remaining: SmallVec<[GoalId; 4]> },
    BothNext { left_answers: Vec<NF<C>>, remaining: SmallVec<[GoalId; 4]> },
    AltNext { remaining: SmallVec<[GoalId; 2]> },
    FixFrame { rel_id: RelId, body: GoalId, fix_goal: GoalId },
}
```

- **SeqNext**: Sequential composition. When a step yields, compose with remaining steps.
- **BothNext**: Conjunction/meet. When a part yields, continue with remaining parts, then meet all.
- **AltNext**: Disjunction. When a branch yields, remember remaining branches for backtracking.
- **FixFrame**: Recursive definition boundary. Marks scope for Call resolution.

### 3. Evaluation Functions (eval.rs)

**`step(task, ctx) -> StepResult`**
- Evaluates one step of the current goal
- For Rule: yields the rule's NF
- For Seq/Both/Alt: pushes continuation, continues with first branch
- For Fix: pushes FixFrame, continues with body
- For Call: returns Blocked(rel_id)

**`resume_after_yield(task, answer, ctx) -> StepResult`**
- Called when a goal has yielded an answer
- Pops top continuation and processes the answer through it
- Returns Continue (more work), Yielded (answer ready), Done, or Blocked

**`backtrack(task, ctx) -> StepResult`**
- Called when we need to find alternative answers
- Pops continuations until finding AltNext with remaining branches
- Returns Continue (try next branch) or Done (no more alternatives)

### 4. Query Loop (api.rs)

```rust
pub fn query(&mut self, goal_id, input, max_steps) -> Vec<Answer> {
    let mut task = create_task(goal_id, input);
    let mut answers = Vec::new();

    for _ in 0..max_steps {
        match step(&mut task, &mut ctx) {
            StepResult::Continue => continue,
            StepResult::Yielded(nf) => {
                // ??? How to handle this ???
            }
            StepResult::Done => break,
            StepResult::Blocked(rel_id) => { /* handle Call */ }
        }
    }
    answers
}
```

## The Problem

### Symptom

Backward query `?- add ; z` returns `(cons z $0) -> $0` instead of `(cons z z) -> z`.

The query means: "enumerate all pairs (x, y) such that add(x) = y, then filter to those where y = z".

Expected: `(cons z z) -> z` (meaning 0+0=0, with output constrained to z)
Actual: `(cons z $0) -> $0` (unconstrained variable, composition didn't happen)

### Root Cause Analysis

The addition relation has structure:
```
add = Fix(add_rel, Alt(base_case, recursive_case))
```

When evaluating `add ; z`:
1. Seq pushes `SeqNext { remaining: [z_rule] }`
2. Fix pushes `FixFrame`
3. Alt pushes `AltNext { remaining: [recursive_case] }`
4. base_case (Rule) yields `(cons z $0) -> $0`

At this point, the kont stack is (bottom to top):
```
[SeqNext { remaining: [z_rule] }, FixFrame, AltNext { remaining: [recursive] }]
```

5. `resume_after_yield` is called with the answer
6. AltNext is popped
7. **BUG**: AltNext pushes itself back and returns `Yielded(answer)`
8. The answer never reaches SeqNext for composition!

### The Semantic Conflict

There are two competing concerns:

**Concern A: Answer Flow**
When AltNext yields an answer, if there's a SeqNext below, the answer should flow DOWN through SeqNext to be composed with the next step.

**Concern B: Backtracking State**
AltNext with remaining branches needs to stay on the stack so that when we backtrack, we can try the remaining branches.

The current implementation prioritizes Concern B: AltNext always pushes itself back before returning. This breaks Concern A because the answer never reaches SeqNext.

### Attempted Fixes and Their Problems

#### Fix 1: Recursive call in AltNext when SeqNext is below
```rust
Kont::AltNext { remaining } => {
    let has_seq_below = matches!(task.peek_kont(), Some(Kont::SeqNext { .. }));
    if has_seq_below {
        let result = resume_after_yield(task, answer, ctx);  // Process through SeqNext
        if !remaining.is_empty() {
            task.push_kont(Kont::AltNext { remaining });  // Push back AFTER
        }
        result
    } else {
        // Original behavior
    }
}
```

**Problem**: This works for the minimal test case, but...

#### Fix 2: Loop in api.rs when Yielded with non-empty kont
```rust
StepResult::Yielded(nf) => {
    loop {
        if task.kont_is_empty() {
            answers.push(nf);
            backtrack(&mut task, &mut ctx);
            break;
        } else {
            match resume_after_yield(&mut task, nf, &mut ctx) {
                StepResult::Yielded(nf2) => nf = nf2,  // Continue looping
                StepResult::Continue => break,
                _ => break,
            }
        }
    }
}
```

**Problem**: Infinite loop! When AltNext has no SeqNext below:
1. AltNext returns Yielded, pushes itself back
2. Loop sees kont not empty, calls resume_after_yield
3. Pops AltNext, returns Yielded, pushes itself back
4. Loop sees kont not empty... infinite!

#### The Fundamental Issue

The continuation stack serves two purposes:
1. **Forward processing**: Determining how to handle an answer (compose, meet, etc.)
2. **Backtracking state**: Remembering alternatives to try later

These are conflated. When AltNext returns Yielded:
- For forward processing: "I'm done with this answer, pass it along"
- For backtracking: "But remember me for later"

The api.rs loop can't distinguish "Yielded and done processing" from "Yielded but more konts to process".

## Possible Solutions

### Solution A: Separate the concerns

Have two stacks:
- `kont`: For forward answer processing
- `choice_points`: For backtracking alternatives

When AltNext yields, it would NOT be on the kont stack, but its remaining branches would be saved as a choice point.

**Pros**: Clean separation of concerns
**Cons**: Significant refactoring

### Solution B: Mark Yielded as "final" or "intermediate"

```rust
enum StepResult {
    Continue,
    FinalYield(NF),      // Answer is ready, collect it
    IntermediateYield(NF), // Answer needs more processing
    Done,
    Blocked(RelId),
}
```

AltNext would return FinalYield when there's no SeqNext below.

**Pros**: Explicit semantics
**Cons**: Adds complexity to StepResult

### Solution C: Check kont type, not just emptiness

In api.rs, instead of checking `kont_is_empty()`, check if the top kont is one that needs further processing:

```rust
fn needs_yield_processing(task: &Task) -> bool {
    match task.peek_kont() {
        Some(Kont::SeqNext { .. }) | Some(Kont::BothNext { .. }) => true,
        Some(Kont::AltNext { .. }) | Some(Kont::FixFrame { .. }) | None => false,
    }
}
```

**Pros**: Minimal change
**Cons**: Duplicates logic between api.rs and eval.rs

### Solution D: AltNext doesn't push back during yield

Change AltNext to NOT push itself back when yielding. Instead, save the remaining branches in the Task struct for backtrack to restore.

```rust
Kont::AltNext { remaining } => {
    if has_seq_below {
        // Save remaining for backtrack, then process through SeqNext
        task.save_alt_choice(remaining);
        resume_after_yield(task, answer, ctx)
    } else {
        // Save remaining for backtrack, yield as final
        task.save_alt_choice(remaining);
        StepResult::Yielded(answer)
    }
}
```

**Pros**: Kont stack only has forward-processing konts
**Cons**: Requires changes to Task and backtrack logic

## Current State

- eval.rs: AltNext has recursive processing for SeqNext below, pushes back after
- api.rs: Has loop that continues on Yielded when kont is not empty
- Result: Infinite loop when AltNext has no SeqNext below

The tests that are failing:
- All addition tests (9 tests)
- All treecalc tests (9 tests)
- All symmetry tests (7 tests)
- Various integration tests

## Questions for Resolution

1. Should the kont stack serve both forward processing AND backtracking, or should these be separated?

2. When AltNext yields a "final" answer (no SeqNext below), should the kont stack be empty from the perspective of the api.rs loop?

3. Is the recursive call approach in AltNext correct, or should all yield processing happen in api.rs?
