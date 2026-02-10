# Investigation: Inline constraint matching before CHR store in single-head simplification

## Summary

In single-head simplification, try matching newly created constraints against rules BEFORE adding them to the ChrStore. Matched constraints are consumed immediately via recursive DFS execution, bypassing the store/agenda roundtrip entirely. Only unmatched constraints are stored.

**Baseline:** 1103213us (median, all values: 1141273, 1131198, 1087948, 1111459, 1088290, 1089542, 1094967, 1083614, 1121949, 1121141)
**After:** 849936us (median, all values: 859463, 844496, 849465, 838578, 837831, 850406, 848455, 870960, 878936, 876276)
**Improvement:** ~23.0% (same-session comparison)
**Mann-Whitney U:** 100/100 (complete separation, p < 0.0001)
**Regression:** None observed on recursive_even_backward_first64 (U=46/100, neutral)

## Problem

In the CHR single-head simplification fixpoint loop, every new constraint created by rule body execution went through this cycle:

1. `add_chr(cid, pred, &av, terms, specs)` — stores constraint in ChrStore (pushes to inst Vec, extends all_args Vec)
2. `agenda.push_back(cid)` — enqueues for processing
3. (Later) `agenda.pop_front()` — dequeues
4. `store.inst[cid]` + `store.args(inst)` — looks up constraint data
5. `match_head(terms, head, flat_ops, inst, inst_args, env)` — tries matching
6. If match: `store.mark_dead(cid)` — marks as dead, then executes body

For the majority of constraints in treecalc, a rule matches immediately. Steps 1-4 and 6 were pure overhead — the constraint was created, stored, enqueued, dequeued, looked up, matched, and immediately killed, all within a single fixpoint iteration.

## Solution

Added three new functions to `src/chr/mod.rs`:

1. **`match_head_direct(terms, head, flat_ops, pred, args, env)`** — Like `match_head` but takes predicate and args directly instead of going through `&CInstance`. Avoids the store lookup indirection.

2. **`try_inline_match(pred, args, terms, program, data, env)`** — Tries matching a constraint against all triggered rules. Uses the same indexing (by_functor + fallback) as the fixpoint loop. Returns `Ok(true)` if a rule matched and fired, `Ok(false)` if no match (caller stores), or `Err(())` on failure.

3. **`exec_body_inline(body, pats, terms, reg, env, program, data)`** — Executes a rule body with inline matching: for each `BodyInstr::AddChr`, calls `try_inline_match` before storing. Matched constraints are consumed recursively (DFS). Unmatched constraints are stored via `add_chr` but NOT pushed to the agenda (all rules were already tried).

The `solve_to_fixpoint_single_head` function was modified to call `exec_body_inline` instead of `Body::exec_with_data` after a rule fires.

### Key design decisions

1. **DFS (recursive) instead of BFS (agenda-based) for matched constraints:** When a rule fires and its body creates new constraints, those constraints are matched immediately in a depth-first manner. This changes the processing order from BFS to DFS but is safe for single-head simplification (the system is confluent). DFS is more cache-friendly since related work stays hot in cache.

2. **Separate RVarEnv for inline matching:** `exec_body_inline` allocates a separate `match_env` for inline matching to avoid clobbering the caller's env. This env is reused across AddChr instructions within the same body.

3. **No agenda push for unmatched constraints:** When `try_inline_match` returns `Ok(false)`, the constraint is stored via `add_chr` but NOT pushed to the agenda. Since all triggered rules were already tried, pushing to the agenda would cause redundant re-matching. These constraints simply persist in the store.

## Files changed

- `src/chr/mod.rs` — Added `match_head_direct`, `try_inline_match`, and `exec_body_inline` functions. Modified `solve_to_fixpoint_single_head` to use `exec_body_inline` for body execution after a rule fires.

## Why 23% instead of 2-4%

The original estimate of 2-4% was based on profiled costs of individual operations (add_chr 1.57%, memmove 1.86%, mi_heap_malloc 1.54%). The actual improvement was dramatically higher due to compounding effects:

1. **Eliminated store operations for the vast majority of constraints.** In treecalc, most constraints created by rule bodies immediately match another rule. These constraints previously went through the full add_chr → agenda → lookup → match → mark_dead cycle. Now they skip all of it.

2. **DFS execution order is cache-friendlier.** The old BFS (agenda-based) approach spread related work across time, causing cache pollution. The new DFS approach processes each constraint chain to completion, keeping working data (TermStore nodes, program rules, env vars) hot in L1/L2 cache.

3. **Reduced Vec growth pressure.** `all_args.extend_from_slice` and `inst.push` for matched constraints caused frequent Vec reallocations and memmoves. Eliminating these for matched constraints dramatically reduces allocation pressure.

4. **Reduced memory footprint.** The ChrStore's inst Vec and all_args Vec grow much less, improving data locality for the remaining store operations. Dead constraints no longer bloat the store.

5. **Eliminated agenda overhead.** The VecDeque push_back/pop_front operations, while individually cheap, added up across thousands of constraints. More importantly, the agenda interleaved constraints from different rule firings, causing poor locality.

## Remaining opportunities

- The initial constraints from `solve_to_fixpoint_single_head` (popped from the global agenda before the first rule fires) still go through the store → agenda path. The inline matching only applies to constraints created by body execution AFTER the first rule fires.
- The `try_inline_match` function still acquires `terms.read_lock()` for each match attempt via `match_head_direct`. A lock-free variant using `terms.nodes.get_mut()` could eliminate this overhead.
- The recursive DFS approach has unbounded stack depth in theory. An iterative approach with an explicit worklist could handle pathological cases, though treecalc's bounded recursion depth makes this a non-issue in practice.
