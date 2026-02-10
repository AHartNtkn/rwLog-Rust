# Investigation: CHR duplicate-argument precheck in normalize_owned

## Summary

Attempted to add a precheck in `normalize_owned` that examines per-predicate constraint args to skip the fixpoint loop when no rule can fire. No improvement — slightly worse.

**Baseline:** 1457446us (median, all values: 1434605, 1461486, 1443177, 1483362, 1451088, 1456507, 1466320, 1448275, 1458384, 1463037)
**After:** 1472749us (median, all values: 1440352, 1475487, 1485470, 1475140, 1430477, 1473345, 1472152, 1493639, 1467184, 1434234)
**Improvement:** -1.05% (slightly worse, noise)
**Mann-Whitney U:** 34/100 (not significant)
**Regression:** N/A

## Problem

`normalize_owned` with watermark=0 enqueues all alive constraints and runs `solve_to_fixpoint`, which iterates all enqueued constraints trying to match each against all applicable rules. When no rule can fire (e.g., because no predicate has enough constraints with matching argument patterns), this O(N^2) work is wasted. The hypothesis was that checking argument indexes first could skip the fixpoint entirely.

## Solution Attempted

Added `can_any_enqueued_fire()` method that, for each predicate with enqueued constraints, checks whether any rule's IndexedTriggers could match by examining the first-argument functor of enqueued constraints against the trigger table. If no predicate has any potential match, skip `solve_to_fixpoint`.

## Files changed

- `src/chr/mod.rs` — Added `can_any_enqueued_fire()` and precheck gate before `solve_to_fixpoint`.

## Why it failed

1. **The brief's premise was incorrect**: The hypothesis assumed multi-head rules like `no_c X, no_c X <=> fail`, but treecalc_synth_flip only has single-head simplification rules (`(no_c l) <=> .`, `(no_c (b $x)) <=> (no_c $x)`, etc.). There are no multi-head rules requiring duplicate argument matching.

2. **IndexedTriggers dispatch already handles this**: For single-head rules with specific first-arg functors, the `by_functor` HashMap lookup in `solve_to_fixpoint` already skips non-matching constraints efficiently. The precheck duplicated this same check.

3. **Precheck adds overhead**: Iterating all enqueued constraints to check arg functors before the fixpoint loop adds cost that isn't recouped when the fixpoint loop itself is already efficient.

4. **No ArgTerm indexes exist in this workload**: The parser produces empty `index_specs` for all predicates in treecalc, so the ArgTerm-based precheck path was never exercised.

## Remaining opportunities

- For workloads with actual multi-head rules and large constraint stores, a precheck based on predicate-count thresholds (e.g., need at least 2 constraints of predicate P for a 2-head rule on P) could avoid unnecessary fixpoint work.
- More impactful: track which constraints changed in `apply_subst_to_data` and only enqueue those, rather than watermark=0 re-enqueueing all alive constraints.
