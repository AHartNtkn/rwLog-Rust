# Investigation: Fuse constraint apply_subst + combine + normalize into single operation

## Summary

Attempted to fuse the 4-step constraint pipeline in compose_nf (apply_subst + remap_and_apply_subst + combine_owned + normalize_owned) into a single `compose_constraint` method. Eliminates intermediate ChrStateData clones and Arc allocations for the (Some, Some) case. Not statistically significant.

**Baseline:** 950930us (median, all values: 1429228, 946181, 954282, 883501, 825652, 1093258, 1119860, 947578, 924645, 1113443)
**After:** 933026us (median, all values: 972349, 913198, 919802, 809164, 819858, 1408816, 946250, 985624, 1308843, 908224)
**Improvement:** ~1.9% (not significant)
**Mann-Whitney U:** 60/100 (not significant, p > 0.05)
**Regression:** N/A (primary did not pass threshold)

## Problem

In compose_nf, the constraint pipeline performs 4 separate operations that each may clone ChrStateData:
1. `a.constraint.apply_subst(subst_left)` — clones a's data, walks args
2. `b.constraint.remap_and_apply_subst(map, subst_right)` — clones b's data, walks args
3. `combine_owned(a_constraint, b_constraint)` — merges stores
4. `normalize_owned(combined)` — runs CHR to fixpoint

For the (Some, Some) case, this creates 2 ChrStateData clones and walks b's args twice.

## Solution Attempted

Added `compose_constraint` method to ConstraintOps trait that fuses all 4 steps. For the (Some, Some) case: clones a's data once, applies subst_left, then merges b's constraints inline (applying remap + subst_right per-arg during copy), then normalizes.

## Why it was discarded

1. **The (Some, Some) case is less common than expected.** Many compose successes have one or both constraints as None, already handled by early returns.

2. **High measurement variance.** Timings ranged from ~809K to ~1.4M us (CV ~17-20%), making it impossible to reliably detect a ~2% effect with N=10.

3. **Savings per-call are tiny.** The fusion saves 1 ChrStateData clone + 1 Arc::new + 1 arg walk pass. For stores with at most ~19 entries, these are microseconds each. With only 2787 compose successes, total savings are ~5-10ms out of ~950ms.

4. **The builtin merging API limits fusion depth.** Theory builtins still require separate remap and merge operations, limiting how much can be fused.

## Files changed

- `src/constraint.rs` — Added `compose_constraint` default method to ConstraintOps trait
- `src/chr/mod.rs` — Added fused `compose_constraint` override for ChrState
- `src/kernel/compose.rs` — Updated compose_nf_impl to use the fused method

## Remaining opportunities

- The constraint pipeline overhead is real but small in absolute terms. The 15.77% ChrState::apply_subst cost is dominated by the actual tree-walking apply_subst calls on constraint args, not by cloning or allocation overhead.
- A lazy constraint application approach (deferring substitution until normalize) could save more, but requires architectural changes to the ConstraintOps trait.
