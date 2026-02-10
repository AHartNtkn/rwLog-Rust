# Investigation: Per-instance ground flag for CInstance

## Summary

Added `all_ground: bool` field to `CInstance` to skip `apply_subst` for fully ground constraint instances. Regressed ~2.6% because the per-instance flag overhead exceeds savings for 1-arg instances.

**Baseline:** 1481295us (median, all values: 1473978, 1508338, 1469544, 1499110, 1486503, 1476086, 1496599, 1521766, 1437968, 1460965)
**After:** 1519393us (median, all values: 1528359, 1542127, 1484440, 1514707, 1555482, 1524080, 1504646, 1530421, 1503497, 1472179)
**Improvement:** -2.6% (regression)
**Mann-Whitney U:** 17/100 (significant regression)
**Regression:** N/A

## Problem

`apply_subst_to_data` iterates all alive CInstance entries and applies substitution to each arg. When all args are already ground (i.e., contain no variables), the substitution is a no-op but still incurs function call overhead per arg. The hypothesis was that a per-instance `all_ground` flag could skip the entire iteration.

## Solution Attempted

Added `all_ground: bool` to `CInstance`, set during construction by checking `TermId::is_ground()` on all args. In `apply_subst_to_data`, `remap_vars`, and `remap_and_apply_subst`, skip instances where `all_ground == true`. After operations that might change groundness, lazily promote the flag.

## Why it failed

1. **Redundant with existing ground-bit check:** `apply_subst` (in `src/subst.rs`) already checks `TermId::is_ground()` (bit 31) as its first operation and returns immediately for ground terms. The per-instance flag duplicates this at a coarser granularity.

2. **1-arg instances negate the benefit:** In treecalc_synth_flip, constraint instances have predicate `no_c(term)` with typically 1 arg. For 1-arg instances, the SmallVec "iteration" is just one load + one call to `apply_subst` (which immediately returns for ground terms via the bit check). The instance-level flag adds an extra field load and branch that costs more than skipping one function call.

3. **CInstance struct size increase:** Adding the `all_ground` field increased CInstance by 1 byte + padding alignment, which may contribute to cache pressure on the hot `inst` Vec iteration in `apply_subst_to_data` and `search_steps_inner`.

4. **Confirmed with second measurement batch:** U=6/100, improvement=-2.5%, with CV of only 1.1%/1.9%, confirming the regression is real and not noise.

## Files changed

- `src/chr/mod.rs` — Added `all_ground: bool` to CInstance, checked in apply_subst_to_data/remap_vars/remap_and_apply_subst, set on construction and lazily promoted after operations.

## Remaining opportunities

- The per-instance ground flag would only pay off for instances with many args (4+) that are all ground, where skipping the SmallVec iteration saves more than the flag overhead. A workload with wider predicates could benefit.
- More impactful: algorithmic changes to avoid calling normalize_owned entirely when constraints are known to be at fixpoint, or reducing rebuild_indexes cost.
