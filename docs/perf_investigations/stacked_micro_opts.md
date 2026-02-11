# Investigation: Stacked Micro-Optimizations

## Summary

Combining three individually sub-threshold micro-optimizations produced a cumulative 3.7% improvement on treecalc_synth_flip, with no regression on secondary workloads.

**Baseline:** 71802.113 us (median, all values: 73804.844, 73460.238, 73179.823, 71764.944, 71885.433, 70486.822, 70952.514, 71839.282, 70548.718, 71633.238)
**After:** 69122.925 us (median, all values: 70268.315, 69553.863, 69993.814, 68691.988, 68174.015, 67528.972, 67536.387, 67875.309, 71550.280, 69962.311)
**Improvement:** ~3.7% (same-session comparison)
**Mann-Whitney U:** 97/100 (p < 0.001)
**Regression:** None observed on recursive_even_backward_first64 (U=80/100, +2.0% improvement)

## Problem

After 43 rounds of optimization, individual micro-optimizations in the CHR constraint engine were producing real but sub-threshold improvements (~2-3% each). The reuse_pat_vecs investigation (Round 43) measured U=72/100 — just 1 point below the 73 significance threshold — suggesting a real effect masked by timing variance. The hypothesis: stacking multiple small wins would produce a cumulative effect that crosses the significance threshold.

## Solution

Three changes implemented together:

### Change 1: SmallVec in instantiate_pat (~2-3% estimated)

Replaced heap-allocated `Vec` with stack-allocated `SmallVec<[_; 8]>` in `instantiate_pat` for both the traversal stack and output buffer. Pattern trees rarely exceed 8 nodes, so the stack buffer covers the vast majority of cases, eliminating malloc/free on every call.

### Change 2: Ground pre-check in apply_subst_to_data (~0.5-1% estimated)

Added `if arg.is_ground() { continue; }` before calling `apply_subst(*arg, subst, terms)` in the apply_subst_to_data loop. While `apply_subst` already checks `is_ground()` internally, the pre-check avoids function call overhead (setup, stack frame) for ground args. The pre-check is a single inlined bitwise AND vs a full non-inlined function call.

### Change 3: #[inline(always)] on hot matching functions

Upgraded `match_flat_ops` and `match_head_direct` from `#[inline]` to `#[inline(always)]`, forcing the compiler to always inline these tight-loop CHR matching functions at their call sites.

### Key design decisions

1. Stacking approach: Individually, none of these changes would reach significance on this benchmark. Combined, the cumulative effect (3.7%) is clearly significant (U=97).
2. SmallVec<8> capacity: Matches pattern tree depths in treecalc (shallow trees). Same capacity as the match_flat_ops stack.
3. Ground pre-check placement: Before the function call, not inside it, to avoid the function call setup entirely.

## Files changed

- `src/chr/mod.rs` — SmallVec in instantiate_pat, ground pre-check in apply_subst_to_data, #[inline(always)] on match_flat_ops and match_head_direct

## Why 3.7% instead of more

Each individual change targets a small fraction of total runtime:
- instantiate_pat is only called for ArgExpr::Pat variants (most args are ArgExpr::RVar, O(1) lookup)
- The ground pre-check only saves function call overhead (~5-10ns per ground arg)
- The inline hints may already be applied by LTO in some cases

The cumulative 3.7% matches the sum of estimated individual contributions (2-3% + 0.5-1% + 0.5-1% = 3-5%).

## Remaining opportunities

- The stacking approach suggests other near-threshold optimizations could be combined in future rounds.
- PGO (Profile-Guided Optimization) showed 14% improvement on treecalc_synth_flip but with a 3.2% regression on recursive_even_backward_first64. A multi-workload PGO training approach could potentially capture the 14% without regression.
- The remaining hotspots (apply_subst at 38.45%, exec_body_inline at 9.35%) are dominated by irreducible computation.
