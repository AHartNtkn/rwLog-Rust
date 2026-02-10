# Investigation: SmallVec for Subst Bindings

## Summary

Replacing Vec<Option<TermId>> with SmallVec<[Option<TermId>; 16]> in Subst to eliminate heap allocation for typical substitutions showed a directional 1.1% improvement but failed to reach statistical significance. DISCARDED.

**Baseline:** 70352.152 us (median, all values: 72286.855, 73190.518, 70352.152, 70625.599, 70550.339, 70204.414, 69509.863, 69838.792, 71791.027, 70340.196)
**After:** 69575.738 us (median, all values: 72529.622, 69907.916, 69255.442, 68887.038, 70125.296, 69575.738, 69268.949, 69036.158, 72120.683, 73088.646)
**Improvement:** ~1.1% (not significant)
**Mann-Whitney U:** 69/100 (p > 0.05, not significant)
**Regression:** N/A (primary failed threshold)

## Problem

Every compose attempt creates a Subst via Subst::with_capacity(combined_var_count), allocating a Vec of Option<TermId> on the heap. With ~64K compose calls per treecalc_synth_flip query, this means ~64K malloc/free pairs of 40-80 byte allocations. The hypothesis was that stack-allocating these via SmallVec would eliminate the allocation overhead.

## Solution

Changed `Subst::bindings` from `Vec<Option<TermId>>` to `SmallVec<[Option<TermId>; 16]>`. The capacity of 16 covers virtually all tree calculus substitutions (NFs have 2-5 variables per side, so combined substitutions need ~5-10 slots).

### Key design decisions

1. Capacity 16: Covers all practical cases for tree calculus. Option<TermId> is 4 bytes (TermId is u32 with niche optimization), so inline storage = 64 bytes.
2. SmallVec provides the same API as Vec (Deref<Target=[T]>), so all callers work unchanged.
3. The with_capacity constructor uses SmallVec::from_elem(None, n) instead of vec![None; n].

## Files changed

- `src/subst.rs` -- Changed bindings field type, updated new() and with_capacity() constructors

## Why only 1.1%

mimalloc is already extremely efficient at small allocations (~15-20ns per alloc/free). Eliminating 64K allocations × ~30ns (malloc+free) = ~2ms savings out of ~70ms total = ~2.8% theoretical maximum. The observed 1.1% is consistent with:

1. Not all 64K Substs are created fresh -- some paths reuse or skip allocation.
2. SmallVec<16> increases Subst stack size from 24 bytes (Vec) to ~72 bytes. The larger struct may affect cache behavior when multiple Substs are alive simultaneously.
3. The coefficient of variation (~3-4%) means the ~1.1% signal is within measurement noise at N=10.

## Remaining opportunities

- **Combine with stacked_micro_opts_2**: The stacked_micro_opts_2 investigation showed a similar ~1.73% borderline improvement from three other micro-optimizations. Combining all changes might produce ~2.8% cumulative improvement.
- **Smaller SmallVec capacity**: SmallVec<[Option<TermId>; 8]> would reduce stack size to ~40 bytes while still covering most cases. This might improve cache behavior.
- The optimization landscape is approaching diminishing returns for allocation-level changes. mimalloc's efficiency makes allocation elimination a diminishing-returns strategy.
