# Investigation: Arc<NF<C>> Wrapping in DiagonalJoin

## Summary

Extended Arc<NF<C>> wrapping from Table answers into DiagonalJoin's seen vectors and dedup sets. Eliminates deep NF clones when inserting into seen_l/seen_r and their dedup FxHashSets. ~5.1% improvement on `recursive_even_backward_first64`.

**Baseline:** 20.71ms (median)
**After:** 19.66ms (median)
**Improvement:** ~5.1% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.01)
**Regression:** None observed on treecalc_first16 (U=100/100, also improved ~6%)

## Problem

From profiling of `recursive_even_backward_first64`:
- `DiagonalJoin::pull_side_in_place` = 11.92% of total time

DiagonalJoin maintains dedup sets (`FxHashSet<NF<C>>`) and seen vectors (`Vec<NF<C>>`) for both sides. When an NF is emitted from one side:
1. The NF is cloned into the dedup set (deep clone for the Hash check and insert)
2. The NF is cloned into the seen vector
3. The NF is paired with entries from the other side for compose/meet

Steps 1-2 involve deep clones of NF (which includes ChrState, SmallVecs, etc.) that are only needed for identity comparison and storage.

## Solution

Changed DiagonalJoin fields to store Arc-wrapped NFs:
- `seen_l: Vec<NF<C>>` → `Vec<Arc<NF<C>>>`
- `seen_r: Vec<NF<C>>` → `Vec<Arc<NF<C>>>`
- `seen_l_set: FxHashSet<NF<C>>` → `FxHashSet<Arc<NF<C>>>`
- `seen_r_set: FxHashSet<NF<C>>` → `FxHashSet<Arc<NF<C>>>`

When an NF is emitted from step_node, it's wrapped in `Arc::new()` once. The dedup set insertion uses `Arc::clone()` (O(1) atomic increment). The seen vector push uses the Arc directly.

The pending queue and pending_set remain as `NF<C>` since those store freshly composed/met results that are unique by construction.

## Files changed

- `src/work/diagonal.rs` — Changed field types and insertion logic for Arc wrapping
- `src/work/meet.rs` — Updated test accessor return types for `seen_l()`/`seen_r()`

## Why 5% instead of 2-4%

The estimated 2-4% was conservative. The actual improvement is larger because:
1. DiagonalJoin is used for both compose (14.1%) and meet paths
2. The deep NF clones were a significant fraction of the pull_side_in_place cost
3. The FxHashSet dedup checks now hash Arc pointers (though Arc<NF<C>> still hashes by NF content for correctness)
