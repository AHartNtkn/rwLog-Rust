# Investigation: Packed Bitset Representation for Small-Arity DropFresh Maps

## Summary

Replaced SmallVec-based DropFresh map with packed bitmask for small arities. DISCARD: no measurable improvement — SmallVec<[(u32,u32); 4]> is already efficient for typical 1-3 pair maps.

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 212883 us (median, all values: 218278, 218489, 221977, 214975, 217848, 203559, 210790, 202130, 207637, 200053)
**After:** 212016 us (median, all values: 216208, 213565, 218313, 217842, 208888, 211372, 212660, 205233, 201210, 203479)
**Improvement:** ~0.4% (within noise)
**Mann-Whitney U:** 55/100 (not significant)

## Problem

DropFresh maps use SmallVec<[(u32,u32); 4]> which stores input→output position pairs. The hypothesis was that replacing this with packed bitmasks (two u32 masks for input/output positions) would enable faster O(1) compose via bitwise ops and reduce allocation overhead.

## Why It Failed

1. **SmallVec<[(u32,u32); 4]> is already efficient.** With inline capacity 4, it avoids heap allocation for typical DropFresh maps (1-3 pairs). The packed bitmask eliminates SmallVec overhead but adds enum dispatch overhead, resulting in a wash.

2. **DropFresh map iteration is not a bottleneck.** The map is iterated in compute_rhs_map and a few other places, but with typical sizes of 1-3 pairs, iteration cost is negligible compared to term operations (apply_subst, matching) that dominate compose_nf and meet_nf.

3. **Packed compose (bitwise AND + rank-select) is not faster in practice** because merge-join on 1-3 element sorted lists is already essentially O(1), and bit manipulation adds comparable overhead.

4. **Full corpus comparison** showed no meaningful difference on any of the 40 benchmark cases.

## Files changed

- `src/drop_fresh.rs` — Replaced SmallVec map with DFMap enum (Packed bitmask + Vec fallback)
- `src/nf.rs` — Updated iterator patterns and DFMap construction
- `src/kernel/dual.rs` — Updated iterator patterns, struct construction, and test code
- `src/kernel/compose.rs` — Updated test struct construction
- `src/work/pipe.rs` — Replaced indexing with is_identity() check

## Remaining opportunities

- DropFresh map representation is not a performance bottleneck. The existing SmallVec with capacity 4 is well-suited for typical small arities. This confirms the dropfresh_fuse_chains finding: DropFresh operations are lightweight and not worth further optimization.
- The entire DropFresh optimization category (backlog items #1-#6) appears exhausted: packed bitsets (DISCARD), composition tables (moot — compose never called), canonical interner (moot), identity fast-path (negligible ROI), fuse chains (dead code), cache-friendly layouts (no bottleneck).
