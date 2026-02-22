# Investigation: Selectivity-Aware Join Ordering for MeetWork

## Summary

Added root-tag filtering to MeetStrategy to skip incompatible NF pairs before meet_nf. DISCARD: U=40/100, no improvement. meet_nf's inline root functor precheck is already near-free (~1-2ns per pair), so higher-level filtering adds bookkeeping overhead without savings.

**Primary workload (join_high_overlap_64x64, 200 iters):**
**Baseline:** 593.3 us (mean, all values: 594.822, 599.541, 594.413, 595.238, 594.833, 572.868, 580.415, 599.454, 603.066, 598.360)
**After:** 598.9 us (mean, all values: 599.421, 597.520, 594.128, 628.787, 580.709, 597.371, 600.814, 596.381, 596.351, 597.024)
**Improvement:** -0.9% (slightly slower)
**Mann-Whitney U:** 40/100 (not significant)

## Problem

The hypothesis was that DiagonalJoin/MeetStrategy processes all NF pairs in arrival order regardless of selectivity. By tracking root functor tags per NF and filtering incompatible pairs before calling meet_nf, we could prune the cross-product earlier.

## Solution Attempted

Added root-tag filtering to MeetStrategy: for each NF arriving on either side, track match_root_tag and build_root_tag. In on_new_left/on_new_right, skip the meet_nf call for pairs where either match tags or build tags are incompatible (using same tags_compatible check as ComposeStrategy).

## Why It Failed

1. **meet_nf's inline root functor precheck is already near-free.** The precheck at lines 97-106 of meet.rs uses get_unlocked (zero-overhead pointer deref) and a simple comparison. This costs ~1-2ns per pair.

2. **MeetStrategy-level tag tracking adds overhead.** Computing match_root_tag and build_root_tag for each new NF involves TermStore lookups (same cost as the precheck), plus Vec storage/indexing overhead. The per-pair tag comparison in the loop is comparable to the precheck itself.

3. **Net effect is neutral to slightly negative.** Replacing an O(1) check inside meet_nf with an O(1) check outside meet_nf, but with additional bookkeeping overhead (Vec pushes, tag computation at insertion time).

4. **Third confirmation that meet-level filtering is a dead end.** meet_index (U=66), meet_fail_cache (0% duplication), and now selectivity_join (U=40) all confirm that the meet_nf precheck is at its optimization ceiling.

## Files changed

- `src/work/meet.rs` — Added root-tag tracking and filtering to MeetStrategy

## Remaining opportunities

- Meet-level pair filtering is exhausted — three approaches have failed
- The remaining meet optimization opportunity is reducing the number of NF pairs generated (algorithmic change to how AndGroup combines streams), not filtering pairs more cheaply
- Adaptive join algorithms (hash-join-like, indexed join) from Conjunction #3 remain uninvestigated but face the same fundamental issue: the precheck is already O(1)
