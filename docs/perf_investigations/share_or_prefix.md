# Investigation: Share Normalized Prefix Work Among Sibling Or Branches

## Summary

Investigated whether Or-branch splitting could avoid redundant normalization by sharing common prefix computations. DISCARD: U=56/100, no improvement. The architecture already uses Arc sharing pervasively — clone during split_or is already O(1) for all significant structures, and compose_nf calls are inherently different per branch.

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 208350 us (mean, all values: 207599, 203884, 206542, 210081, 210891, 207587, 210094, 209513, 213101, 204213)
**After:** 207465 us (mean, all values: 204661, 202869, 210809, 204216, 212422, 213785, 204943, 204334, 209821, 206789)
**Improvement:** ~0.4% (within noise)
**Mann-Whitney U:** 56/100 (not significant)

## Problem

The hypothesis was that when PipeWork::split_or creates Or branches, each branch independently re-normalizes shared pipeline state. If sibling branches share a common prefix (same left-side NF chain), that normalization work could be cached or shared via Arc-wrapping.

## Solution Attempted

Arc-wrapped the `dispatch_cache` in PipeWork for O(1) clone sharing across Or siblings. When PipeWork is cloned during split_or, siblings share the dispatch table HashMap via Arc instead of deep-cloning it. Mutations use Arc::make_mut for copy-on-write.

## Why It Failed

1. **dispatch_cache is typically None at split time.** The cache is lazily allocated and only populated when a Call has a flat-Or-of-Atoms body AND a boundary NF exists. At the split_or point, it's usually empty, so cloning is already free.

2. **All significant structures already use Arc.** NF boundaries and Factors already use Arc (clone is O(1)). Env and Tables already use Arc (clone is O(1)). There's nothing expensive left to share.

3. **compose_nf calls are inherently different per branch.** Each Or branch has a distinct atom, so the compose operations differ per branch. There's no structural redundancy to exploit through caching.

4. **The flat profile confirms no single bottleneck.** No function exceeds 5% self-time. The architecture already handles sharing well through pervasive Arc usage.

## Files changed

- `src/kernel/pipe.rs` — Arc-wrapped dispatch_cache in PipeWork

## Remaining opportunities

- Or-branch sharing is effectively solved by the existing Arc architecture
- The remaining Disjunction optimization targets (branch pruning #4, batch stepping #5) address different aspects than sharing
- The flat profile means further gains require algorithmic changes (reducing total work), not sharing optimizations
