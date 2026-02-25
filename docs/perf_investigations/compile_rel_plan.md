# Investigation: Compile Rel Definitions into Cached Execution Plans

## Summary

Investigated compiling Rel definitions into cached execution plans to avoid redundant Rel tree traversal. DISCARD: U=61/100, no improvement. Rel dispatch is already very cheap (enum matching + Arc cloning). Prior optimizations already cover the main compilation targets (pipe_batch_advance, cached_dispatch_table, compose_chain_fuse). The bottleneck is compose_nf failures (99% failure rate), not Rel traversal.

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 213421 us (median, all values: 207280, 214790, 215693, 216857, 212704, 213449, 213393, 209375, 216253, 209955)
**After:** 211750 us (median, all values: 211777, 203206, 210153, 217982, 210432, 211722, 213193, 213520, 213337, 210154)
**Improvement:** 0.78% (within noise)
**Mann-Whitney U:** 61/100 (not significant)

## Problem

The hypothesis was that Rel trees are re-traversed from scratch each time they're evaluated via Call resolution, and compiling them into a cached representation could eliminate redundant enum traversal overhead.

## Solution Attempted

Changed `from_rel_with_boundaries` in pipe.rs to use Factors rope directly instead of building a Vec, avoiding one allocation per call. This was the only concrete optimization found after thorough analysis.

## Why It Failed

1. **Most compilation targets already covered by prior optimizations.** Single-Atom bodies: pipe_batch_advance (81.6%). Or-of-Atoms bodies: cached_dispatch_table (47%). Deterministic wrapper chains: compose_chain_fuse (34.7%).

2. **Rel::Clone is cheap.** All inner fields are Arc-wrapped, so "re-evaluating" a Rel tree is just matching on enum variants and cloning Arc pointers. There is no expensive tree traversal to cache away.

3. **The real bottleneck is compose_nf failures.** treecalc_synth_flip does 277,985 compose attempts with only 2,778 successes (99% failure rate). The overhead is in the compose kernel, not Rel dispatch/construction.

4. **from_rel_with_boundaries overhead is negligible.** Even eliminating its Vec allocation showed no measurable impact on a 212ms workload.

## Files changed

- `src/work/pipe.rs` — Changed from_rel_with_boundaries to avoid Vec allocation

## Remaining opportunities

- General Rel compilation is a dead end — Rel dispatch is already lightweight (Arc cloning)
- The remaining opportunity in Major Proposal 1 (AOT compilation) is about specialized execution strategies, not caching Rel trees
- The 99% compose failure rate remains the dominant cost center, addressed by precheck and normalize cache optimizations
