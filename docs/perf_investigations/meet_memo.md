# Investigation: Meet NF Memoization by Canonical Pair Fingerprints

## Summary

Investigated memoizing meet_nf results to skip duplicate (a,b) pairs. DISCARD: U=18/100 (7% slower). Cache overhead exceeds savings despite 12.1% duplication rate.

**Primary workload (join_high_overlap_64x64, 200 iters):**
**Baseline:** 603 us (median, all values: 594, 596, 600, 600, 605, 606, 614, 629, 845, 927)
**After:** 647 us (median, all values: 643, 645, 645, 645, 646, 647, 648, 651, 728, 952)
**U statistic:** 18/100 (optimized is consistently slower)

## Problem

Hypothesis: meet_nf has higher duplication than compose_nf (which had 0.02%) because DiagonalJoin generates symmetric pairs — meet(a,b) and meet(b,a) from the two growing sets.

## Duplication Rate Analysis

| Benchmark | meet_attempts | unique_pairs | duplicates | dup_rate |
|---|---|---|---|---|
| join_high_overlap_64x64 | 4096 | 3600 | 496 | 12.1% |
| join_low_overlap_64x64 | 4096 | 4096 | 0 | 0.0% |
| parallel_and_32x32_overlap16 | 1024 | 904 | 120 | 11.7% |
| treecalc_synth_flip | 241 | 189 | 52 | 21.6% |
| treecalc_first16 | 7 | 5 | 2 | 28.6% |

**Critical finding:** Without symmetric hashing (treating (a,b) and (b,a) as the same key), the primary benchmark showed 0% duplication. The 12.1% comes entirely from (a,b)/(b,a) orderings in DiagonalJoin.

## Why It Didn't Work

1. **Low absolute duplication**: Only 496 of 4096 meet pairs are duplicates on the primary benchmark
2. **Cheap failures dominate**: 99.2% of meets fail (4064 of 4096). Failed meets cost essentially nothing due to the root functor precheck (inline TermId comparison), so avoiding them via cache saves negligible time
3. **Cache overhead on every call**: 100% of calls pay hash computation + HashMap lookup cost, but only 12% benefit from a cache hit
4. **Symmetric duplicates fail anyway**: The (a,b)/(b,a) duplicate pairs mostly fail at the root functor precheck — the precheck is cheaper than the cache lookup

## Files Changed

None merged (DISCARD).

## Insights

- Meet_nf memoization is not viable because the root functor precheck (from meet_fuse_reinv, 35% improvement) already makes meet failures essentially free. Caching failures that cost ~2ns to detect adds ~15-20ns overhead per call.
- The 12% symmetric duplication from DiagonalJoin is a real phenomenon but the absolute savings per cached hit (~2ns) is too small to overcome per-call overhead.
- This confirms the meet_index finding: the meet_nf rejection path is at absolute minimum cost. Further meet improvements must target the successful meet path or reduce meet attempt count.
