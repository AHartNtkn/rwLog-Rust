# Investigation: Cache Failed meet_nf Pairs to Skip Repeated Impossible Intersections

## Summary

Instrumented meet_nf to measure pair duplication rate across all meet-heavy workloads. DISCARD: 0% duplication on all join workloads. The AndJoiner generates each (left, right) pair exactly once via incremental cross-product, so there are no repeated failures to cache.

**No performance measurement needed** — instrumentation showed the optimization has no opportunity to help.

## Problem

On meet-heavy workloads (join_high_overlap), meet_nf is called thousands of times. The hypothesis was that the same (NF_a, NF_b) pair might fail meet_nf from different search branches, and caching the failure could avoid re-running the matching pipeline.

## Instrumentation Data

| Case | Meet Attempts | Unique Pairs | Dup% | Success Rate |
|------|-------------|-------------|------|-------------|
| join_high_overlap_64x64 | 4096 | 4096 | **0%** | 1% |
| join_low_overlap_64x64 | 4096 | 4096 | **0%** | 0% |
| parallel_and_32x32_overlap16 | 1024 | 1024 | **0%** | 2% |
| join_skewed_128x4 | 512 | 512 | **0%** | 1% |
| conjunction_cross_16x16 | 256 | 256 | **0%** | 0% |
| treecalc_synth_flip | 241 | 190 | 21% | 97% |
| failfast_conjunction | 32 | 32 | **0%** | 3% |
| treecalc_first16 | 7 | 5 | 29% | 100% |
| conjunction_selective | 6 | 6 | **0%** | 17% |

## Why It Failed

1. **AndJoiner generates each pair exactly once**: `enqueue_meets()` uses incremental cross-product — when element `i` arrives on the left side, it pairs with all previously-seen right elements. No (a, b) pair is ever generated twice.

2. **Architecturally identical to compose_fail_cache**: The compose_fail_cache investigation (DISCARD) found 0% compose duplication for the same reason — cross-product pairs are generated exactly once by the DiagonalJoin.

3. **Only treecalc cases show any duplication**: treecalc_synth_flip has 21% duplication across 241 meet calls, but with 97% success rate only ~7 failures occur total. Caching would save 1-2 calls at most.

4. **Root functor precheck already fast-rejects**: The existing `meet_root_functor_mismatch` precheck (meet.rs lines 39-71) rejects most failures in O(1) by comparing root functors. For join workloads, all NFs have distinct root constructors, so failures are caught before any expensive matching pipeline runs.

## Files changed

None — instrumentation only, no code changes committed.

## Remaining opportunities

- Meet performance on join workloads is already dominated by the sheer number of cross-product pairs (4096 for 64x64), not by repeated work on the same pairs
- Further meet optimization would need to reduce the number of pairs attempted (e.g., via indexing/discrimination) rather than caching results
- The root functor precheck is already highly effective at fast-rejecting incompatible pairs
