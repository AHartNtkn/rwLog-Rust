# Investigation: Memoize compose_nf Results by NF Pair Fingerprint

## Summary

Investigated compose_nf memoization for treecalc_synth_flip. DISCARDED before implementation: instrumentation revealed only 0.02% duplicate compose pairs (61 out of 277,985). Cache overhead would far exceed savings.

**Verdict:** DISCARD (not implemented — duplicate rate too low)

## Problem

treecalc_synth_flip performs 277,985 compose attempts with 99% failure rate. The hypothesis was that multiple DiagonalJoin instances across different branches encounter the same NF pairs, and caching compose results would skip redundant computations.

## Investigation

Before implementing the cache, instrumented `compose_nf` to track pair duplication by (Arc pointer, Arc pointer) identity.

### Measured Duplicate Rate

| Metric | Value |
|--------|-------|
| Compose attempts | 277,985 |
| Compose successes | 2,778 |
| Compose failures | 275,207 |
| Unique compose pairs | 277,924 |
| Duplicate calls | 61 |
| Duplication rate | **0.02%** |

**Frequency distribution:**
- 1x called: 277,869 pairs
- 2x called: 52 pairs
- 4x called: 3 pairs

## Why Cache Won't Help

A cache would skip **61 compose_nf calls out of 277,985** (0.02%). The overhead of maintaining a cache — hash computation, lookup, and insertion for every single one of the 277,985 calls — would far exceed the savings from skipping 61 calls. Even at 1 nanosecond per cache operation, that's ~278us of pure overhead to save ~61 compose_nf calls (most of which would be fast failures caught by the root functor precheck).

## Root Cause of Low Duplication

DiagonalJoin already deduplicates NFs via `seen_l_set`/`seen_r_set` (hash-based dedup on incoming NFs). Pair generation within each DiagonalJoin is exhaustive but non-repeating — each (left_idx, right_idx) pair is generated exactly once. Cross-DiagonalJoin deduplication would require a global cache, but different DiagonalJoin instances in treecalc_synth_flip almost never encounter the same NF pairs because CHR constraints make each branch's NFs unique.

## Consistency with Prior Work

A previous investigation (`docs/perf_investigations/compose_meet_memoization.md`) found 21.1% duplication across quick-tier cases, but only because of fixpoint verification re-runs. For treecalc_synth_flip specifically (a stress-tier case), the duplication is essentially zero.

## Files Changed

None (instrumentation was temporary, reverted before reporting).

## Remaining Opportunities

The 99% compose failure rate (275,207 failures out of 277,985) is the real cost center, not duplicates. Reducing the number of pairs GENERATED (via better join strategies, constraint propagation, or work avoidance at the scheduling level) would have much more impact than caching results.
