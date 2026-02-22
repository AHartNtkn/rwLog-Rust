# Investigation: Cache Branch Failure Signatures

## Summary

Investigated caching branch failure signatures to prune repeated dead search paths. DISCARD at instrumentation phase: prior investigations (compose_fail_cache, compose_memo) already prove <0.02% failure overlap on treecalc_synth_flip. CHR constraints make each branch's NF state unique, preventing structural overlap. No code changes made.

## Problem

The hypothesis was that many branches fail for the same structural reason (same NF shapes, same constraints producing the same compose_nf failures), and caching failure fingerprints could prune entire subtrees before stepping into them. This would attack the 99% compose failure rate from a new angle — avoiding branches that are structurally identical to known failures.

## Why It Failed

1. **Prior data conclusively disproves the hypothesis.** compose_fail_cache (prior investigation) showed 0% cache hit rate on treecalc workloads with -1.21% regression from overhead. compose_memo showed only 61 duplicates out of 277,985 compose attempts (0.02%).

2. **CHR constraints create unique states per branch.** Even branches that fail for "structurally similar" reasons (same functor shapes) differ in their constraint states, making fingerprints unique.

3. **Branch-level fingerprints would have even lower overlap.** If individual compose NF pairs show 0.02% overlap, branch-level fingerprints (incorporating multiple NF pairs, DropFresh states, Pipe states) would be even more specific and have lower hit rates.

4. **DiagonalJoin already deduplicates per-instance.** The existing seen_l_set/seen_r_set in DiagonalJoin prevent duplicate compose pairs within each join instance.

## Files changed

None — discarded at instrumentation phase based on prior data.

## Remaining opportunities

- Branch failure caching is a dead end for this workload — CHR constraints make each state unique
- The 99% compose failure rate is already addressed by root functor precheck (O(1)) and var_range skip
- Further work-avoidance for compose failures would require changing the search strategy itself, not caching failures
