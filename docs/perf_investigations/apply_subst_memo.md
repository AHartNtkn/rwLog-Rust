# Investigation: Thread-Local Memoization Cache for apply_subst

## Summary

Added a thread-local SubstCache that fingerprints substitutions and caches `apply_subst` results. No statistically significant improvement on treecalc_synth_flip.

**Baseline:** 405.33ms (median, all values: 402.38, 405.33, 406.72, 405.83, 407.12, 401.96, 407.89, 402.50, 404.23, 405.34)
**After:** 404.22ms (median, all values: 403.39, 405.59, 402.69, 404.00, 406.62, 403.35, 402.23, 404.46, 404.43, 404.84)
**Improvement:** ~0.28% (within noise)
**Mann-Whitney U:** 62/100 (n.s.)
**Regression:** Not tested (primary workload not significant)

## Problem

`apply_subst` consumes 35.88% of treecalc_synth_flip runtime. The function walks term trees and applies substitutions, frequently seeing the same (term, subst) pair multiple times due to shared subterms and repeated compositions.

## Solution

Added a thread-local memoization cache (`SubstCache`) that:
1. Computes a u64 fingerprint of each `Subst` (XOR-based hash of variable bindings)
2. Uses `(TermId, subst_fingerprint)` as cache key
3. Returns cached result on hit, avoiding the tree walk

Implementation:
- Added `Subst::fingerprint()` method
- Created `SubstCache` struct with `HashMap<(TermId, u64), TermId>` and generation-based invalidation
- Modified `apply_subst`/`apply_subst_shifted` to compute fingerprint and pass to core
- Modified `apply_subst_core` to check cache before tree walk and store results after

## Why 0% instead of 10-20%

The overhead of cache operations (fingerprint computation, HashMap lookup, HashMap insert) is comparable to the work saved by cache hits:

1. **Fingerprint cost**: Computing a u64 hash of the substitution requires iterating all bindings — O(n) where n is the substitution size
2. **Cache lookup cost**: HashMap lookup with (TermId, u64) key has non-trivial overhead per call
3. **Cache hit rate**: Unknown, but even with high hit rates, the per-call overhead eats the savings
4. **apply_subst fast path**: The existing code already has efficient fast paths (ground bit check, inline variable check) that bypass most of the tree walk for simple terms. The cache only helps for complex non-ground terms, which are a minority of calls.

The fundamental issue is that `apply_subst` is called millions of times with small, cheap terms. The cache overhead per-call exceeds the savings for the majority of calls, even though the cache would help for the expensive minority.

### Key design decisions

1. **Fingerprint-based keying** — Chose XOR-based fingerprint over full substitution comparison. This trades collision risk for speed, but the fingerprint computation itself is still O(n).
2. **Thread-local cache** — Avoids synchronization overhead but means no sharing across threads (not relevant for this single-threaded workload).

## Files changed

- `src/subst.rs` — Added `Subst::fingerprint()`, `SubstCache` struct, thread-local `SUBST_CACHE`, modified `apply_subst_core` to use cache

## Remaining opportunities

- **Structural sharing**: Instead of caching individual apply_subst results, use persistent data structures (e.g., hash-consed terms) so that identical subterms share memory and apply_subst naturally deduplicates via pointer identity.
- **Lazy substitution**: Instead of eagerly applying substitutions, represent "term + pending substitution" as a composite and only resolve when the result is needed. This could eliminate many redundant applications.
- **Substitution composition**: Instead of applying substitutions one at a time through the pipeline, compose substitutions algebraically and apply once.
