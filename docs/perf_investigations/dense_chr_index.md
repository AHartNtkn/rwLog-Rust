# Investigation: Dense Vec-based CHR predicate indexing

## Summary

Replaced HashMap-based CHR predicate indexing with dense Vec-based O(1) lookup. No significant improvement on primary workload.

**Baseline:** 1208313us (median, all values: 1207542, 1222039, 1208782, 1207844, 1194238, 1332893, 1206625, 1235474, 1200827, 1566607)
**After:** 1215845us (median, all values: 1213134, 1207605, 1215430, 1216259, 1252496, 1259725, 1204889, 1234689, 1215177, 1560849)
**Improvement:** -0.62% (not significant)
**Mann-Whitney U:** 38/100 (not significant)
**Regression:** N/A

## Problem

HashMap::get_inner was 5.08% of runtime in the profile. Two CHR index structures used HashMap<FuncId, Vec<_>>:
1. `IndexedTriggers.by_functor` — maps functor ID to rule occurrences, looked up per constraint in the fixpoint loop.
2. `IndexData::ArgTopFunctor` — maps first-arg functor to candidate constraint IDs for join step candidate search.

The hypothesis was that replacing these with `Vec<Vec<_>>` indexed by FuncId (via lasso's Key trait) would provide O(1) array lookup (~5ns) vs HashMap's hash+probe (~30-50ns).

## Solution Attempted

Replaced both `HashMap<FuncId, Vec<_>>` occurrences with `Vec<Vec<_>>` using `FuncId.into_usize()` for indexing. The Vec is sized to accommodate the maximum FuncId seen during construction. Lookup uses direct array indexing with bounds checking (returns empty fallback for out-of-bounds).

## Why it failed

1. **The 5.08% HashMap::get_inner is not dominated by CHR index lookups.** The profile attributes ALL HashMap lookups to this single symbol, including term store hash-consing (intern_unlocked), dedup set lookups, and other data structures. The CHR index lookups are a small fraction of the total.

2. **Few distinct functors per predicate.** For the treecalc workload with `no_c/1`, there are only 5 functor patterns (l, b, f, c, a). A HashMap with 5 entries has excellent cache locality — the entire table fits in one cache line. The per-lookup savings of Vec vs HashMap are negligible for such small maps.

3. **The fixpoint loop overhead is dominated by other work.** Within normalize_owned (14.40% self-time), the index lookup is a small portion compared to VecDeque management, terms.with_term calls, match_head dispatch, and body execution.

4. **Slight improvement on secondary workload.** recursive_even_backward_first64 showed U=74/100 (borderline significant, 2.59%), suggesting the optimization might help workloads with more diverse predicate structures or higher CHR throughput.

## Files changed

- `src/chr/mod.rs` — Replaced HashMap with Vec in IndexedTriggers.by_functor and IndexData::ArgTopFunctor (reverted, DISCARD)

## Remaining opportunities

- The 5.08% HashMap overhead is primarily from term store hash-consing, not CHR indexes. Optimizing intern_unlocked's HashMap usage would have more impact.
- For workloads with many distinct predicates and complex join patterns, the dense index might help more. The treecalc workload with its single predicate is not a good target.
