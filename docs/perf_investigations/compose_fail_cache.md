# Investigation: Cache compose_nf failure results

## Summary

Attempted to cache compose_nf failure results using FxHashSet<(u64, u64)> keyed by NF hashes. Regression on primary workload due to 0% cache hit rate.

**Baseline:** 1189473us (median, all values: 1189074, 1185199, 1200463, 1211203, 1176513, 1181435, 1208191, 1199352, 1186057, 1189872)
**After:** 1203811us (median, all values: 1184531, 1200400, 1199469, 1219043, 1182218, 1190297, 1230723, 1209854, 1216267, 1207223)
**Improvement:** -1.21% (regression)
**Mann-Whitney U:** 29/100 (not significant, trending worse)
**Regression:** N/A

## Problem

compose_nf has 324K attempts with only 2787 successes (99.14% failure rate). Prior investigation (compose_meet_memoization) found 21% of compose calls are duplicates from tabling fixpoint verification. The hypothesis was that caching failed (a, b) NF pairs would avoid recomputing ~68K duplicate failures.

## Solution Attempted

Added a thread-local `FxHashSet<(u64, u64)>` failure cache in compose_nf. Before attempting match_term_lists_shifted, check if `(a.cached_hash, b.cached_hash)` is in the cache. On failure, insert the pair. The cache is cleared at engine initialization.

## Why it failed

1. **The 21% duplication rate is workload-specific, not universal.** The prior investigation measured across ALL corpus cases. The 21% aggregate was driven by `recursive_add_*` cases (50% duplication each). The treecalc cases showed 0% duplication — `treecalc_first_answer` had 5 composes / 5 unique, `treecalc_first16` had 81 composes / 81 unique. Since `treecalc_synth_flip` is a treecalc workload, it has essentially zero duplicate compose pairs, making every cache lookup a miss.

2. **The existing root functor precheck already eliminates most failures cheaply.** Lines 59-73 of compose.rs short-circuit composition when the first build pattern of `a` and first match pattern of `b` have different root functors. This O(1) check makes most failures very cheap (~10ns). A cache that prevents cheap failures provides no benefit.

3. **Thread-local HashSet overhead is significant at scale.** With 324K compose calls and 0% cache hits, the cost is 324K hash computations + 324K HashSet lookups + 324K insertions. FxHashSet operations are fast individually but sum to ~1.2% regression at this call volume.

4. **No workload benefits.** The `recursive_add_*` cases have 50% duplication but are fast enough that absolute savings would be tiny. There is no workload in the corpus where both high duplication rate AND expensive failing composes are present at scale.

## Files changed

- `src/kernel/compose.rs` — Added thread-local FxHashSet<(u64, u64)> failure cache with lookup before compose and insertion on failure (reverted, DISCARD)
- `src/engine.rs` — Added clear_compose_fail_cache() call in Engine::new_with_env (reverted, DISCARD)

## Remaining opportunities

- The compose failure path is already extremely cheap due to the root functor precheck. Further optimization of compose failures is unlikely to yield measurable improvement on treecalc workloads.
- For workloads with high compose duplication (recursive_add_*), caching could help but those workloads are already fast (<100ms). The optimization would need to target a workload where duplication is both high and the failures are expensive.
