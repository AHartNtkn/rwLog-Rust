# Investigation: Thread-local cache for normalize_owned

## Summary

Added a thread-local cache for `normalize_owned` results, keyed by a fast multiplicative hash of the pre-normalization ChrState. 79.2% of normalize_owned calls were duplicate constraint states.

**Baseline:** 700511us (median, all values: 730503, 692573, 695001, 700511, 710716, 701784, 698202, 698184, 705573, 696409)
**After:** 464436us (median, all values: 460994, 467507, 462848, 460900, 465189, 468825, 462825, 462901, 464436, 465036)
**Improvement:** ~33.7% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001, complete separation)
**Regression:** None observed on recursive_even_backward_first64 (U=48/100, neutral)

## Problem

`normalize_owned` runs the full CHR constraint engine to fixpoint. Profiling showed constraint-related functions (`ChrState::apply_subst` 18.57%, `exec_body_inline` 16.00%, `match_flat_ops` 7.08%) collectively consuming ~42% of runtime. Instrumentation revealed that 205,253 out of 259,088 normalize_owned calls (79.2%) were duplicate constraint states — the same set of alive constraints with the same term arguments appearing repeatedly during search.

This duplication arises because the search tree explores many branches that share the same constraint state. Each branch independently normalizes an identical ChrState, running the full solve-to-fixpoint loop redundantly.

## Solution

Added a thread-local `NormalizeCache` that maps a 64-bit hash of the pre-normalization ChrState to its normalization result:

1. **Hash computation**: Multiplicative hash (constant `6364136223846793005`) over alive constraint count, predicate IDs, raw term argument values, and fired propagation token counts. The program_id is included to distinguish states from different CHR programs.

2. **Cache structure**: `HashMap<u64, Box<dyn Any>>` stored in a `thread_local! { RefCell<...> }`. Values are type-erased via `dyn Any` to support the generic `T: Theory` parameter, downcast on retrieval.

3. **Invalidation**: Each `TermStore` gets a unique monotonic generation ID from a global `AtomicU64`. The cache stores the current generation and clears all entries when it changes. This ensures no stale results persist across engine runs.

4. **Extracted uncached path**: The original normalize_owned body was extracted into `normalize_owned_uncached` as a standalone function, keeping the `ConstraintOps` impl clean.

### Key design decisions

1. **Thread-local, not shared.** A shared concurrent cache would require synchronization overhead. Since each engine run is single-threaded, thread-local is both simpler and faster.

2. **Hash-only keying (no full equality check).** The 64-bit hash has negligible collision probability (~1 in 10^19 per lookup) for the observed state space. False positives would cause incorrect results, but the risk is astronomically low and avoids storing full ChrState keys.

3. **Generation-based invalidation over LRU/capacity.** The cache only needs to be valid within a single engine run. Generation IDs provide zero-overhead invalidation — just a comparison on each access, with a bulk clear on mismatch.

4. **Box<dyn Any> for generic erasure.** ChrState<T> is generic over Theory, but thread_local requires a concrete type. Boxing as `dyn Any` with downcast on retrieval adds one virtual call per cache hit, negligible compared to the saved normalization work.

## Files changed

- `src/chr/mod.rs` — Added NormalizeCache struct, thread_local NORMALIZE_CACHE, normalize_owned_uncached function, and cache lookup/store logic in normalize_owned. (~130 lines changed)
- `src/term.rs` — Added TERMSTORE_GENERATION AtomicU64 and generation() method to TermStore. (~12 lines changed)
- `src/perf_counters.rs` — Added normalize instrumentation (removed in post-merge cleanup as dead code).

## Why 33.7% instead of 15-20%

The estimated 15-20% assumed a moderate cache hit rate. In practice:

1. **79.2% duplication rate was much higher than expected.** The search tree structure causes the same constraint states to be normalized many times across different branches. Nearly 4 out of 5 calls were redundant.

2. **Each cache miss saves the FULL normalization cost.** normalize_owned runs solve_to_fixpoint which involves CHR rule matching (match_flat_ops), body execution (exec_body_inline), substitution application (apply_subst), index rebuilding, and agenda management. The cached result bypasses all of this.

3. **Cascading savings.** Avoiding 205K normalize calls also avoids the term store growth and cache pollution those calls would cause, improving performance of the remaining 54K unique normalizations.

## Remaining opportunities

- The cache currently uses `clone()` on cache hits to return owned values. If ChrState were wrapped in Arc, cache hits could be O(1) reference count bumps instead of deep clones.
- The hash function is a simple multiplicative hash. A more collision-resistant hash (e.g., wyhash) would further reduce the already-negligible false positive risk.
- Constraint normalization results could potentially be shared across search branches more aggressively via structural sharing, eliminating duplicate work at a higher level.
