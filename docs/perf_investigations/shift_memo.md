# Investigation: Thread-local memoization cache for shift_term

## Summary

Added a thread-local memoization cache for `shift_term` results, keyed by packed (TermId, offset) u64 keys. The same compound terms get shifted by the same offset repeatedly across compose attempts.

**Baseline:** 472037us (median, all values from worker report: ~472ms range)
**After:** 304508us (median, all values from worker report: ~305ms range)
**Improvement:** ~35.5% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001, complete separation)
**Regression:** None observed on recursive_even_backward_first64 (U=53/100, neutral)

## Problem

`shift_term` was 19.74% of runtime (plus 11.83% HashMap::get_inner from its interning = 31.57% total). shift_term walks a term tree, shifts all variable indices by an offset, and interns each shifted node in the TermStore HashMap. During compose_nf, matching calls shift_term when a left-side variable binds to a right-side compound term. The same compound terms get shifted by the same offset repeatedly across many compose attempts in the same engine run.

## Solution

Added a thread-local `ShiftCache` with a HashMap<u64, TermId> keyed by packed (TermId.raw() << 32 | offset) values:

1. **Cache structure**: `ShiftCache` struct with `generation: u64` for TermStore-based invalidation and `entries: HashMap<u64, TermId>` for the actual cache. Follows the same pattern as the NormalizeCache from R38.

2. **Skip trivial cases first**: Ground terms return immediately (unchanged). Inline variables are a simple array lookup (O(1)) — these don't need caching. The cache only kicks in for compound (store-referenced, non-ground) terms that require the full tree walk.

3. **Offset derivation**: The offset is derived from `shifted_vars[0].inline_var_index()` since `shifted_vars[0]` is always `Var(0 + offset)`.

4. **Selective storage**: Only stores cache entries when the result differs from the input term, avoiding wasted memory on terms unchanged by the shift.

5. **Generation invalidation**: Cache automatically cleared when a new TermStore is created (different generation).

### Key design decisions

1. **Thread-local, not TermStore-embedded.** Same rationale as NormalizeCache — each engine run is single-threaded, no synchronization needed.

2. **Packed u64 key.** TermId is 32 bits and offset fits in 32 bits, so we pack both into a single u64 for efficient hashing and comparison.

3. **Cache after inline var check.** Inline variables are O(1) shifted via array lookup — caching them would add overhead. Only compound terms benefit from caching.

4. **Only cache changed terms.** If shift_term returns the input unchanged (no variables in the subtree that need shifting), we don't store a cache entry. This keeps the cache focused on the expensive cases.

## Files changed

- `src/matching.rs` — Added ShiftCache struct, thread_local SHIFT_CACHE, cache lookup/store in shift_term, extracted shift_term_uncached for the inner tree walk. (~86 lines added)

## Why 35.5% instead of 15-25%

The estimated 15-25% assumed a moderate cache hit rate. In practice:

1. **Extremely high hit rate.** The treecalc_synth_flip workload has a small vocabulary of compound terms (tree calculus combinators). The same terms appear in many NF build/match patterns and get shifted by the same offsets across hundreds of thousands of compose attempts. The cache likely achieves >90% hit rate.

2. **Each cache hit saves a full tree walk + HashMap interning.** The uncached shift_term walks the entire term tree (potentially several levels deep) and interns each intermediate shifted node via HashMap insert. A cache hit replaces all of this with a single HashMap lookup.

3. **Cascading savings from reduced TermStore growth.** Fewer intern calls means the TermStore grows more slowly, improving cache locality for subsequent operations.

## Remaining opportunities

- The cache uses hashbrown HashMap. A direct-mapped array cache (indexed by TermId.raw() % N) could be even faster for the common case, at the cost of more collisions.
- apply_subst (28.17% pre-shift_memo) is now the dominant remaining cost. It walks constraint args through substitutions. Similar memoization may be possible for apply_subst, though the varying substitutions make keying harder.
