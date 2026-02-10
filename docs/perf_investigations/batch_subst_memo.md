# Investigation: Memoized batch apply_subst for ChrState constraint operations

## Summary

Attempted to add subtree-level memoization to `apply_subst` within ChrState operations, sharing a FxHashMap cache across all constraint arg apply_subst calls. Massive regression.

**Baseline:** 1233203us (median, all values: 1197475, 1252537, 1192262, 1210993, 1270090, 1245737, 1245406, 1233203, 1195538, 1210316)
**After:** 1449993us (median, all values: 1420584, 1447410, 1396203, 1455182, 1474475, 1449993, 1478936, 1436525, 1411424, 1459881)
**Improvement:** -17.6% (regression)
**Mann-Whitney U:** 0/100 (complete separation, optimized always slower)
**Regression:** N/A (primary showed clear regression)

## Problem

`apply_subst` is 20.25% of self-time in the profile. ChrState::apply_subst_to_data iterates all alive CHR constraints and calls `apply_subst` on each arg individually. Since terms are hash-consed, multiple constraint args may share subtrees (same TermId). The hypothesis was that sharing a memoization table across all constraint arg apply_subst calls within one ChrState::apply_subst_to_data invocation would eliminate redundant subtree traversals.

## Solution Attempted

Added `apply_subst_memo` and `apply_subst_core_memo` functions in `src/subst.rs` that accept a `&mut FxHashMap<TermId, TermId>` memo table. At each Visit step in the traversal, the memo is checked first; on cache hit, the cached result is used without traversal. After computing a result for any TermId, it's inserted into the memo. In `src/chr/mod.rs`, modified `apply_subst_to_data` and `remap_and_apply_subst` to create a shared memo HashMap and pass it to all per-arg apply_subst calls.

## Why it failed

1. **HashMap overhead dominates.** The FxHashMap per-node cost (hash computation, bucket probe, insertion) is applied to EVERY Visit step in the traversal. Even with FxHashMap's fast hashing, the overhead is ~20-50ns per operation, which is comparable to or exceeds the baseline work per node (read term store entry + branch).

2. **apply_subst is already highly optimized.** The existing `apply_subst_core` already has:
   - Ground term early-exit via `is_ground()` bit (O(1), no traversal)
   - `all_same` check that reuses the original TermId when no children changed (avoids hashcons lookup)
   - Lock-free node access via `RwLock::get_mut()`

   These mean the baseline is already ~35ns per node. Adding a HashMap check+insert at ~30ns per node nearly doubles the cost.

3. **Subtree sharing is limited for this workload.** In treecalc_synth_flip, constraint args have relatively unique structures. The terms may be small or the substitutions sparse enough that most terms are either ground (already O(1)) or have unique non-ground structure. Without significant sharing, the memo never amortizes its overhead.

4. **The fundamental problem: apply_subst is a hot, tight inner loop.** Any per-node overhead in the traversal is amplified across ~334K calls. The overhead must be less than the savings per cached subtree, and for small terms with limited sharing, this condition is never met.

## Files changed

- `src/subst.rs` — Added apply_subst_memo and apply_subst_core_memo with FxHashMap memoization (reverted, DISCARD)
- `src/chr/mod.rs` — Modified apply_subst_to_data and remap_and_apply_subst to use memoized version (reverted, DISCARD)

## Remaining opportunities

- The 20.25% apply_subst hotspot is resistant to per-node caching due to the already-optimized baseline. Future approaches should focus on REDUCING THE NUMBER OF CALLS rather than caching within calls.
- Track which variable indices appear in ChrState constraints (via bitset) and skip apply_subst entirely when the substitution's domain doesn't overlap.
- Lazy/deferred substitution: accumulate pending substitutions on ChrState and apply once at normalize_owned, reducing the number of full tree-walk passes.
- Consider a Vec-indexed memo (by TermId.index()) for lower per-lookup overhead, but the fundamental issue of limited subtree sharing likely remains.
