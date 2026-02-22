# Investigation: Cache collect_tensor Results for meet_nf

## Summary

Attempted to cache collect_tensor results per NF via OnceLock in NfInner, avoiding repeated apply_var_renaming tree walks. DISCARD: 1.9% regression on join_high_overlap (U=25/100). OnceLock atomic overhead exceeds savings; apply_var_renaming already has identity fast path.

**Primary workload (join_high_overlap_64x64, 200 iters):**
**Baseline:** 598 us (median, all values: 582, 603, 597, 597, 597, 628, 594, 600, 598, 599)
**After:** 609 us (median, all values: 586, 608, 611, 609, 609, 594, 610, 610, 614, 608)
**Improvement:** -1.9% (regression)
**Mann-Whitney U:** 25/100 (significant regression)

## Problem

meet_nf calls `collect_tensor(a, terms)` and `collect_tensor(b, terms)` on every meet attempt. The same NF may appear in many different meet pairs. collect_tensor involves `apply_var_renaming_list` which walks term trees. Caching the result per NF could eliminate redundant tree walks.

## Approach

Added `cached_direct_build: OnceLock<SmallVec<[TermId; 1]>>` to NfInner. Lazily populated on first collect_tensor call, reused on subsequent calls. Also updated `direct_rule_terms` to use the same cache.

## Why It Failed

1. **OnceLock atomic overhead**: Every cache access (even hits) requires atomic load with Acquire ordering. For a workload where each NF has collect_tensor called only a few times, the per-access overhead exceeds the savings.
2. **Identity fast path already exists**: apply_var_renaming already returns immediately when rhs_map is identity (common case), making the tree walk nearly free for many NFs.
3. **Low reuse rate**: Each NF typically participates in only a few meet attempts before being consumed or pruned, limiting cache hit rate.

## Files changed

- `src/nf.rs` — Added OnceLock cache field to NfInner, cache population in collect_tensor
- `src/join.rs` — Updated direct_rule_terms to use cache
- `src/engine.rs` — Minor adaptation

## Remaining opportunities

- This confirms the earlier cache_collect_tensor DISCARD finding (NF/Kernel backlog item 7, sub-investigation). The collect_tensor cost is genuinely low for typical NF sizes.
- If NF reuse becomes higher (e.g., through structural sharing or dedup), caching could become worthwhile, but with current architecture the reuse rate is too low.
