# Investigation: Specialize compose_nf for arity-1 NFs

## Summary

Attempted to add a specialized fast path in `compose_nf` for arity-1 NFs (one match pattern, one build pattern), which dominate treecalc_synth_flip. No significant improvement.

**Baseline:** 1297888us (median, all values: 1297695, 1319302, 1293577, 1298080, 1291720, 1320235, 1298102, 1294501, 1319671, 1291619)
**After:** 1294472us (median, all values: 1304830, 1308083, 1281587, 1284113, 1279875, 1278942, 1307732, 1313868, 1308786, 1283436)
**Improvement:** 0.26% (not significant)
**Mann-Whitney U:** 65/100 (not significant)
**Regression:** N/A

## Problem

On treecalc_synth_flip, most NFs are arity-1. The general compose_nf path handles arbitrary arities via Vec/SmallVec collections, loops over pattern lists, and general-purpose `match_term_lists_shifted`. The hypothesis was that a specialized path avoiding these overheads could reduce per-compose cost across ~324K compose attempts.

## Solution Attempted

Added `compose_nf_unary` fast path that:
1. Calls matching functions directly instead of through `match_term_lists_shifted`
2. Uses `collect_tensor_build_unary` with SmallVec instead of Vec for rhs_map
3. Defers b-side collect_tensor until after matching succeeds (avoids work for 99%+ failing path)

## Why it failed

1. **The overhead eliminated was too small to matter.** compose_nf spends ~6% of total time, but the allocation overhead (Vec for rhs_map, SmallVec clone) is a tiny fraction. The dominant cost is tree-walking matching, which the specialization doesn't change.

2. **Root functor precheck is already very effective.** ~99% of compose attempts are filtered before reaching collect_tensor or match_term_lists_shifted.

3. **match_term_lists_shifted already has a fast path for single elements.** When length is 1, the existing code calls `match_terms_combined_shifted` directly on the first iteration (subst starts empty), so loop overhead is negligible.

4. **SmallVec vs Vec for rhs_map saved a heap allocation per compose, but modern allocators handle small allocations very cheaply.** The Vec was typically only 2-8 elements (~16-64 bytes), well within mimalloc's fast path.

5. **Deferring b's collect_tensor saves ~800 calls** (successful composes), but at microsecond-level cost per call, this amounts to ~1ms total.

## Files changed

- `src/kernel/compose.rs` — Added `compose_nf_unary` fast path (reverted, DISCARD)
- `src/nf.rs` — Added `collect_tensor_build_unary` with SmallVec, converted `collect_tensor` to use SmallVec (reverted, DISCARD)

## Remaining opportunities

- The compose matching traversal itself dominates compose cost — optimizing the tree walk would be more impactful than reducing surrounding overhead.
- Batch-rejecting multiple compose candidates without per-term matching (e.g., bloom filter on term structure, NF shape signatures).
- The compose precheck + unary specialization design spaces appear exhausted for micro-optimizations. Remaining compose improvements need to be algorithmic (fewer compose attempts, smarter scheduling).
