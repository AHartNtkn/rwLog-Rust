# Investigation: Compose NF Success Path Optimization

## Summary

Investigated compose_nf success path optimization by fusing collect_tensor into factor_tensor_with_subst. DISCARD: U=34/100 (not significant), success path costs are evenly distributed.

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 406.1 us (median, all values: 393637, 390903, 391287, 402012, 406197, 406054, 408570, 409029, 411638, 409308)
**After:** 410.0 us (median, all values: 403005, 390449, 413998, 400664, 418882, 404493, 408860, 410292, 411181, 412072)
**U statistic:** 34/100 (not significant)

## Problem

After exhaustive precheck optimization (root functor, depth-2, multi-position, cached fields — all confirmed exhausted), the remaining runtime on treecalc_synth_flip is dominated by ~2,800 successful compose_nf calls (out of ~64K total after normalize cache). These successes pay the full cost: matching, substitution, factor_tensor_with_subst, constraint pipeline.

## Why It Didn't Work

The success path cost is evenly distributed across multiple operations:
1. **Matching** (match_term_lists_shifted)
2. **Constraint apply_subst** (twice — a-side and b-side)
3. **Constraint combine_owned**
4. **Constraint normalize_owned** (already cached — 79.2% hit rate)
5. **factor_tensor_with_subst** (already fused from prior investigation)
6. **NF construction with hashing**

No single component dominates enough for a targeted micro-optimization to produce measurable improvement. The attempted fusion (eliminating collect_tensor(b) by combining cached_rhs_map into shifted_vars) saved one tree traversal per success, but the savings per-call are too small relative to the other costs.

## Files Changed

None merged (DISCARD).

## Insights

- The compose_nf success path design space is exhausted for micro-optimizations. Costs are evenly spread.
- **The constraint pipeline (CHR) is the largest contributor** but is already cached at the normalize level.
- Further improvement on treecalc_synth_flip requires **reducing the number of successful composes** (algorithmic change — e.g., smarter search pruning, better constraint propagation) rather than making each one cheaper.
- The ~64K compose operations (after normalize cache) producing ~2,800 successes is the fundamental character of the workload. Reducing the 64K (pruning failures) is exhausted; reducing the 2,800 (pruning successes) requires domain-level reasoning about which composes are redundant.
