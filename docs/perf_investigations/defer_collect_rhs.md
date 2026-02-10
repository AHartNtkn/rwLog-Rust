# Investigation: Defer b-side collect_tensor in compose_nf

## Summary

Attempted to defer `collect_tensor(b)` until after matching succeeds in compose_nf, since 99.14% of compose attempts fail at matching. No statistically significant improvement.

**Baseline:** 1400195us (median, all values: 1401385, 1396075, 1426903, 1398000, 1388072, 1391071, 1405037, 1428009, 1412400, 1399006)
**After:** 1388899us (median, all values: 1402356, 1405873, 1375596, 1387696, 1390101, 1384927, 1378260, 1407228, 1379746, 1402593)
**Improvement:** ~0.8% first batch (not reproducible)
**Mann-Whitney U:** 73/100 first batch, 60/100 second batch (not significant)
**Regression:** N/A

## Problem

In `compose_nf_impl`, both `collect_tensor(a)` and `collect_tensor(b)` are called before matching (lines 75-76). `collect_tensor` converts an NF to direct-rule form by building a `rhs_map` from DropFresh and calling `apply_var_renaming_list` on build_pats. Since 99.14% of compose attempts fail at matching, b's collect_tensor work is wasted. `apply_var_renaming_list` was 2.67% of runtime in profiles.

## Solution Attempted

Two approaches were tried:

### Approach A: Simple deferral

Defer `collect_tensor(b)` to the success path. Use `&b.match_pats` directly for matching (since `rw2.lhs` = `b.match_pats.clone()` anyway). Added `collect_tensor_rhs()` helper that only computes the rewritten build_pats without cloning match_pats.

### Approach B: Fused DropFresh + substitution (abandoned)

Enhanced `SubstParams` to fold the DropFresh variable renaming into `factor_tensor_with_subst`. This was WORSE than baseline (U=39/100, -0.73%) because always setting `shifted=true` for RHS variables added overhead that negated the savings.

## Files changed

- `src/kernel/compose.rs` — Deferred `collect_tensor(b)` to success path; used `collect_tensor_rhs(a)` instead of full `collect_tensor(a)`.
- `src/nf.rs` — Added `compute_rhs_var_map()` and `collect_tensor_rhs()` helpers.

## Why it failed

1. **Root functor precheck already filters**: The precheck at lines 59-73 catches most obviously-incompatible pairs BEFORE collect_tensor is called. The "99.14% failure rate" at matching is misleading — many failures occur at the precheck, not at matching.

2. **collect_tensor is lightweight**: For typical NFs with 1-2 build patterns and small terms, building the rhs_map Vec and running apply_var_renaming_list takes microseconds. Saving a few microseconds per call on already-filtered paths doesn't accumulate to a measurable improvement over 1.4 seconds total runtime.

3. **SmallVec clone is cheap**: `nf.match_pats.clone()` copies inline SmallVec data (1-2 TermIds), not a heap allocation.

4. **Profile may have shifted**: After Round 22's massive 27.8% improvement (fused_factor_compose), the relative weight of apply_var_renaming_list may be different from what the pre-Round-22 profile showed.

## Remaining opportunities

- The fused approach (B) failed because of overhead from shifted=true semantics. A more targeted fusion that adds DropFresh renaming as a separate pre-lookup step (not through shifted_vars) might work better, but the marginal benefit is likely <1%.
- collect_tensor's work could be cached in NF (Arc-wrapped), but this was previously investigated (Round 21: cache_collect_tensor, DISCARD).
