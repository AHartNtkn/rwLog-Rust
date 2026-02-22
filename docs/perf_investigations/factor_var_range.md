# Investigation: Extend var_range Subtree Skipping to factor_tensor Traversals

## Summary

Extended the var_range overlap check (from subst_var_range) to the three tree-walking functions in factor_tensor_with_subst: renumber_vars_through_subst_list, collect_vars_through_subst_list, and apply_subst_and_renumber_list. DISCARD: no measurable improvement (U=40/100). The factor functions are on the compose success path (~1% of compose attempts), making per-call savings negligible.

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 209365 us (mean, all values: 208206, 210112, 211241, 213046, 213017, 211471, 207492, 203862, 207328, 207869)
**After:** 210637 us (mean, all values: 215697, 206693, 214513, 208417, 210302, 206837, 211159, 208315, 211960, 212480)
**Improvement:** -0.6% (noise)
**Mann-Whitney U:** 40/100 (not significant)

## Problem

The subst_var_range optimization (36.5% improvement) added var_range overlap checks to apply_subst_core in src/subst.rs. However, factor_tensor_with_subst in src/nf.rs uses its own custom tree-walking functions that bypass apply_subst_core. These functions (renumber_vars_through_subst_list, collect_vars_through_subst_list, apply_subst_and_renumber_list) could potentially benefit from the same var_range skip.

## Approach

Added combined_bound_var_range() helper for computing the union of two substitution ranges. In each of the three traversal functions, added var_range overlap check before pushing children: when the subtree's var range doesn't overlap the substitution range and the term isn't in the shifted namespace, skip substitution resolution and process variables directly.

## Why It Failed

The factor_tensor_with_subst functions are called only on the **compose success path** — roughly 1% of all compose attempts. While subst_var_range worked because apply_subst_core is called on the hot failure path (100% of compose attempts run apply_subst for constraints), the factor functions execute so infrequently that even significant per-call savings produce unmeasurable total improvement.

The key insight: **optimizations must target the hot path (failure path for compose), not the cold path (success path)**. The success path processes ~1% of attempts, so a 50% speedup there saves only ~0.5% total.

## Files changed

- `src/subst.rs` — Added combined_bound_var_range() helper
- `src/nf.rs` — Added var_range checks in renumber_vars_through_subst_list, collect_vars_through_subst_list, apply_subst_and_renumber_list

## Remaining opportunities

- The factor_tensor success path is now well-optimized and too infrequent to yield measurable gains from micro-optimizations
- Further compose improvements must target the failure path or reduce the total number of compose attempts
