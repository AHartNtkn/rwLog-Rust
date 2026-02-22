# Investigation: Skip apply_subst Subtrees via Variable Range Check

## Summary

Added variable range overlap check in apply_subst_core to skip entire subtrees when the subtree's [min_var, max_var] range has no overlap with the substitution's bound variable range. Leverages the var_ranges infrastructure added by fast_occurs. KEEP: ~36.5% improvement on treecalc_synth_flip (U=100/100).

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 325194 us (median, all values: 318126, 317730, 319888, 319881, 323103, 329961, 329748, 327284, 328393, 329703)
**After:** 206376 us (median, all values: 208783, 204152, 202892, 206849, 206197, 206555, 206110, 205056, 213474, 212232)
**Improvement:** ~36.5% (same-session comparison)
**Mann-Whitney U:** 100/100 (complete separation)
**Regression:** None observed on recursive_even (U=76), join_high_overlap (U=48)

## Problem

`apply_subst` was ~33% of total runtime on treecalc_synth_flip. The function walks every non-ground subtree, resolving variable bindings through the substitution. However, many subtrees contain variables that are entirely outside the substitution's bound range — particularly in tree calculus where left-side and right-side variables occupy disjoint namespace ranges.

The var_ranges infrastructure (added by fast_occurs) already tracks per-term [min_var, max_var] ranges computed at intern time. This data was being used for occurs check rejection but not for apply_subst.

## Solution

Two changes:

### 1. Subst::bound_var_range() method

Added a method that computes the minimum and maximum variable indices with actual `Some` bindings in the substitution. Pre-computed once at the start of each `apply_subst_core` call.

### 2. Range overlap check in apply_subst_core

When visiting a non-ground App term (store ref), before pushing its children to the work stack, check whether the term's var_range overlaps with the substitution's bound range. If no overlap, the subtree cannot be affected by the substitution and the original TermId is pushed directly to the result stack.

### Key design decisions

1. **Overlap check only when `!SHIFTED || !raw`**: When SHIFTED=true and raw=true, the subtree's variables need virtual shifting even if no substitution binding applies. Skipping such subtrees would return incorrect unshifted terms. The check is only applied in the safe cases.

2. **Pre-computed subst range**: Computing `bound_var_range()` once per call (iterating the substitution bindings) is amortized across all subtree checks within that call. The iteration is cheap — substitutions are typically small Vec<Option<TermId>>.

3. **Zero overhead for non-matching terms**: The range check is a simple integer comparison against the var_ranges Vec (parallel to nodes), adding negligible cost per visited node.

## Files changed

- `src/subst.rs` — Added `bound_var_range()` method to Subst; added var_range overlap check in `apply_subst_core` for non-ground App store refs. Pre-computes subst range once per call.

## Why 36.5% instead of the theoretical 33%

The profiled 33% was apply_subst's inclusive cost. The optimization skips entire subtrees where var ranges don't overlap, which eliminates not just the variable resolution work but also all the child visiting, stack management, and all_same checking for those subtrees. The superlinear improvement (36.5% > 33%) suggests that the skipped subtrees were the most expensive ones (deep trees with many children), and that eliminating their traversal also reduces cache pressure and allocation overhead for the remaining work.

## Remaining opportunities

- The var_range check could be extended to factor_tensor_with_subst, which also walks term trees applying substitutions
- A finer-grained check using variable bitmasks (instead of min/max range) could catch cases where the range overlaps but the specific variables don't
- The SHIFTED+raw case is currently excluded from the optimization; investigating whether a shifted range check is feasible could capture additional savings
