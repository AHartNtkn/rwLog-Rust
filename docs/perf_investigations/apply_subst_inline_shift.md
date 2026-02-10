# Investigation: Inline shift_term into apply_subst traversals

## Summary

Attempted to eliminate separate shift_term tree walks by deferring variable shifting into apply_subst and factor_tensor_with_subst traversals via a ShiftMask bitmask.

**Baseline:** 741984us (median, all values: 745853, 728023, 742177, 745210, 737688, 743241, 735517, 744083, 736183, 741790)
**After:** 746085us (median, all values: 741825, 726554, 749850, 736582, 750850, 752599, 748592, 754534, 743578, 743116)
**Improvement:** -0.55% (slight regression)
**Mann-Whitney U:** 29/100 (not significant)
**Regression:** N/A (primary failed to show improvement)

## Problem

`shift_term` appeared at 13.35% of runtime in post-R37 profiling. It performs a full tree walk to shift all variable indices in a term by an offset, creating new shifted terms in the TermStore. This is called during matching when a left-side variable binds to a right-side compound term that needs its variables shifted into the left-side namespace.

## Solution

Introduced a `ShiftMask` bitmask tracking which substitution bindings contain unshifted right-side variables:

1. Modified `match_terms_combined_shifted` and `match_terms_combined_shifted_with_left_renaming` to skip `shift_term` calls and instead record which bindings need shifting in a ShiftMask.
2. Added `resolve_var_chain_with_shift_check` to check the ShiftMask during variable resolution.
3. Added `needs_shift` flag propagation through the factor_tensor_with_subst work stack.
4. Added `materialize_shift_mask` for constraint paths that cannot do on-the-fly shifting.

### Files changed

- `src/subst.rs` — Added ShiftMask type, resolve_var_chain_with_shift_check, materialize_shift_mask
- `src/matching.rs` — Modified shifted matching functions to return (Subst, ShiftMask), skip shift_term
- `src/kernel/util.rs` — Propagated ShiftMask through match_term_lists functions
- `src/kernel/compose.rs` — Handled (Subst, ShiftMask) from matching, materialize for constraints
- `src/nf.rs` — Added shift_mask to SubstParams, updated fused traversals for on-the-fly shifting

## Why -0.55% (regression) instead of 5-10% improvement

1. **Offset-aware matching already eliminated most shift_term calls.** The `match_terms_combined_shifted` fast path (from Round 6's optimization) handles the first match pair without any shift_term. For the treecalc_synth_flip workload, most compose attempts involve single-element pattern lists, so the fast path handles them entirely — shift_term is never called.

2. **Deferred shifting adds overhead that negates savings.** The ShiftMask tracking (bit operations on every binding), the needs_shift propagation through the work stack, and resolve_var_chain_with_shift_check (extra branch on every variable resolution) all add per-operation overhead. For the small terms in the remaining call sites, this overhead exceeds the cost of the original shift_term walk.

3. **Constraint paths still require materialization.** The generic apply_subst used by constraint handling cannot do on-the-fly shifting, so materialize_shift_mask must eagerly walk the substitution bindings. This re-does the work that shift_term would have done, limiting potential savings to only the factor_tensor_with_subst code path.

4. **The 13.35% profile attribution was misleading.** The profiling data was captured before the offset-aware matching optimization (Round 6) was implemented. After that optimization eliminated the dominant shift_term call site, the residual cost is minimal.

## Remaining opportunities

- shift_term is now a minor cost center. Further optimization of variable shifting is unlikely to yield measurable improvements on this workload.
- The profiling data should be refreshed after each major optimization to avoid chasing stale hotspots.
