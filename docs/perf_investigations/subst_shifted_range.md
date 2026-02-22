# Investigation: Extend var_range Skip to SHIFTED+raw Case in apply_subst_core

## Summary

Extended the var_range subtree skip in apply_subst_core to handle the SHIFTED+raw case by redirecting non-overlapping subtrees to shift_term instead of full substitution walk. DISCARD: no measurable improvement (U≈50/100, neutral).

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 208185 us (median, all values: 207358, 207420, 208128, 207512, 203282, 211130, 209372, 210635, 214554, 208243)
**After:** 209582 us (median, all values: 206713, 208362, 207124, 211895, 209983, 210345, 209180, 211508, 208833, 211005)
**Improvement:** ~0% (neutral)
**Mann-Whitney U:** ~44/100 (not significant)

## Problem

The subst_var_range optimization (36.5% improvement) added var_range overlap checks to skip subtrees in apply_subst_core where the subtree's variable range doesn't overlap the substitution's bound range. However, this skip was disabled for the `SHIFTED=true && raw=true` case because shifted variables need virtual shifting even when no substitution binding applies — simply pushing the unchanged TermId would return unshifted terms, which is incorrect.

## Solution Attempted

For the SHIFTED+raw case where the subtree's var_range doesn't overlap the substitution range:
1. Compute the shifted var_range by looking up `shifted_vars[t_min]` and `shifted_vars[t_max]`
2. If the shifted range also doesn't overlap, call `shift_term(tid, shifted_vars, terms)` directly instead of walking the full substitution pipeline
3. shift_term has its own cache and is simpler than full apply_subst_core

Changes in:
- `src/subst.rs` — Added SHIFTED+raw var_range check with shift_term fallback
- `src/matching.rs` — Made shift_term accessible for the subst module

## Why It Failed

1. **The SHIFTED+raw code path is already fast**: The subst_var_range optimization already catches the easy cases (non-SHIFTED or non-raw). The remaining SHIFTED+raw calls are precisely the ones where variable ranges DO overlap with the substitution range, so the new skip rarely triggers.

2. **shift_term is not cheaper than the existing code**: When variables do need shifting, the current apply_subst_core SHIFTED path already handles this efficiently through its main loop. Redirecting to shift_term adds a function call and its own cache lookup overhead without saving work.

3. **The check itself adds overhead**: Computing `shifted_vars[t_min]` and `shifted_vars[t_max]` and then checking range overlap adds work to every SHIFTED+raw call, even when the skip doesn't trigger. This overhead approximately cancels any savings from the few cases where it does skip.

4. **Very few SHIFTED+raw calls with non-overlapping ranges**: In practice, the SHIFTED+raw case is used during compose_nf matching where the shifted variables ARE in the substitution's range — that's why matching is being performed. The non-overlapping case is rare.

## Files changed

- `src/subst.rs` — Extended var_range skip for SHIFTED+raw case
- `src/matching.rs` — Exposed shift_term for use from subst module

## Remaining opportunities

- The apply_subst_core SHIFTED+raw path is effectively optimized — var_range skip covers the easy cases, and the remaining cases genuinely need full substitution walks
- Further optimization of apply_subst would need to target the substitution application itself (e.g., batched or lazy substitution) rather than additional skip conditions
- The subst_var_range optimization already captured the vast majority of available savings in this area
