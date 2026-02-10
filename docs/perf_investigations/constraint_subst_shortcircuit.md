# Investigation: Skip ChrState::apply_subst when substitution doesn't affect constraint variables

## Summary

Attempted to skip the expensive ChrStateData clone + arg walk in ChrState::apply_subst when the substitution doesn't bind any variables present in constraint args.

**Baseline:** 466967us (median, all values: 473617, 464776, 466085, 473559, 468309, 466074, 467848, 482605, 462005, 464603)
**After:** 467505us (median, all values: 462218, 465173, 485130, 467419, 481011, 467590, 461830, 478975, 463118, 469973)
**Improvement:** -0.12% (no change)
**Mann-Whitney U:** 50/100 (not significant — pure noise)
**Regression:** N/A (primary failed to show improvement)

## Problem

`apply_subst` (the term-level function) is 28.17% of runtime, called from `ChrState::apply_subst` in the compose_nf constraint pipeline. Every successful compose matching triggers constraint apply_subst which clones ChrStateData and walks all alive constraint args through the substitution. The existing `constraint_ground_skip` optimization skips when all args are ground, but for non-ground constraints the walk always happens.

## Solution

Added a pre-check in ChrState::apply_subst before the clone+walk:

1. **Subst::bound_var_mask() -> u64**: Bloom-filter bitmask where bit `(i % 64)` is set for each bound variable index.
2. **Pre-check scan**: Before cloning ChrStateData, scan alive constraint args:
   - Ground args: skip
   - Inline variables: accumulate into `constraint_var_mask`
   - Non-ground compound terms: conservatively set `has_compound_nonground = true`
3. If no compound non-ground args and `(constraint_var_mask & subst.bound_var_mask()) == 0`: skip operation entirely.

## Files changed

- `src/subst.rs` — Added `bound_var_mask()` method to Subst
- `src/chr/mod.rs` — Added pre-check scan in ChrState::apply_subst

## Why 0% instead of 5-15% improvement

1. **Compound non-ground args are common.** Many constraint args are compound terms containing variables deep in the tree. The optimization can't cheaply determine which variables are inside without walking the tree (which is the expensive operation we're trying to skip), so it conservatively falls through to the full path.

2. **Variable overlap is frequent.** Even when all args are inline variables, they often DO overlap with the substitution's bound variables. Constraint variables typically reference the same NF variables being composed. The disjoint case is rare.

3. **Scan overhead offsets savings.** The pre-check scan iterates all alive instances and their args, partially offsetting any savings from the occasional skip.

## Remaining opportunities

- Caching a `non_ground_var_mask` on ChrStateData incrementally (updated at constraint add/remove) could avoid the scan overhead, but handling compound terms would require collecting variable indices at insertion time.
- The `all_args_ground` optimization already captures the highest-value case. The marginal value of "non-ground but disjoint variables" is small.
- The 28.17% apply_subst cost may be better attacked via memoization at a higher level (caching ChrState::apply_subst results) or by reducing the number of constraint pipeline invocations.
