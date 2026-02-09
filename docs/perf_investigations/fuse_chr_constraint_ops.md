# Investigation: Fuse CHR constraint remap + apply_subst

## Summary

Fused `remap_constraint_vars` and `apply_subst` for the b-side CHR constraint in compose_nf into a single operation, eliminating one full ChrStateData clone. Also fixed the double-clone pattern in `apply_subst` and `remap_vars`. ~1.7% improvement on treecalc_synth_flip.

**Baseline:** 1508206us (median, all values: 1468501, 1528237, 1490268, 1492806, 1538339, 1506893, 1538137, 1481135, 1536826, 1509519)
**After:** 1483157us (median, all values: 1494174, 1483426, 1470533, 1457364, 1473238, 1482887, 1506426, 1480532, 1538050, 1489546)
**Improvement:** ~1.7% (same-session comparison)
**Mann-Whitney U:** 75/100 (p < 0.05)
**Regression:** None observed on recursive_even_backward_first64 (U=43/100, neutral)

## Problem

In `compose_nf_impl`, the b-side CHR constraint undergoes two separate operations:
1. `remap_constraint_vars` — shifts variable indices by `b_var_offset`
2. `apply_subst` — applies the right-side substitution

Each operation cloned the entire `ChrStateData` (Vec<CInstance>, Vec<PredStore> with HashMaps, TokenStore, VecDeque). Worse, the clone pattern in both `apply_subst` and `remap_vars` was `self.clone()` followed by `Arc::make_mut`, which *always* triggered a deep clone because `self` was still alive (refcount >= 2).

Profiling showed `ChrState::apply_subst` at 14.5% inclusive and `Arc::make_mut` at 3.83% self-time.

## Solution

Three changes:

1. **Fused `remap_and_apply_subst`**: Added to `ConstraintOps` trait with a default implementation. The ChrState override clones ChrStateData once and applies both remap and substitution in a single pass over constraint args.

2. **Fixed double-clone pattern**: Changed `apply_subst` and `remap_vars` to clone `data_ref.as_ref()` directly instead of `self.clone()` + `Arc::make_mut`, eliminating the guaranteed-unnecessary deep clone.

3. **Skip rebuild_indexes in fused path**: The fused operation skips `rebuild_indexes` because `normalize_owned` (called after `combine_owned`) will do this anyway.

### Key design decisions

1. Added `remap_and_apply_subst` as a trait method with default impl rather than only on ChrState, so the compose code can use it generically.
2. Extracted `build_remap_map` from `remap_constraint_vars` so compose.rs can check if remapping is needed and call the fused path only when a map exists.
3. The fused method processes each constraint arg in one pass: remap then subst per arg, rather than iterating all args twice.

## Files changed

- `src/constraint.rs` — Added `remap_and_apply_subst` to `ConstraintOps` trait with default implementation.
- `src/chr/mod.rs` — Fixed `apply_subst` and `remap_vars` to clone data directly (not self.clone() + Arc::make_mut). Added fused `remap_and_apply_subst` override.
- `src/kernel/compose.rs` — Uses `build_remap_map` + `remap_and_apply_subst` for b-side constraint.
- `src/kernel/util.rs` — Extracted `build_remap_map` from `remap_constraint_vars`.

## Why 1.7% instead of 4-8%

1. **Only b-side benefits from fusion**: The a-side constraint only needs `apply_subst` (no remap), so it doesn't benefit from the fused operation.
2. **Clone cost is only part of apply_subst**: The 14.5% inclusive time for apply_subst includes the actual substitution tree walks, not just cloning. The clone overhead was maybe 3-4% of that.
3. **Not all compose successes have large ChrStateData**: Many successful composes have small or empty constraint stores, where cloning is cheap regardless.

## Remaining opportunities

- Track which constraint args actually changed in `apply_subst_to_data` and only re-enqueue those constraints (instead of watermark=0 re-enqueueing all). This would reduce the O(N) pass in normalize_owned.
- The a-side `apply_subst` still uses the old pattern of cloning then mutating. Could be optimized to clone data directly when the caller doesn't need the original.
- `combine_owned` still clones when merging two ChrStates; could potentially take ownership of one side.
