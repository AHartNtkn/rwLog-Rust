# Investigation: Fuse ChrState apply_subst + combine_owned into single operation

## Summary

Attempted to fuse ChrState::apply_subst + ChrState::remap_and_apply_subst + combine_owned into a single `combine_with_substs` operation, eliminating one ChrStateData clone. Slight regression.

**Baseline:** 1221257us (median, all values: 1210543, 1279765, 1257876, 1218400, 1224113, 1195833, 1230331, 1231000, 1199609, 1204589)
**After:** 1238014us (median, all values: 1246149, 1283051, 1240682, 1224416, 1253006, 1232720, 1238937, 1234839, 1237091, 1217379)
**Improvement:** -1.37% (regression)
**Mann-Whitney U:** 24/100 (not significant, trending worse)
**Regression:** N/A

## Problem

In compose_nf, when composition succeeds, the constraint goes through three separate operations: (1) clone a's ChrStateData + apply subst_left, (2) clone b's ChrStateData + apply remap+subst_right, (3) combine_owned merges b into a. The hypothesis was that fusing these into a single operation would save one ChrStateData clone (3.41% of profile) and improve cache locality.

## Solution Attempted

Added `combine_with_substs` to the ConstraintOps trait with a default implementation delegating to the three separate operations. Overrode in ChrState to: (1) clone a's ChrStateData once, (2) apply subst_left to a's constraints in-place, (3) copy b's alive constraints directly into the combined store, applying remap+subst_right to each arg as it's copied. This eliminates creating an intermediate ChrState for b.

## Why it failed

1. **Arc's copy-on-write already makes the "extra" clone free.** The existing code creates ChrStates with refcount=1 (since apply_subst creates a new Arc). When combine_owned calls Arc::make_mut on the a-side ChrState, it's a no-op because refcount=1. The "redundant clone" the fused version eliminates was already zero-cost.

2. **The fused version adds per-constraint branching overhead.** The inline remap+subst application for b's constraints requires branching on `Option<&[Option<u32>]>` for the remap step per constraint, adding code complexity in a hot loop.

3. **The real cost is apply_subst tree walks, not cloning.** ChrStateData::clone at 3.41% includes the Vec/HashMap copies, but the dominant 20.25% is in the tree-walking apply_subst calls. Fusing the combine step doesn't reduce the tree-walking cost.

## Files changed

- `src/constraint.rs` — Added combine_with_substs to ConstraintOps trait (reverted, DISCARD)
- `src/chr/mod.rs` — Added ChrState::combine_with_substs override (reverted, DISCARD)
- `src/kernel/compose.rs` — Updated compose_nf to use fused method (reverted, DISCARD)

## Remaining opportunities

- The ChrStateData cloning overhead (3.41%) is already minimized by Arc's COW semantics. Further clone elimination would require changing compose_nf to take ownership of NFs (architectural change).
- The dominant cost remains apply_subst tree walks (20.25%). Approaches that REDUCE the number of tree walks (lazy substitution, variable domain filtering) would be more impactful than reorganizing the combine pipeline.
