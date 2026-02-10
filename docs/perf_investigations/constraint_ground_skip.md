# Investigation: Skip constraint operations when all args are ground

## Summary

Added `all_args_ground` flag to ChrStateData. When all alive constraint args have the ground bit set and builtins are empty, `apply_subst`, `remap_vars`, and `remap_and_apply_subst` skip the expensive ChrStateData clone + arg walk and return a cheap Arc refcount bump.

**Baseline:** 824267us (median, all values: 823804, 824501, 825321, 823781, 827033, 825016, 823036, 825726, 824033, 823588)
**After:** 815149us (median, all values: 813485, 813356, 813918, 815972, 814567, 817457, 810606, 815747, 815729, 816018)
**Improvement:** ~1.1% (same-session comparison)
**Mann-Whitney U:** 100/100 (complete separation, p < 0.0001)
**Regression:** None observed on recursive_even_backward_first64 (U=92/100, 5.47% improvement)

## Problem

In compose_nf, ChrState::apply_subst (15.77% of profile) clones ChrStateData and walks all alive constraint args to apply a substitution. ChrStateData::clone adds another 1.95%. After CHR normalization resolves variables, constraint args become progressively grounded. Once all args are ground, subsequent apply_subst calls are pure waste — they clone, walk, find nothing changed, and wrap in a new Arc.

## Solution

Added `all_args_ground: bool` field to ChrStateData that caches whether every alive constraint arg has `is_ground()` set. The flag is:
- Initialized to `true` on empty store construction (no args = vacuously ground)
- Updated incrementally in `introduce` (set false if new args are non-ground)
- Updated in `combine_owned` (set false if merged side is non-ground)
- Recomputed fully at the end of `normalize_owned` (where constraints settle to fixpoint)

When `all_args_ground` is true AND `T::is_empty(&builtins)` (always true for NoTheory), three methods return early:
- `apply_subst` — skips ChrStateData clone + apply_subst_to_data walk
- `remap_vars` — skips ChrStateData clone + variable renaming walk
- `remap_and_apply_subst` — skips ChrStateData clone + fused remap+subst walk

### Key design decisions

1. **Conservative flag semantics:** If in doubt, the flag is set to `false` (safe, just misses optimization). The recompute in `normalize_owned` ensures it catches up.

2. **Builtins check via `T::is_empty`:** The fast path also requires builtins to be empty/trivial, since `T::apply_subst` on builtins could have side effects even when args are ground. For NoTheory (the treecalc case), builtins are always empty.

3. **Recompute at normalize_owned:** This is the canonical "constraint settling" point where all CHR rules have fired to fixpoint. After this, the flag accurately reflects the ground state of all args.

## Files changed

- `src/chr/mod.rs` — Added `all_args_ground` field to ChrStateData, `recompute_all_args_ground` method, incremental flag maintenance in introduce/combine_owned, full recompute in normalize_owned, and fast-path checks in apply_subst/remap_vars/remap_and_apply_subst. (46 insertions)

## Why 1.1% instead of 4-8%

The estimated 4-8% assumed >50% of compose successes would hit the all-ground fast path. The actual fraction is lower — many constraints still have non-ground args at the point where compose_nf applies substitutions. The 1.1% represents the subset where args ARE ground after prior normalizations. The 5.47% improvement on recursive_even_backward (non-CHR workload) shows the fast path is more impactful when constraints are trivially empty.

## Remaining opportunities

- The 15.77% ChrState::apply_subst cost is only partially addressed. The remaining cost comes from constraints with non-ground args that genuinely need substitution applied.
- A variable bitset on ChrStateData could enable a more precise check: skip apply_subst when the substitution's domain doesn't intersect with the constraint's variable set (even if args aren't fully ground).
- The 14.18% split_match_subst cost in compose_nf is unaffected by this change — it's genuine computation on the matching result.
