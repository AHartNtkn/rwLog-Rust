# Investigation: Incremental CHR Normalization

## Summary

Added a fixpoint watermark to ChrStateData to skip re-processing stable constraints during normalize_owned. ~1.4% improvement on treecalc_synth_flip.

**Baseline:** 2390191us (median, all values: 2405301, 2425427, 2432504, 2381002, 2389922, 2363939, 2384020, 2405920, 2365757, 2390460)
**After:** 2355792us (median, all values: 2356361, 2347027, 2380272, 2352902, 2353188, 2365660, 2371012, 2374604, 2355222, 2348983)
**Improvement:** ~1.4% (same-session comparison)
**Mann-Whitney U:** 93/100 (p < 0.001)
**Regression:** None observed on recursive_even_backward_first64 (U=40/100, neutral)

## Problem

In `src/chr/mod.rs`, `normalize_owned()` called `enqueue_all_alive_in()` which put ALL alive constraints on the processing agenda, even ones already at fixpoint from a previous normalization. Then `solve_to_fixpoint()` processed every constraint, trying each against applicable CHR rules. Additionally, `rebuild_indexes()` rebuilt all indexes from scratch every time. For synth_flip with the `no_c` constraint theory, stable old constraints were being redundantly processed.

The CHR pipeline consumed ~33% of synth_flip runtime: match_head (17.2%), normalize_owned (10.1%), collect_args (3.4%), rebuild_indexes (1.1%), search_steps_inner (1.5%).

Also, `rebuild_indexes` was called redundantly — once in `normalize_owned` and again in `solve_to_fixpoint`.

## Solution

Added a `fixpoint_watermark: u32` field to `ChrStateData` that tracks up to which Cid constraints are at fixpoint. Constraints with `cid.0 < fixpoint_watermark` are skipped during agenda construction and indexing.

### Key design decisions

1. **Watermark-based tracking**: A simple monotonic counter avoids per-constraint flags. After successful normalization, the watermark advances to `next_cid`. When constraint args change (via substitution), the watermark resets to 0.

2. **Incremental indexing via `index_from`**: When watermark > 0, only constraints above the watermark are indexed (via `ChrStore::index_from`), avoiding a full `rebuild_indexes` call. Existing indexes for old constraints remain valid.

3. **Change-tracking in `apply_subst_to_data`**: Returns `bool` indicating whether any constraint arg actually changed. For the `no_c` theory, constraint args are ground terms (e.g., `f(b(l))`, `c(z)`), and `apply_subst` returns the same TermId for ground terms. This preserves the watermark through the compose pipeline when constraints have ground args.

4. **Change-tracking in `remap_vars`**: Same approach — only resets watermark and rebuilds indexes when args actually change. Skips both rebuild_indexes and watermark reset when all args are ground and unchanged.

5. **Removed redundant `rebuild_indexes`**: The call in `solve_to_fixpoint` (line 1405) was redundant since `normalize_owned` already rebuilds before enqueuing. Removed.

6. **Thawed state at fixpoint**: `thaw_chr` sets `fixpoint_watermark = next_cid` since the frozen state was at fixpoint.

## Files changed

- `src/chr/mod.rs` — Added `fixpoint_watermark` field to `ChrStateData`, `index_from()` for incremental indexing, `enqueue_above_watermark()` for incremental enqueuing, change-tracking in `apply_subst_to_data` and `remap_vars`, watermark management in `normalize_owned`.

## Why 1.4% instead of 15-25%

The initial hypothesis overestimated the savings because:

1. **Many normalize calls involve fresh constraints** (watermark=0). After `combine_owned`, if the combined store was built from scratch or substitution changed args, a full rebuild is required.

2. **The naive implementation showed zero improvement** (U=42). The key obstacle: `apply_subst` and `remap_vars` were unconditionally resetting the watermark to 0 even when constraint args were ground and unchanged. The fix was tracking whether args actually changed.

3. **`solve_to_fixpoint` was already somewhat efficient**: Dead constraints are skipped via `is_alive_in()` check. The savings come from skipping agenda iteration and `rebuild_indexes` for already-stable constraints, which are a modest fraction of total CHR overhead.

4. **The CHR rules in treecalc are all single-headed simplification rules**, so the fixpoint loop for unchanged constraints was already cheap (each constraint quickly finds it has no applicable rule and moves on).

## Remaining opportunities

- Further CHR optimization: compiled decision trees for multi-argument indexing (match_head is still 17% of synth_flip)
- Caching normalized constraint states by input hash to avoid repeated full normalization
- Reducing apply_subst overhead (19.6% of synth_flip) via specialization for common term patterns
