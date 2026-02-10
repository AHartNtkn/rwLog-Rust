# Investigation: Arc-wrap PredStore in ChrStore

## Summary

Arc-wrapped `Vec<PredStore>` inside ChrStore to avoid deep-cloning PredStore HashMaps during ChrStateData::clone. No significant improvement.

**Baseline:** 1225812us (median, all values: 1172831, 1202206, 1175551, 1235724, 1229377, 1224250, 1227375, 1239769, 1232828, 1224150)
**After:** 1217963us (median, all values: 1179259, 1202961, 1199052, 1226256, 1220797, 1199746, 1219208, 1224709, 1216719, 1245190)
**Improvement:** 0.64% (not significant)
**Mann-Whitney U:** 62/100 (not significant)
**Regression:** N/A

## Problem

After compact_cinstance reduced CInstance size, ChrStateData::clone was 1.82% of runtime. The remaining clone cost includes deep-cloning `Vec<PredStore>`, where each PredStore contains `HashMap<FuncId, Vec<Cid>>` index data. The hypothesis was that Arc-wrapping would make the clone O(1) via refcount bump, with COW via Arc::make_mut in rebuild_indexes.

## Solution Attempted

Changed `preds: Vec<PredStore>` to `preds: Arc<Vec<PredStore>>` in ChrStore. Updated all mutation sites (add_chr, rebuild_indexes, index_from) to use `Arc::make_mut`. Converted `const_empty()` to `empty()` with `LazyLock` for the static EMPTY_STORE since `Arc::new()` is not const.

## Why it failed

1. **ChrStateData clones are rarely shared.** ChrStateData is typically owned (refcount=1) because `Arc::make_mut` in `data_mut()` already triggers clone-on-write at the outer level. The inner `Arc<Vec<PredStore>>` rarely has refcount > 1 at clone time, so the deep clone still happens via `Arc::make_mut` rather than being avoided via refcount bump.

2. **PredStore clone cost is small relative to total.** ChrStateData::clone was only 1.82% of runtime after compact_cinstance. The PredStore HashMap portion within that 1.82% is minor compared to other clone costs (inst Vec, all_args Vec, tokens). Even eliminating PredStore clone entirely would yield at most ~0.5-1% improvement.

3. **Arc overhead offsets savings.** Atomic refcount operations on every clone/drop add a constant cost that offsets whatever savings come from the occasional avoided deep clone.

## Files changed

- `src/chr/mod.rs` — Changed `preds: Vec<PredStore>` to `preds: Arc<Vec<PredStore>>` in ChrStore, updated mutation sites to use `Arc::make_mut`, converted `const_empty()` to `empty()` with `LazyLock` (reverted, DISCARD)

## Remaining opportunities

- ChrStateData::clone at 1.82% is approaching the noise floor for individual optimizations. Further clone reduction would require eliminating clones entirely (e.g., persistent/immutable data structures) rather than making individual fields cheaper to clone.
- The dominant runtime costs are now algorithmic: apply_subst (21.35%), normalize_owned (15.11%), match_head (11.39%), match_term_lists_shifted (8.28%). These represent core computation that can only be reduced by algorithmic changes (reducing call counts, better pruning, avoiding redundant work).
