# Investigation: Incremental Constraint Hash Maintenance

## Summary

Maintaining a commutative hash of all alive constraint arguments incrementally (updated at every mutation site in ChrStore) to avoid recomputation in normalize_owned showed no statistically significant improvement on treecalc_synth_flip.

**Baseline (run 1):** 76395.307 us (median, all values: 81284.192, 74827.035, 76167.221, 76889.730, 74815.580, 79511.404, 76623.393, 75517.327, 75060.955, 76769.151)
**After (run 1):** 75434.725 us (median, all values: 80596.492, 71270.307, 79887.635, 74230.977, 76205.446, 79318.826, 72990.560, 74125.029, 75229.618, 75639.831)
**Improvement (run 1):** ~1.26%
**Mann-Whitney U (run 1):** 62/100 (not significant)

**Baseline (run 2):** 74337.330 us (median, all values: 75039.902, 74972.092, 74188.053, 71536.142, 74486.607, 80915.746, 73796.744, 73337.608, 73966.761, 76297.665)
**After (run 2):** 74738.055 us (median, all values: 71567.128, 73925.547, 71399.942, 75457.108, 78179.005, 74159.868, 74292.613, 75183.497, 76215.378, 75716.519)
**Improvement (run 2):** ~-0.54%
**Mann-Whitney U (run 2):** 46/100 (not significant)
**Regression:** None (indistinguishable from noise)

## Problem

The `normalize_owned` method in ChrState computes a commutative hash over all alive constraints by iterating `inst` and their args (~4.55% self-time in the profile). This hash is used to check a thread-local cache before running the CHR solver. The hypothesis was that maintaining this hash incrementally at mutation sites (`add_chr`, `mark_dead`, `apply_subst_to_data`, etc.) would eliminate the O(N) hash walk in normalize_owned.

## Solution (attempted)

Added a `constraints_hash: u64` field to `ChrStore` and a `single_constraint_hash(pred, args)` helper function. Updated all mutation sites:
- `add_chr`: wrapping_add the new constraint's hash
- `mark_dead`: wrapping_sub the dead constraint's hash
- `apply_subst_to_data`: full recompute after substitution (sub old hashes, apply subst, add new hashes)
- `combine_owned` / `combine`: wrapping_add the hashes from both stores
- `remap_vars` / `remap_and_apply_subst`: full recompute after variable remapping

In `normalize_owned`, replaced the hash computation loop with a direct read of `d.store.constraints_hash`.

### Key design decisions

1. Used the same hash formula (wrapping_mul + wrapping_add with constant 6364136223846793005) as the original normalize_owned loop for correctness.
2. Commutative combination via wrapping_add allows O(1) incremental updates for add_chr and mark_dead.
3. For apply_subst_to_data and remap operations, a full recompute is needed because all args change — no incremental shortcut possible.

## Files changed

- `src/chr/mod.rs` — Added `constraints_hash` field, `single_constraint_hash` helper, and incremental maintenance at all mutation sites

## Why no improvement

The critical insight is that `apply_subst_to_data` — the most frequent mutation path (called from every compose_nf constraint pipeline) — cannot be truly incremental. It must walk all alive constraints to substitute their args, and then must walk them again to recompute hashes. The "incremental" optimization just moves the hash computation from normalize_owned into `apply_subst_to_data`, with no net reduction in work.

The only mutation sites where incremental hashing saves work are `add_chr` and `mark_dead` (O(1) instead of O(N)). But these happen during CHR solving, which is already cached by the normalize_owned hash — and the hash computation in normalize_owned itself is a tiny fraction of the 4.55% self-time (most of that 4.55% is the actual CHR solving, not hash computation).

The potential savings from eliminating the hash loop is at most ~1-2% of total runtime — below the noise floor of measurement.

## Remaining opportunities

- The normalize_owned commutative hash cache (implemented in R41) already captures ~76% of the low-hanging fruit in CHR normalization
- Further CHR optimization would need to target the actual solving work, not the hash/cache infrastructure
- apply_subst at 36.32% remains the dominant hotspot — optimization there would have the highest ROI
