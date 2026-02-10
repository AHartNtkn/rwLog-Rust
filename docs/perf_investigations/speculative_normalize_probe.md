# Investigation: Speculative Normalize Cache Probe

## Summary

Speculative computation of the normalize_owned commutative hash before the full constraint pipeline (to skip ChrStateData clone + combine on cache hit) showed a 3.8% regression on treecalc_synth_flip.

**Baseline:** 72932.141 us (median, all values: 73767.199, 72345.577, 72385.577, 73605.873, 71937.683, 75112.240, 72458.411, 73803.681, 71615.391, 71720.890)
**After:** 75680.623 us (median, all values: 75451.670, 83773.365, 74752.045, 75756.320, 76028.758, 74604.555, 76295.738, 75711.590, 75649.655, 78500.194)
**Improvement:** ~-3.8% (regression)
**Mann-Whitney U:** 2/100 (optimized is significantly slower)
**Regression:** Optimized is significantly slower than baseline

## Problem

The constraint pipeline in compose_nf (apply_subst + combine + normalize_owned) runs on every compose success (~640 calls). The normalize_owned cache has a 79.2% hit rate, but apply_subst (38.45% of runtime) and ChrStateData::clone (2.18%) run BEFORE the cache is checked. The hypothesis was that computing the normalize_owned hash speculatively — by walking constraint args and calling apply_subst per-arg WITHOUT cloning ChrStateData — would let us check the cache first and skip clone + combine on hit.

## Solution (attempted)

Added `speculative_normalize_check` method to the ConstraintOps trait (with default `None` return). ChrState implementation:

1. Walks a-side alive constraint instances, computes per-arg `apply_subst(arg, subst, terms)`, hashes (pred, substituted_args) using the same commutative formula as normalize_owned
2. Walks b-side alive instances with remap + apply_subst, same hashing
3. Computes combined hash including alive_count, token fired counts, program_id
4. Probes the NORMALIZE_CACHE thread-local with this hash
5. On hit: returns cached result directly, skipping the full pipeline
6. On miss: returns None, falling through to the existing pipeline

In compose_nf, the speculative probe is called before the existing constraint pipeline. On cache hit, the clone + combine + normalize steps are skipped entirely.

### Key design decisions

1. Reused the exact same hash formula as normalize_owned for cache compatibility.
2. Added ground-args short-circuit to skip the probe when `all_args_ground` is true.
3. The probe walks args without cloning ChrStateData — only reads, no writes.

## Files changed

- `src/constraint.rs` — Added `speculative_normalize_check` to ConstraintOps trait
- `src/chr/mod.rs` — Implemented `speculative_normalize_check` on ChrState<T>
- `src/kernel/compose.rs` — Inserted speculative probe before constraint pipeline

## Why regression instead of improvement

The critical insight is that **the speculative hash computation does the same per-arg apply_subst work as the full pipeline**. The normalize_owned hash formula uses fully-substituted TermIds, requiring `apply_subst(arg, subst, terms)` per arg — the exact same operation that dominates the full pipeline at 38.45% of runtime.

The savings on cache hit are only ChrStateData::clone (2.18%) and combine_owned (small). But the probe itself costs nearly as much as apply_subst_to_data because it walks the same args and calls the same apply_subst function.

On cache miss (~31%), the per-arg walk runs TWICE: once in the speculative probe (wasted), once in the full pipeline. This miss penalty outweighs the clone savings on hits.

The probe achieved ~69% hit rate (38K hits out of ~55K probes), but the per-hit savings (~7μs for clone avoidance) were far smaller than the per-miss penalty (~44μs for redundant arg walk).

## Remaining opportunities

- The normalize_owned cache is already highly effective at 79.2% hit rate. Further improvement would require either:
  - A hash formula that doesn't require per-arg apply_subst (e.g., based on pre-substitution state + substitution fingerprint). But pre_constraint_cache already tried this approach and found substitutions are unique per compose attempt.
  - Making apply_subst itself cheaper — but ground-bit skipping, all_same, and lock-free access are already implemented.
- The apply_subst at 38.45% appears to be irreducible computation: unique inputs requiring unique tree walks on every call.
- The constraint pipeline has been extensively optimized over 14+ sub-investigations. The remaining overhead is dominated by fundamental term substitution work.
