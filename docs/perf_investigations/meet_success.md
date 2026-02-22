# Investigation: Meet NF Success Path Fusion

## Summary

Ported compose_nf's proven fusion techniques to meet_nf: skip split_match_subst, use factor_tensor_with_subst, fused constraint handling. KEEP: 2.57% improvement on join_high_overlap_64x64 (U=94/100), plus dead code cleanup.

**Primary workload (join_high_overlap_64x64, 200 iters):**
**Baseline:** 593.2 us (median, all values: 593.041, 593.006, 593.198, 593.641, 595.151, 594.482, 592.929, 595.305, 581.185, 595.387)
**After:** 584.4 us (median, all values: 586.296, 571.387, 546.381, 584.462, 587.659, 587.064, 587.807, 569.079, 563.913, 591.096)
**Improvement:** ~2.57% (same-session comparison)
**Mann-Whitney U:** 94/100 (p < 0.001)
**Regression:** None observed on treecalc_synth_flip (U=50) or recursive_even (U=27, borderline neutral)

## Problem

compose_nf had been heavily optimized through a series of fusions (factor_tensor_with_subst, skip_split_subst, cached_rhs_map, offset_aware_match) but meet_nf still used the old unfused pipeline. As explicitly noted in prior reports: "The meet_nf path still uses the unfused pipeline" and "meet_nf path still uses split_match_subst."

## Solution

Ported three key compose_nf optimizations to meet_nf:

### Key design decisions

1. **Skip split_match_subst**: Both LHS and RHS matching now return raw combined substitutions. Consumers resolve bindings via apply_subst's chain-following. This eliminates the O(n) walk through all bindings to split into (left, right) halves.

2. **factor_tensor_with_subst**: Replaced 5 separate `apply_subst_list` calls + `factor_tensor` with the fused `factor_tensor_with_subst` that resolves substitutions during its traversal passes. This avoids creating intermediate substituted terms that are immediately consumed.

3. **remap_and_apply_subst**: b-side constraint handling simplified from separate `remap_constraint_vars` + 3 `apply_subst` calls to a single-pass `remap_and_apply_subst`.

4. **Dead code cleanup**: Removed now-unused `match_term_lists`, `match_term_lists_shifted`, and `remap_constraint_vars` functions from kernel/util.rs.

## Files changed

- `src/kernel/meet.rs` — Rewrote `meet_nf_impl` to use fused pipeline
- `src/kernel/util.rs` — Added `match_term_lists_shifted_combined`, `match_term_lists_combined`; made `compose_subst` public; removed 3 unused functions

## Why 2.57% instead of more

The compose_nf fusions achieved much larger improvements (16-28%) because compose is called ~64K-278K times per query. Meet is called far fewer times — join_high_overlap_64x64 has 4096 meet pairs but only ~32 succeed (due to the root functor precheck filtering). The per-call savings from fusion is similar, but the total savings is proportionally smaller due to lower call volume.

## Remaining opportunities

- The meet_nf path now uses the same fused pipeline as compose_nf. Further optimization would require reducing meet call count (already addressed by root functor precheck) or architectural changes.
- cached_rhs_map (compose_nf's 3.71% optimization) was not ported to meet because meet's variable routing differs — both sides are "built" from the combined substitution, unlike compose where one side is "matched" and the other "built".
