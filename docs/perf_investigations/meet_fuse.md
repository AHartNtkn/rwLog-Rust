# Investigation: Fuse meet_nf Pipeline

## Summary

Applied the same factor_tensor fusion technique from compose_nf to meet_nf. DISCARDED: meet workloads are too small a fraction of corpus time (0.6%) to produce a measurable signal.

**Full corpus U:** 42/100 (not significant)
**Verdict:** DISCARD

## Problem

meet_nf still uses the unfused pipeline: `apply_subst_list → factor_tensor`. The compose_nf fusion (factor_tensor_with_subst) gave 27.8% improvement. Hypothesis: the same fusion could improve join-heavy workloads (join_high_overlap: 4096 meets, join_low_overlap: 4096 meets).

## Implementation

Replaced the `apply_subst_list` + `factor_tensor` pipeline in `meet_nf_impl` with `compose_subst` + `factor_tensor_with_subst`. Eliminated 6 `apply_subst_list` calls by composing substitutions into a single combined substitution, then passing original patterns with the combined substitution to the fused function. All tests pass (719 unit + 23 semantic + 3 symmetry property tests).

## Why It Failed

1. **Meet workloads are 0.6% of total corpus** — even a 20% improvement on meet-heavy cases would be ~0.1% total improvement, well below noise
2. **`compose_subst` still creates intermediate terms** in substitution values, partially offsetting the savings from avoiding `apply_subst_list` on the final patterns
3. **Compose is called 100x+ more than meet** — the compose fusion was impactful because it affects 278K calls vs 241 meet calls for treecalc
4. **No codegen effects** — changing meet_nf code did not affect treecalc via instruction cache or optimizer decisions

## Key Insight

The optimization is correct but the target is too small. For any further meet_nf optimization to register on the full corpus, the benchmark suite would need significantly more meet-heavy workloads.

## Files Changed (not merged)

- `src/kernel/meet.rs` — Replaced unfused pipeline with factor_tensor_with_subst
