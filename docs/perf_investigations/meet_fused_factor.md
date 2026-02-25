# Investigation: Fuse RHS apply_subst + matching in meet_nf

## Summary

Fused the RHS apply_subst + matching pipeline in meet_nf_impl to eliminate intermediate term creation. KEEP: ~0.9% improvement on join_high_overlap (U=78/100, p < 0.05), no regressions.

**Primary workload (join_high_overlap, 200 iters):**
**Baseline:** 599.9 us (median, all values: 597.857, 605.142, 599.882, 601.179, 583.273, 598.225, 596.804, 601.946, 594.705, 601.435)
**After:** 595.2 us (median, all values: 595.702, 575.461, 595.122, 581.150, 595.241, 597.025, 595.807, 593.717, 602.800, 593.292)
**Improvement:** ~0.9%
**Mann-Whitney U:** 78/100 (p < 0.05)
**Regression:** None observed on treecalc_synth_flip, recursive_even_backward_first64, join_low_overlap

## Problem

The meet_nf_impl pipeline had a 3-step RHS matching process:
1. `apply_subst_list` — apply LHS substitution to a-side RHS terms, creating intermediate SmallVec
2. `apply_subst_shifted_list` — apply LHS substitution (shifted) to b-side RHS terms, creating another intermediate SmallVec
3. `match_term_lists_combined` — match the two intermediate lists against each other

Steps 1-2 created temporary term allocations that were immediately consumed by step 3. This is the same pattern that `fused_factor_compose` eliminated in compose_nf for a 27.8% improvement.

## Solution

Replaced the 3-step pipeline with a single `match_rhs_lists_with_pre_subst` function that applies both substitutions on-the-fly during matching, processing one pair at a time without bulk intermediate term creation.

This is a DIFFERENT approach from the prior failed meet_nf fusion attempt (docs/perf_investigations/meet_fuse.md), which tried to use compose_subst + factor_tensor_with_subst and regressed 15%. This approach targets only the RHS matching step, leaving the final factor_tensor_with_subst path unchanged.

### Key design decisions

1. **Target RHS matching, not the full pipeline:** The prior attempt tried to fuse the entire meet pipeline including factor_tensor, which caused a 15% regression. This approach surgically targets only the RHS matching step where intermediate terms are created.
2. **On-the-fly substitution during matching:** Instead of pre-substituting all terms, resolve variables through substitutions during the matching walk itself.
3. **Dead code removal:** The now-unused `apply_subst_list`, `apply_subst_shifted_list`, and `match_term_lists_combined` functions were removed.

## Files changed

- `src/kernel/meet.rs` — Replaced 3-step RHS pipeline with single fused call
- `src/kernel/util.rs` — Added `match_rhs_lists_with_pre_subst`; removed dead functions

## Why 0.9% instead of more

The improvement is small because most meet attempts fail at the LHS matching stage or root functor precheck (99% failure rate on join_high_overlap), never reaching the RHS matching step. Only the ~1% of meets that succeed LHS matching benefit from this optimization.

## Remaining opportunities

- The meet_nf factor_tensor step (on the success path) could still be fused, but the prior attempt's regression suggests this requires careful approach
- Meet optimization is increasingly constrained by the low success rate — most work is already avoided by the root functor precheck
