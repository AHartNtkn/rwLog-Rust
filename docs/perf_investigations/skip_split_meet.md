# Investigation: Eliminate split_match_subst from meet_nf Success Path

## Summary

Investigated porting the skip_split_subst compose optimization to meet_nf. DISCARD: the optimization was already implemented — meet_nf's success path already uses the raw combined substitution without splitting.

**No performance measurement needed** — the optimization target does not exist.

## Problem

The hypothesis was that meet_nf's success path still called split_match_subst to split the combined substitution into (left, right) halves, and that eliminating this (as was done for compose_nf with a 16.1% improvement) would yield similar gains on meet-heavy workloads.

## Why It Failed

1. **The optimization was already implemented.** The meet_nf success path in `src/kernel/meet.rs` already uses `match_term_lists_shifted_combined()` which returns the raw combined substitution (no split).

2. **meet_nf line 152** uses `match_rhs_lists_with_pre_subst()` which fuses RHS apply_subst + matching into a single pass, returning a combined substitution.

3. **The combined `meet_subst` is passed directly** to constraints and `factor_tensor_with_subst` — no `split_match_subst` call exists anywhere in meet_nf's success path.

4. **This was completed as part of prior meet_nf fusion work** (meet_fused_factor investigation, commit 8354150).

## Files changed

None — investigation only, no code changes.

## Remaining opportunities

- meet_nf success path is now well-optimized: combined substitution (no split), fused RHS matching (no intermediate terms)
- The remaining meet_nf optimization target is the factor_tensor step, but prior attempts regressed 15%
- Meet optimization is constrained by the low success rate — 99% of meets fail before reaching the success path
