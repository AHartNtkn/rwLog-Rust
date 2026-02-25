# Investigation: Pre-Compute Match/Build Variable Ranges in NfInner

## Summary

Added match_var_range and build_var_range metadata to NfInner for compose precheck. DISCARD: the hypothesis was fundamentally unsound — after NF factoring, variable ranges are always 0..arity-1, so they provide no discriminative power for compose rejection.

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 218844 us (median, all values: 211735, 384744, 221417, 224365, 216924, 216525, 219090, 215981, 218844, 219695)
**After:** 218451 us (median, all values: 210292, 248388, 230724, 214356, 221102, 218451, 223396, 215418, 215160, 215136)
**Improvement:** ~0% (within noise)
**Mann-Whitney U:** 59/100 (not significant)

## Problem

The compose_nf precheck design space (root functor, multi-position, depth-2) targets functor structure. The hypothesis was that variable range metadata would provide a different, orthogonal axis of information for early rejection: if NF_a's build-side variable range (after renaming-apart offset) doesn't overlap NF_b's match-side variable range, the compose must fail.

## Why It Failed

1. **The hypothesis was fundamentally unsound.** After NF factoring, match patterns always have vars 0..in_arity-1 and build patterns have vars 0..out_arity-1. Variable ranges are entirely determined by DropFresh arities, not by pattern structure. They always start at 0, so they trivially overlap with any non-empty range.

2. **Matching success depends on structural compatibility** (functor names, nesting), not variable index ranges. A variable on either side can match any term regardless of its index.

3. **The only valid precheck is ground-vs-ground**: when both sides have NO variables (arity=0), reject if patterns differ structurally. This case almost never occurs in tree calculus workloads.

4. **Variable ranges at the NF level are the wrong axis of information.** The var_range infrastructure in TermStore is powerful for subtree skipping within a traversal (as demonstrated by subst_var_range's 36.5% improvement), but NF-level ranges collapse to trivial 0..n ranges after factoring.

## Files changed

- `src/nf.rs` — Added match_var_range and build_var_range fields to NfInner; added ground-vs-ground precheck in compose_nf

## Remaining opportunities

- Compose precheck design space is now thoroughly exhausted: root functor (KEEP), multi-position (DISCARD), depth-2 (DISCARD), variable compatibility (DISCARD), NF variable ranges (DISCARD). Five approaches tried, only root functor provides value.
- Further compose_nf optimization should target the matching/substitution pipeline itself, not additional prechecks
- The var_range infrastructure remains valuable for within-traversal optimizations (fast_occurs, subst_var_range) but not for NF-level structural compatibility
