# Investigation: skip_occurs_ground

**Status:** DISCARD
**Round:** 20
**Date:** 2025-02-09

## Hypothesis

`occurs_locked` is 3.63% of runtime on treecalc_synth_flip. Since ground terms (bit 31 set in TermId) cannot contain variables, an early `is_ground()` check should skip the full tree walk for ground subtrees, eliminating most occurs check overhead.

## Changes Made

- `src/matching.rs`: Added `is_ground()` early-return in `occurs_locked` to skip the recursive tree walk when the term is ground.

## Measurement

### Primary: treecalc_synth_flip
**Baseline median:** 2303649us
**Optimized median:** 2303732us
**U = 42/100 — DISCARD (no improvement)**

## Analysis

The occurs check already exits quickly for ground terms because ground terms have no variables — the function walks to a leaf without finding a match and returns false. The `is_ground()` shortcircuit saves only the overhead of one function call and array index vs. immediately discovering the term is `App(f, children)` and recursing into children that are themselves quickly resolved.

The 3.63% in profiles likely includes:
1. Non-ground terms that genuinely need the full walk (these are not helped by the ground check)
2. The function call overhead itself (which the ground check doesn't eliminate — it adds a different check before the existing walk)
3. Cache effects from the term store access pattern during matching

The optimization adds overhead (reading the TermId to check the ground bit) that roughly equals the savings from skipping the walk for ground terms.

## Remaining Opportunities

- **Eliminate occurs check entirely for linear patterns**: If a pattern has no repeated variables, the occurs check is unnecessary. A compile-time linearity analysis could skip it for most patterns.
- **Batch occurs checking**: Defer occurs checks until after all other matching succeeds, then check all bindings at once. This avoids checking bindings for matches that will fail for other reasons.
