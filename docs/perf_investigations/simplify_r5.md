# Investigation: Consolidation Round 5 — build_remap_map and allocation hoisting

## Summary

Multi-target consolidation: simplified `build_remap_map` with `Option::max()` + iterator, hoisted allocation in `match_term_lists_shifted_with_left_renaming_combined`. Net -11 lines. KEEP (consolidation, U=45, neutral performance).

**Baseline:** 45041 us (median, all values: 44968, 44901, 45052, 45030, 45041, 45059, 45135, 45100, 45083, 45023)
**After:** 45011 us (median, all values: 44960, 44874, 45082, 45008, 45013, 45010, 45027, 45042, 45016, 44914)
**Improvement:** ~0.1% (neutral)
**Mann-Whitney U:** 45/100 (not significant — expected for consolidation)
**Regression:** None observed on full corpus

## Changes

### 1. Simplified `build_remap_map` in `kernel/util.rs`

Replaced a verbose 4-arm match block with `Option::max()` and iterator `.map().collect()`. The original code manually matched on `(Some(a), Some(b))`, `(Some(a), None)`, `(None, Some(b))`, `(None, None)` — this is exactly what `Option::max()` does. Result: -8 lines, more idiomatic.

### 2. Hoisted allocation in `match_term_lists_shifted_with_left_renaming_combined`

Moved the `rhs_map_opt` Vec allocation outside the inner loop in `kernel/util.rs`. The Vec was being allocated on every iteration even though its structure only depends on the outer pattern, not the per-iteration matching state.

## Files changed

- `src/kernel/util.rs` — Simplified `build_remap_map` match block to `Option::max()` + iterator; hoisted `rhs_map_opt` allocation out of inner loop

## Remaining opportunities

- Further consolidation targets are becoming sparse after 5 rounds of cleanup (rounds 1-5 removed ~130+ lines total)
- Any remaining cleanup should focus on areas actively being modified by performance optimizations
