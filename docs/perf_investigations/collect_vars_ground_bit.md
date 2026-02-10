# Investigation: Ground-bit Subtree Skipping in collect_vars and apply_var_renaming

## Summary

Added `is_ground()` bit-test checks to `collect_vars_helper` and `apply_var_renaming` in `src/nf.rs`, allowing entire ground subtrees to be skipped without reading from the TermStore. ~1.5% improvement on `recursive_even_backward_first64`.

**Baseline:** 19.96ms (median, all values: 19.89, 19.83, 19.81, 20.02, 20.01, 19.94, 19.96, 19.99, 19.97, 20.08)
**After:** 19.66ms (median, all values: 19.71, 19.65, 19.68, 19.45, 19.89, 19.60, 19.57, 19.76, 19.81, 19.65)
**Improvement:** ~1.5% (same-session comparison)
**Mann-Whitney U:** 97/100 (p < 0.01)
**Regression:** None observed on treecalc_first16 (U=70/100, not significant)

## Problem

From profiling of `recursive_even_backward_first64`:
- `collect_vars_helper` = 1.96% of total time
- `apply_var_renaming` = 1.13% of total time
- Combined: ~3.1% of execution time

Both functions walk the full term tree via TermStore lookups, even for ground subtrees that by definition contain no variables. The `is_ground()` bit (bit 31 of TermId) already existed and was proven in `apply_subst` (src/subst.rs:180) but was not applied to these functions.

## Solution

Added a single `is_ground()` check at the top of each function's inner loop:

1. **`collect_vars_helper` (line 387-390)**: `if tid.is_ground() { continue; }` — skips ground terms entirely since they contain no variables.
2. **`apply_var_renaming` (line 503-507)**: `if tid.is_ground() { result_stack.push(tid); continue; }` — pushes ground terms unchanged since variable renaming has no effect on them.

## Files changed

- `src/nf.rs` — Added ground-bit checks in `collect_vars_helper` and `apply_var_renaming`

## Why 1.5% instead of 3%

The 3.1% profile figure represents total time in these functions, but not all of that time is spent on ground subtrees. The `recursive_even_backward_first64` workload uses Peano naturals which have relatively shallow ground substructure. Workloads with larger ground terms would see proportionally bigger wins.

## Pattern

This is the same `is_ground()` pattern already proven in `apply_subst` (src/subst.rs:180). It's a zero-cost check (single bit test on a value already in register) that avoids TermStore lock acquisition and tree traversal.
