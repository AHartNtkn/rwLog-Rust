# Investigation: Mega-Stack Plus (R46 Micro-Opts + Additional Changes)

## Summary

Combining R46 micro-optimizations (inline resolve_var_chain, SmallVec compose indices, SmallVec Subst) produced a 1.08% regression. The SmallVec<16> for Subst is counterproductive. DISCARDED.

**Baseline:** 72117.697 us (median, all values: 75975.039, 72775.098, 70973.977, 71806.043, 75011.611, 73051.929, 72429.350, 70324.481, 70746.268, 69236.247)
**After:** 72895.989 us (median, all values: 76004.162, 73467.105, 73063.945, 72623.069, 74008.312, 71126.541, 72728.032, 71613.374, 70555.587, 73951.797)
**Improvement:** -1.08% (regression)
**Mann-Whitney U:** 36/100 (p > 0.1, directional regression)
**Regression:** Primary workload itself regressed

## Problem

Same hypothesis as mega_stack — combining R46 micro-optimizations — but with an attempted 5th change for additional savings.

## Solution

Three changes implemented (Changes 3 and 5 from the brief were abandoned):

1. **#[inline(always)] on resolve_var_chain_unlocked**
2. **SmallVec<[usize; 8]> for compose indices**
3. **SmallVec<[Option<TermId>; 16]> for Subst bindings**

The cached root functor change (Change 3) and thread-local Subst reuse (Change 5) were not implemented due to complexity.

## Files changed

- `src/subst.rs` — #[inline(always)] + SmallVec for Subst
- `src/work/compose.rs` — SmallVec for compose indices

## Why regression

**SmallVec<[Option<TermId>; 16]> for Subst is actively harmful.** The Subst struct grows from Vec's 24 bytes to SmallVec's ~136 bytes (16 × 8 bytes + SmallVec metadata). This:

1. Increases stack frame size of match_term_lists_shifted_with_left_renaming_combined
2. Increases memcpy cost when Subst is passed by value or returned
3. Worsens cache utilization when multiple Substs exist during nested matching
4. The allocation savings (eliminating ~64K mallocs of 40-80 bytes) are smaller than the cache penalty from 5× larger stack objects

## Remaining opportunities

- **SmallVec with smaller capacity** (4 or 8) might work — balancing inline storage against cache pressure
- **Thread-local Vec reuse** (without SmallVec) could eliminate allocation without increasing struct size
- The optimization frontier appears reached for this codebase
