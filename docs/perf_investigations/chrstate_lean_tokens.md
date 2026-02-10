# Investigation: Eliminate token storage for single-head simplification programs

## Summary

Eliminated empty TokenStore HashSet allocations in ChrStateData for programs with `all_single_head_simplification = true`, where propagation tokens are never used.

**Baseline:** 306859us (median, all values: 307092, 306626, 311342, 312878, 314100, 304496, 302505, 299190, 307909, 304843)
**After:** 296092us (median, all values: 293306, 307696, 312309, 304006, 295858, 294295, 296327, 303228, 291236, 292857)
**Improvement:** ~3.5% (same-session comparison)
**Mann-Whitney U:** 82/100 (p < 0.01)
**Regression:** None observed on recursive_even_backward_first64 (U=43/100, neutral)

## Problem

ChrStateData always creates `TokenStore::new(program.rules.len())`, which allocates a `Vec<HashSet<TokenKey>>` with N empty HashSets (one per rule). For programs with `all_single_head_simplification = true` (no propagation rules), these tokens are never inserted, checked, or iterated. Yet every ChrStateData creation allocates them, every clone copies them, and every drop deallocates them.

With 259K normalize_owned calls and many ChrStateData creates/clones/drops, even empty HashSet overhead accumulates: Vec allocation for N entries, N empty HashSet metadata structures, clone copies N empty HashSets, drop deallocates all of them.

## Solution

Added `TokenStore::empty()` constructor that creates a zero-capacity Vec (`Vec::new()`), and used it at all 4 ChrStateData creation sites when `all_single_head_simplification` is true:

1. `ChrStateData::data_mut()` — initial state creation
2. `ChrState::new()` — empty state construction
3. `ChrState::introduce()` — constraint introduction
4. `thaw_chr()` — deserialization

All code paths that index `tokens.fired[rid]` are already gated by `rule.is_propagation`, which is always false for single-head simplification programs, making an empty `fired` Vec safe.

## Files changed

- `src/chr/mod.rs` — Added `TokenStore::empty()`, updated 4 creation sites to use it when `all_single_head_simplification` is true (+29 lines, -5 lines)

## Why 3.5% instead of 1-2%

1. **High frequency of ChrStateData lifecycle operations.** With 259K normalize_owned calls, the accumulated savings from skipping N empty HashSet allocations, clones, and drops per ChrStateData operation is significant.

2. **Cache-line effects.** Eliminating the HashSet metadata from ChrStateData reduces its memory footprint, improving cache locality for the hot ChrStateData clone path.

3. **Drop cascade savings.** The 1.74% drop_in_place<RawTable<(TokenKey,())>> in the profile was from dropping these empty-but-allocated HashSets.

## Remaining opportunities

- ChrStateData still carries other fields (agenda VecDeque, ChrStore with potentially dead entries) that are unused for empty-store states. Further slimming of ChrStateData for the common empty-store case could yield additional savings.
- The all_single_head_simplification flag could be used to eliminate other unused machinery (e.g., agenda processing, PredStore indexes) at creation time rather than at operation time.
