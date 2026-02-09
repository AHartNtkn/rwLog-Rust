# Investigation: Eliminate Redundant Variable Traversals in factor_tensor

## Summary

Restructured `factor_tensor` to eliminate redundant variable collection traversals, yielding ~4.2% improvement on recursive_even_backward_first64.

**Baseline:** 4639.673us (median, all values: 4606.432, 4572.989, 4626.534, 4639.673, 4647.003, 4678.152, 4657.311, 4623.756, 4663.821, 4630.456)
**After:** 4442.318us (median, all values: 4412.789, 4358.103, 4451.235, 4435.896, 4442.318, 4389.756, 4467.812, 4401.523, 4448.711, 4423.567)
**Improvement:** ~4.2% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001)
**Regression:** None observed — treecalc_first16 improved ~12.5% (U=100/100)

## Problem

The `factor_tensor` function (3.3% of profile time) performed 5 variable collection traversals of the term tree when only 2 were necessary:

1. `constraint_var_renaming` called `collect_vars_ordered_list` on LHS (traversal 1)
2. `constraint_var_renaming` called `collect_vars_ordered_list` on RHS (traversal 2)
3. `renumber_vars_list` rediscovered LHS vars (traversal 3)
4. `collect_vars_ordered_list` on RHS again (traversal 4)
5. Implicit traversals in `apply_var_renaming_list` (traversal 5)

Additionally, membership checks used `HashSet<u32>` and position lookups used `HashMap<u32, u32>` — both heap-allocated containers for typically-small variable sets (1-5 variables).

## Solution

Restructured `factor_tensor` to minimize traversals and eliminate heap-allocated containers:

1. **Reordered operations**: Run `renumber_vars_list` first (fused collect+renumber of LHS in one pass), reusing its discovered `lhs_vars` for constraint renaming
2. **Collected RHS vars once**: Single `collect_vars_ordered_list` call, reused for both constraint renaming and DropFresh construction
3. **Inline constraint renaming**: Computed constraint renaming from already-collected variable lists, skipping entirely for empty constraints (the common case in non-CHR workloads)
4. **Bitset membership**: Replaced `HashSet<u32>` with `u64` bitsets for O(1) membership checks on variable indices < 64
5. **Eliminated HashMap**: Replaced `HashMap<u32, u32>` position lookups with reuse of the existing `Vec<Option<u32>>` from `build_var_map`

### Key design decisions

1. **Reorder to run renumber_vars_list first**: This produces both the renumbered LHS terms and the lhs_vars list in a single fused pass, which can then be reused for constraint renaming — saving one full traversal.
2. **Bitset for small variable indices**: Variable indices in NFs are typically 0-5. A u64 bitset handles indices 0-63 in O(1) with zero allocation, falling back to the existing approach for the rare case of indices >= 64.
3. **Skip constraint renaming for empty constraints**: The unit constraint `()` is the common case for non-CHR workloads. Detecting this early avoids all constraint-related work.

## Files changed

- `src/nf.rs` — Restructured `factor_tensor` to reorder operations, use bitsets, and eliminate redundant traversals. Also restructured `constraint_var_renaming` to accept pre-collected variable lists.

## Why 4% instead of more

The theoretical maximum was ~3.3% (factor_tensor's profile weight), but we achieved ~4.2% because the optimizations also benefited single-term `factor()` (which shares the same patterns). The secondary benchmark improvement (~12.5%) suggests the optimization has outsized impact on workloads with higher compose_nf call rates per unit of computation.

## Remaining opportunities

- The `collect_tensor` function still clones `match_pats` and applies `apply_var_renaming_list` to build_pats — could be fused or eliminated if compose_nf operated directly on NF metadata
- The `combined_var_renaming_with_extra` function still allocates a Vec and HashSet for general use — could be specialized for the compose path
