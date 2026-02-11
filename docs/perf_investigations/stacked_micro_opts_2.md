# Investigation: Stacked Micro-Optimizations Round 2

## Summary

Combining three micro-optimizations (#[inline(always)] on resolve_var_chain_unlocked, SmallVec for compose indices, cached NF root functors) produced a directional 1.73% improvement but failed to reach statistical significance. DISCARDED.

**Baseline:** 71808.379 us (median, all values: 73332.749, 69245.600, 71098.584, 72795.708, 70771.488, 73200.208, 71191.094, 72425.664, 70695.065, 72431.954)
**After:** 70563.592 us (median, all values: 69566.740, 71208.164, 70315.362, 69631.572, 69707.935, 71758.727, 70811.822, 70159.722, 71129.592, 73046.540)
**Improvement:** ~1.73% (not significant)
**Mann-Whitney U:** 70/100 (p > 0.05, not significant)
**Regression:** N/A (primary failed threshold)

## Problem

After R44's successful stacking approach (3.7%, U=97), the hypothesis was that another set of three micro-optimizations targeting different hot paths could produce a similar cumulative effect.

## Solution

Three changes implemented together:

### Change 1: #[inline(always)] on resolve_var_chain_unlocked (~0.5% estimated)

Upgraded from `#[inline]` to `#[inline(always)]` on `resolve_var_chain_unlocked` in `src/subst.rs`. This function is called from apply_subst_core's inner loop (~38% of runtime). Same pattern as R44's match_flat_ops/match_head_direct win.

### Change 2: SmallVec for compatible indices in ComposeStrategy (~0.3% estimated)

Replaced `Vec<usize>` with `SmallVec<[usize; 8]>` for `compatible_r` and `compatible_l` in `ComposeCursor` and their construction functions. Eliminates heap allocation for the typical case of 1-4 compatible functor matches.

### Change 3: Cache root functor in NfInner (~0.5% estimated)

Added `cached_build_root: Option<FuncId>` and `cached_match_root: Option<FuncId>` to NfInner. Used in compose_nf_impl precheck and build_root_tag/match_root_tag to avoid terms.get_unlocked() store lookups.

### Key design decisions

1. Stacking approach: Following R44's proven pattern of combining sub-threshold changes.
2. Targeted different hot paths than R44 (apply_subst variable resolution, compose strategy allocation, compose_nf precheck).
3. Used store-lookup fallback for cached root functors when cache is None (graceful degradation).

## Files changed

- `src/subst.rs` -- #[inline(always)] on resolve_var_chain_unlocked
- `src/work/compose.rs` -- SmallVec for ComposeCursor, cached root tag fast-path
- `src/nf.rs` -- cached_build_root/cached_match_root fields in NfInner
- `src/kernel/compose.rs` -- Use cached root functors in precheck

## Why 1.73% instead of 3-4%

The R44 stacking targeted HOTTER code paths:
- match_flat_ops/match_head_direct are called per-CHR-rule-attempt (extremely hot)
- instantiate_pat SmallVec avoids allocation in the CHR body execution path
- The ground pre-check eliminates function calls in apply_subst_to_data

The R46 targets are less frequently exercised:
- resolve_var_chain_unlocked may already be inlined by LLVM (small function with #[inline])
- Compose cursor allocation is per-NF-arrival, not per-compose-attempt
- get_unlocked store lookups for root functors are already very cheap (direct Vec index)

The combined ~1.73% is within measurement noise (CV ~1.6-1.8%), making it indistinguishable from random variation at N=10.

## Remaining opportunities

- **Combine with subst_smallvec**: The subst_smallvec investigation showed a similar ~1.1% borderline improvement. Stacking ALL changes from both R46 candidates might produce ~2.8% cumulative improvement closer to the significance threshold.
- The optimization landscape is approaching diminishing returns. Individual micro-optimizations produce <2% effects that are below measurement sensitivity at N=10.
