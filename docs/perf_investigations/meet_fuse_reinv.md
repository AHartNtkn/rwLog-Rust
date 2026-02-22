# Investigation: Meet NF Root Functor Precheck — Reinvestigation with Targeted Benchmark

## Summary

Reinvestigation of meet_fuse with join_high_overlap_64x64 as primary benchmark. KEEP: 35.0% improvement (U=100/100), no regression on full corpus (U=48).

**Baseline:** 1124.8 us (median, all values: 1125.2, 1122.8, 1128.8, 1136.9, 1138.3, 1109.6, 1134.9, 1124.5, 1077.9, 1123.1)
**After:** 731.5 us (median, all values: 730.2, 733.8, 734.6, 733.2, 727.8, 735.0, 730.8, 731.4, 731.6, 727.3)
**Improvement:** ~35.0% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001)
**Regression:** None observed (full corpus U=48, perfectly neutral)

## Problem

meet_nf_impl processes every NF pair through the full pipeline: collect_tensor, pre_create_shifted_vars, variable renaming, and matching — even when 99%+ of meet attempts fail. The original investigation attempted factor_tensor_with_subst fusion (paralleling compose_nf's approach) but was measured against the full corpus where meet is only 0.6% of total time (U=42).

## Solution

Added a root functor precheck at the top of meet_nf_impl that compares root functors of match_pats[0] and build_pats[0] before any expensive work. This catches obviously incompatible NF pairs with an O(1) comparison.

### Key design decisions

1. **Root functor precheck, not fusion** — The fusion approach (compose_subst + factor_tensor_with_subst) was re-attempted and confirmed to regress ~15%. compose_subst creates intermediate terms and factor_tensor_with_subst chases substitution chains, adding more overhead than it saves for meet_nf's use case. The precheck approach is simpler and far more effective.

2. **Inline nullary constant handling** — Inline nullary terms (ground constants stored directly in TermId) are the dominant term type in join workloads. `get_unlocked()` returns None for them. The helper uses direct TermId comparison for inline nullary constants, avoiding term store lookups entirely.

3. **Check both sides** — Two prechecks: one comparing a's build with b's match, and one comparing b's build with a's match, since meet_nf needs both directions to match.

## Files Changed

- `src/kernel/meet.rs` — Added `meet_root_functor_mismatch` helper (+~50 lines) and two precheck calls in `meet_nf_impl` before collect_tensor

## Why 35% Instead of More

The precheck eliminates the collect_tensor/matching cost for incompatible pairs, but compatible pairs (which succeed) still pay the full cost. The 35% reflects that the vast majority of meet attempts fail and the precheck catches most failures at O(1) cost.

## Why Invisible in Full Corpus

Meet operations are ~0.6% of total corpus time. The 35% improvement on meet-heavy workloads translates to ~0.2% corpus impact — well within noise (U=48). This is exactly the measurement problem that caused the original investigation to be incorrectly discarded.

## Remaining Opportunities

- **Deeper precheck** — Check child functors (depth-2) for pairs that pass root functor check. Same risk as compose's depth-2 precheck: per-call overhead may exceed savings.
- **Meet-specific indexing** — For DiagonalJoin meet pairs, index NFs by root functor to avoid generating incompatible pairs in the first place (paralleling compose's indexed_diagonal_join).
