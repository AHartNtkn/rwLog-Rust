# Investigation: Branch Pruning via Root Functor Compatibility

## Summary

Added root functor compatibility checking in PipeWork::advance_or to prune Or branches before creating splits. DISCARD: U=66/100, no improvement. Or branches at the pipe level are rarely simple Atoms — most contain Call/Fix/Seq structures that can't be statically checked, so pruning rarely fires. The existing compose_nf root functor precheck already catches incompatible compositions at the point of actual fusion.

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 210571 us (median, all values: 207468, 211301, 210337, 209466, 211608, 213431, 212534, 210805, 210325, 212433)
**After:** 209687 us (median, all values: 211935, 209100, 212506, 208239, 208518, 211193, 208467, 210274, 208439, 211747)
**Improvement:** ~0.4% (within noise)
**Mann-Whitney U:** 66/100 (not significant)

## Problem

The hypothesis was that Or branches in PipeWork could be pruned before splitting if their root functor is incompatible with the downstream boundary NF. This would avoid creating the Or split, stepping into the branch, and failing at compose_nf time.

## Solution Attempted

Added `boundary_tag_for_end` and `branch_compatible` helper methods to PipeWork. In `advance_or`, before creating Or splits, check if each branch's root functor is compatible with the current boundary NF. Skip branches that are statically incompatible.

## Why It Failed

1. **Or branches at the pipe level are rarely simple Atoms.** In treecalc_synth_flip and most real workloads, Or nodes that reach `advance_or` contain Call/Fix/Seq structures, not bare Atoms. The `branch_compatible` method conservatively returns `true` for all non-Atom branches, so pruning rarely fires.

2. **The existing `try_dispatch_or_atoms` already handles the narrow case.** When a Call body is a flat Or-of-Atoms, functor filtering is already applied via cached dispatch tables. This optimization attempted to generalize to the broader Or split path but encountered structurally complex branches.

3. **compose_nf root functor precheck already catches incompatible compositions at ~1-2ns per pair.** The cost of creating the Or split and then failing at compose time is already low per-attempt.

4. **Fourth confirmation that Or-level filtering is a dead end.** After share_or_prefix (U=56), dedup_at_emission (0.8% duplication), flatten_or_spine (regression), and now branch_prune_compat (U=66), the Or execution path appears well-optimized.

## Files changed

- `src/work/pipe.rs` — Added root functor compatibility checking in `advance_or`
- `src/work/tests.rs` — Updated tests for new boundary handling

## Remaining opportunities

- Or-level pruning of simple Atom branches is a dead end — compose_nf precheck handles this
- Deeper static analysis of Rel variants (walking into Seq/Fix/Call to extract root tags) could help but adds complexity
- Batch branch stepping (Disjunction #5) addresses a different aspect — per-step overhead amortization
