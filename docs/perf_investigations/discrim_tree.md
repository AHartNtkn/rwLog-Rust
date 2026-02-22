# Investigation: Discrimination Tree for Depth-2+ Dispatch

## Summary

Investigated MP3 depth-2+ discrimination tree for wide_match_512. DISCARD: 3.8% improvement on wide_match_512 (U=77) but regresses recursive_even by 2.5% (U=5) and treecalc_synth_flip by 1.9% (U=11).

**Primary workload (wide_match_512):**
**Baseline:** 888.6 us (median, all values: 891.4, 1241.0, 859.8, 857.4, 866.6, 888.6, 1224.8, 855.5, 1217.6, 879.7)
**After:** 855.2 us (median, all values: 1192.1, 1044.5, 857.8, 843.9, 839.6, 1217.1, 845.9, 853.6, 835.3, 855.2)
**U statistic:** 77/100
**Regression:** recursive_even U=5 (+2.5%), treecalc_synth_flip U=11 (+1.9%)

## Problem

wide_match_512 has 512 rules sharing top functor `pair`. Existing root functor precheck passes for all 512, providing no filtering. Depth-2 functor checks could narrow the candidate set.

## Approaches Tried

### 1. ComposeStrategy DeepIndex (HashMap-based discrimination tree in DiagonalJoin)

Indexed NFs by depth-2 functor tags in ComposeStrategy. DISCARDED: ~26% regression on recursive_even from enlarged ComposeWork struct requiring boxing. Also, wide_match_512's compose path goes through PipeWork's direct compose_nf calls (pipe boundary absorption), NOT through ComposeStrategy's diagonal join — wrong code path.

### 2. Kernel compose_nf depth-2 precheck

Added child functor checks after existing root functor check in compose_nf_impl. Even the most minimal version adds ~0.7us per compose_nf call from extra `get_unlocked` lookups. This accumulates over hundreds of calls on workloads that don't benefit.

### Key design decisions

1. **Per-call overhead is the killer** — compose_nf is called on every compose attempt. Adding any code changes the function's icache footprint and branch prediction. The overhead is tiny per-call but measurable when accumulated.
2. **Root-failing pairs already fail fast** — pairs that match root functor but fail at depth-2 were already failing quickly in the matcher. The savings per rejected pair are small.

## Files Changed

None merged (DISCARD).

## Why Only 3.8% on wide_match_512

The depth-2 precheck eliminates heavyweight matching work for 511/512 rules, but compose_nf's existing root check already causes fast failure. The overhead saved per rejected pair is small because root-matching pairs that fail at depth-2 were already failing quickly.

## Remaining Opportunities

- **Or-spine level dispatch**: Instead of per-compose_nf checks, pre-index the 512-rule Or at relation construction time and dispatch directly to matching rules, skipping 511 compose_nf calls entirely. This is the compiled_dispatch approach extended to depth-2+.
- **Selective activation**: Only activate depth-2 indexing for high-arity Or relations (>32 rules) to avoid overhead on small relations.
- **nonlinear_match_64 showed 28% improvement** (U=82) — depth-2 checks are highly effective for certain patterns. A targeted approach could capture this.
