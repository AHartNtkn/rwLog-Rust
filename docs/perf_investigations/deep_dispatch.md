# Investigation: Depth-2 Dispatch Indexing at Or-Spine Level

## Summary

Implemented depth-2 functor dispatch in `try_dispatch_or_atoms` to narrow candidate rules when root-functor dispatch leaves many collisions. KEEP: 27.2% improvement on wide_match_512 (U=100/100), 25.4% on nonlinear_match_64 (U=84/100), zero overhead on other workloads.

**Primary workload (wide_match_512, 50 iters):**
**Baseline:** 821.9 us (median, all values: 821.546, 821.656, 823.432, 821.072, 820.148, 822.156, 826.034, 821.883, 820.255, 833.489)
**After:** 599.0 us (median, all values: 597.992, 607.656, 594.528, 596.088, 593.633, 597.854, 602.566, 600.537, 601.283, 603.537)
**Improvement:** ~27.2% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001)
**Regression:** None observed on treecalc_synth_flip (U=58) or recursive_even (U=50)

## Problem

`wide_match_512` has 512 rules all sharing root functor `pair`. The existing `compiled_dispatch` in `try_dispatch_or_atoms` indexes by root functor only, so all 512 rules survive the filter. Every query attempts 512 compose operations, of which only 1 succeeds (the rule matching the specific `pair(cN, ...)` pattern).

A prior investigation (discrim_tree) tried adding depth-2 checks INSIDE `compose_nf` but regressed 2.5% on recursive_even due to per-call overhead. The insight: dispatch must happen at the Or-spine level (once per relation call), not per compose attempt.

## Solution

Extended `try_dispatch_or_atoms` with a secondary child[0] functor filter that activates only when the root-functor filter leaves more than 8 candidates. For each surviving atom, extract the functor of child position 0 (first argument of the root constructor) and filter by compatibility with the input's child[0] functor.

### Key design decisions

1. **Threshold of 8**: Only apply depth-2 filtering when >8 candidates survive root-functor dispatch. This ensures zero overhead on workloads with distinct root functors (treecalc, recursive_even) where depth-1 dispatch already narrows sufficiently.

2. **Or-spine level, not per-compose**: The filtering happens in `try_dispatch_or_atoms` which runs once per Call resolution, not in `compose_nf` which runs per pair. This amortizes the cost over all compose attempts.

3. **Wildcard handling**: If the boundary's child[0] is a variable (not a functor), the depth-2 filter is skipped entirely (no information to filter on). Rules with variable child[0] always pass (tags_compatible returns true for Wildcard).

## Files changed

- `src/work/mod.rs` — Added `term_child0_tag`, `build_child0_tag`, `match_child0_tag` helper functions (+39 lines)
- `src/work/pipe.rs` — Extended `try_dispatch_or_atoms` with depth-2 filter block when compatible.len() > 8 (+25 lines)

## Why 27% instead of more

The 27% improvement reflects eliminating 511 of 512 compose attempts. The remaining time is the single successful compose plus overhead from the 1025→3 step reduction and the dispatch filtering itself. The per-query base cost (term interning, factoring, output construction) sets a floor.

## Remaining opportunities

- **Depth-3+ indexing**: For workloads where child[0] also collides across many rules, further levels could help. However, no current benchmark exercises this pattern.
- **Pre-built index map**: Currently re-scanning compatible Vec on each dispatch. For very large Or bodies (1000+ rules), a pre-built HashMap keyed by (root, child0) pair could avoid the linear scan. The current threshold-gated approach is sufficient for 512 rules.
- **Combined with compiled decision trees**: This ad-hoc depth-2 filter could be generalized into a compiled decision tree per Or body, supporting arbitrary depths and multiple child positions.
