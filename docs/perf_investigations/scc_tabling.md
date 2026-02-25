# Investigation: SCC-Based Tabling Scheduling

## Summary

Investigated MP7 SCC-aware scheduling for mutually recursive tabling groups. DISCARD: no optimization opportunity — rwlog's call-context tabling creates trivial SCCs for all current benchmarks.

## Problem

Standard Datalog engines compute SCC DAGs at evaluation time and schedule fixpoint iterations per-SCC, processing bottom-up. The hypothesis was that rwlog's tabling could benefit from the same approach by grouping mutually recursive predicates and reducing cross-component compose attempts.

## Analysis: Why SCC Scheduling Cannot Help

### Architecture mismatch

rwlog uses **call-context tabling**: each `CallKey` (relation + left/right boundary NFs) creates an independent table with its own fixpoint loop. This is fundamentally different from Datalog's predicate-level tabling. Cross-table dependencies are mediated through the search tree (ComposeWork, Or interleaving), not through shared fixpoint iterations. The semi-naive watermark mechanism already ensures each table only replays delta answers.

### Benchmark analysis

1. **graph_reach_64** — single self-recursive relation (`reach` calls only itself). SCC is trivially `{reach}`. Steps=7198, compose=382. No inter-table scheduling opportunity.

2. **left_rec_32** — single self-recursive relation. SCC is trivially `{left_rec}`. Steps=336, compose=66.

3. **recursive_even_backward_first64** — the ONLY benchmark with mutual recursion (`even`↔`odd`), but uses streaming mode (first_n=64), not fixpoint exhaustion. Both relations would be in the SAME SCC, so no multi-tier scheduling to exploit.

### Missing preconditions

To benefit from SCC scheduling, a workload would need: (a) multiple mutually recursive relations, (b) evaluated to fixpoint exhaustion, (c) with multiple distinct SCCs in the call graph. None of the current benchmarks satisfy all three conditions.

## Files Changed

None (investigation only).

## Insights

- rwlog's call-context tabling is architecturally different from Datalog's predicate-level tabling. SCC scheduling is a Datalog optimization that assumes predicate-level grouping.
- All recursion-heavy benchmarks use single self-recursive relations with trivial SCCs.
- This finding should inform future MP7 work: improvements to rwlog's tabling should focus on per-table optimizations (replay strategy, answer indexing) rather than cross-table scheduling.
