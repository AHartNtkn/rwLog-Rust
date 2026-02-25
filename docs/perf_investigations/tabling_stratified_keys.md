# Investigation: Stratified Call-Key Table Entries

## Summary

Investigated whether call-key table entries could use stratified keys separating shape from constraint components. DISCARD: instrumentation shows zero shape overlap across all benchmarks — every table differs structurally, not just by constraints. The optimization premise is disproven.

**No performance measurement needed** — the optimization target does not exist.

## Problem

The hypothesis was that structurally identical calls with different constraint states create separate tables, causing redundant fixpoint iterations. Stratifying keys (shape-only for table lookup, constraints as post-filter) could enable more table sharing.

## Why It Failed

1. **Zero shape overlap across all benchmarks.** Instrumentation measured total tables vs distinct shape-only keys:
   - recursive_even_backward_first64: 127 tables, 127 distinct shapes (0 overlap)
   - treecalc_synth_flip: 30 tables, 30 distinct shapes (0 overlap)
   - graph_reach_64: 64 tables, 64 distinct shapes (0 overlap)
   - left_rec_32: 1 table, 1 distinct shape (0 overlap)
   - constraint_* benchmarks: 0 tables (no tabling used)

2. **CallKey diversity comes from structural differences.** Different rel/bind_id/NF patterns, not constraint differences, drive table creation. Each call site x input pattern produces a unique structural key.

3. **Most benchmarks use empty constraints.** ChrState with no data makes all constraint comparisons trivially equal — constraints are already a non-factor in table keying.

4. **treecalc_synth_flip has non-empty constraints but still zero overlap.** Its 30 tables all have distinct shapes regardless of constraint state.

## Files changed

None — instrumentation only, no code changes merged.

## Remaining opportunities

- Table count reduction via constraint stratification is a dead end — zero overlap exists
- Future tabling optimization should focus on reducing per-table fixpoint iteration cost, not table count
- Table count correlates with problem size (127 for 64-element recursive_even, 64 for graph_reach), suggesting one table per "call site x input pattern"
