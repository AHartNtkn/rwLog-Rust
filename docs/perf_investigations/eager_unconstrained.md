# Investigation: Compile-Time Eager Compose for Trivial Constraint Types

## Summary

Added a compile-time constant `ALWAYS_EMPTY` to `ConstraintOps` that enables eager compose pair processing when the constraint type is always trivial (like `()`). ~3.7% improvement on recursive_even_backward_first64.

**Baseline:** 10857us (median, all values: 10772, 10596, 11175, 11201, 10631, 10530, 11024, 10577, 11149, 10943)
**After:** 10451us (median, all values: 10236, 10390, 10298, 10555, 10512, 10378, 10769, 10638, 10745, 10315)
**Improvement:** ~3.7% (same-session comparison)
**Mann-Whitney U:** 87/100 (p < 0.01)
**Regression:** None observed on treecalc_synth_flip (U=47/100, neutral)

## Problem

The cursor-based compose pair queue adds dispatch overhead to every compose operation. When a new NF arrives from one side, a `ComposeCursor` is enqueued. On the next `pre_step()` call, one cursor is popped and all pairs processed. Results go to pending and are drained one per step.

Prior investigation (compose_budget) showed that eager compose (processing pairs directly in `on_new_left`/`on_new_right`) gives 64.6% improvement on even64, but causes catastrophic regression on treecalc_synth_flip because the one-step delay between NF arrival and cursor processing is essential for CHR constraint propagation timing.

## Solution

Added `const ALWAYS_EMPTY: bool` to the `ConstraintOps` trait with default `false`. The `()` implementation sets it to `true`. The `ChrState<T>` implementation inherits the default `false`.

In `ComposeStrategy`, the `on_new_left`, `on_new_right`, and `pre_step` methods branch on `C::ALWAYS_EMPTY`:
- When `true` (C=()): pairs are composed eagerly inline, pushing results directly to pending
- When `false` (C=ChrState): cursor-based deferral as before

Since `ALWAYS_EMPTY` is a const, the dead branch is eliminated at compile time via monomorphization. For C=(), only the eager code path exists. For C=ChrState<T>, only the cursor code path exists.

### Key design decisions

1. **Compile-time decision vs runtime check**: Using a trait constant rather than checking `nf.constraint.is_empty()` at runtime avoids the risk of NFs with dynamically-empty CHR constraints in CHR workloads being eagerly processed, which could change execution order and regress CHR pruning.

2. **Preserving cursor-based safety for CHR**: Even if individual NFs in a CHR workload happen to have empty constraints, the cursor-based path is used for all of them, preserving the one-step delay essential for CHR constraint propagation.

## Files changed

- `src/constraint.rs` — Added `const ALWAYS_EMPTY: bool` to `ConstraintOps` trait (default false), set to `true` for `()` impl
- `src/work/compose.rs` — Added compile-time branching in `on_new_left`, `on_new_right`, and `pre_step` to eagerly compose pairs when `C::ALWAYS_EMPTY` is true

## Why 3.7% instead of 64.6%

The original compose_budget investigation measured 64.6% improvement from eager compose. The discrepancy is because numerous prior optimizations have already substantially reduced compose dispatch overhead:

1. **In-place stepping** (diagonal_join_take_self_overhead) eliminated 88% of allocations
2. **Diagonal hash dedup** reduced duplicate processing
3. **Fused renumber_vars** (collect_apply_fuse) eliminated redundant variable traversals
4. **Arc-wrapped DropFresh map** reduced clone costs

These optimizations collectively made each compose step much cheaper, reducing the relative benefit of eliminating cursor dispatch steps. The cursor overhead that remains is a smaller fraction of total execution time.

## Remaining opportunities

- The cursor-based path for CHR workloads still has dispatch overhead. Batching multiple cursors per `pre_step()` call (preserving the one-step delay) could help CHR workloads.
- For unit-constraint workloads, the pending drain still happens one per step. A multi-emit API could eliminate this remaining overhead.
