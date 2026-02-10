# Investigation: Budgeted Eager Compose

## Summary

Attempted to process compose pairs eagerly in `on_new_left`/`on_new_right` with a budget to cap cascading. 64.6% improvement on recursive_even_backward_first64, but catastrophic regression on treecalc_synth_flip even at budget=1.

**Baseline:** 11142us (median, all values: 11453, 11414, 11135, 11123, 11383, 11149, 11155, 10628, 10637, 11024)
**After:** 3947us (median, all values: 3975, 3996, 3979, 3919, 3994, 5709, 3848, 3882, 3854, 3849)
**Improvement:** ~64.6% on primary (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001) on primary
**Regression:** CATASTROPHIC on treecalc_synth_flip — hangs at every budget level (16, 4, 2, 1)

## Problem

ComposeWork uses a cursor-based pair queue. When a new NF arrives from one side, a `ComposeCursor` is pushed. On the next `pre_step()` call, one cursor is popped and all pairs within it are processed. Results go to pending and are drained one per step.

This design requires ~4096 compose-related steps for even64 (cursor processing + pending drain). Each step goes through the full dispatch chain at ~2.7us per step, accounting for ~11ms of the 13.9ms baseline.

A previous "eager compose" (Round 14 item) eliminated cursors entirely and improved even64 by 50%, but caused synth_flip to hang (>60s). This investigation tested whether a budget could preserve the benefit while preventing the regression.

## Solution Attempted

Modified `on_new_left`/`on_new_right` to process pairs eagerly in a tight loop up to `COMPOSE_BUDGET` pairs, deferring remaining pairs to traditional cursors.

Tested budgets of 16, 4, 2, and 1.

## Results by Budget

| Budget | even64 | synth_flip | Compose count (synth) |
|--------|--------|------------|----------------------|
| Baseline (cursor) | ~11.1ms | ~2.45s | 324K |
| 16 | ~3.9ms | >10s (hang) | N/A |
| 4 | ~3.9ms | >10s (hang) | N/A |
| 2 | ~3.9ms | 9.9s (4.2x regression) | 1.1M |
| 1 | ~3.9ms | >10s (hang) | N/A |

## Key Finding: The Regression is About Execution Order, Not Batch Size

Even budget=1 (processing a single pair eagerly) causes synth_flip to hang. The root cause is not batch size but **execution timing**: eager compose makes results available one step earlier than cursor-based processing. This changes the order in which nested compose nodes produce results, which changes which branches get explored vs. pruned by CHR constraint propagation.

At budget=2, synth_flip's compose count jumped from 324K to 1.1M (3.4x), confirming that the changed execution order causes more branches to be explored before CHR pruning can kill them. The cascade creates a positive feedback loop at certain nesting depths.

### The One-Step Delay is Essential

The cursor-based design has a one-step delay between NF arrival (in `on_new_left`/`on_new_right`) and compose processing (in `pre_step` on the next call). This delay is not an implementation detail — it serves as a natural rate limiter that gives CHR constraint propagation time to prune failing branches before compose results cascade deeper. Any optimization that eliminates this delay, even for a single pair, fundamentally changes the execution order and can regress CHR-heavy workloads.

## Files changed

- `src/work/compose.rs` — Added COMPOSE_BUDGET constant and eager_compose_left/right methods

## Remaining opportunities

To capture the 64.6% improvement for tabling workloads without regressing CHR:

1. **Batch cursor processing within `pre_step`**: Process multiple cursors per `pre_step()` call instead of just one. This preserves the one-step delay between NF arrival and compose processing (results are still deferred to the next step) while amortizing dispatch overhead by doing more work per step.

2. **Workload-adaptive strategy**: Distinguish tabling-heavy vs. CHR-heavy compose nodes and apply different strategies. Tabling composes could use eager processing while CHR composes use cursor-based.

3. **Reduce per-step dispatch overhead**: Make the cursor-drain steps cheaper rather than eliminating them. step_node inlining, or a special "pending drain" fast-path that bypasses the full dispatch chain.
