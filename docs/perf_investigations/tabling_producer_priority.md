# Investigation: Producer Prioritization by Yield Rate

## Summary

Investigated producer prioritization for tabling via two approaches: burst stepping and dry-step skip scheduling. DISCARD: burst stepping causes stack overflow due to recursive step_node nesting with nested FixWork. Dry-step skip scheduling is sound but targets a pathology (stuck producers) that doesn't occur in current benchmarks.

## Problem

When multiple tabled calls are active, some producers may be "stuck" — consuming CPU without producing new answers. The hypothesis was that prioritizing productive producers (or deprioritizing unproductive ones) could reduce wasted work.

## Approaches Tried

### 1. Burst Stepping (Failed — Stack Overflow)

Stepping a producer multiple times per step_in_place call. step_node → Fix::step_in_place → step_table_producer → step_node is recursive. With nested Fix (mutual recursion), burst factor B at depth D gives B^D stack growth. Stack overflows at even B=2.

### 2. Dry-Step Skip Scheduling (Implemented, Not Measurable)

When a FixWork producer yields no new answer for 3+ consecutive steps AND no external progress, skip stepping the producer entirely and let Or-rotation give CPU to other work. Added `dry_steps: u8` and `last_seen_len: usize` tracking to FixWork.

Implementation passes all tests and has zero clippy warnings, but the optimization targets a pathology that doesn't occur in current benchmarks:

- **recursive_even** has high producer yield rate (~50% of steps produce answers), so the dry-step skip threshold of 3 rarely triggers
- **treecalc_synth_flip** has a single producer that is consistently productive
- The existing Or-rotation already provides fair scheduling

## Files changed

- `src/work/fix.rs` — Added DRY_STEP_SKIP_THRESHOLD, dry_steps/last_seen_len fields, skip logic in step_in_place

## Why It Failed

1. **Burst stepping is fundamentally incompatible with nested FixWork** due to recursive step_node nesting causing exponential stack growth.
2. **Current benchmarks don't have "stuck" producers** — all producers in the corpus are consistently productive.
3. **Or-rotation already provides fair scheduling** — producers get roughly equal CPU time through the existing interleaving mechanism.
4. **FastLock is zero-cost** (single-threaded) — reducing lock calls doesn't help.

## Remaining opportunities

- A benchmark with many tabled calls where some are dead-end producers would be needed to exercise this optimization
- The dry-step skip approach is sound and could be revisited if such workloads are added to the corpus
- Producer scheduling improvements require workloads with diverse producer productivity rates
