# Investigation: Selective dirty enqueue in normalize_owned

## Summary

Attempted to track which specific CHR constraint instances had their arguments changed by substitution application, and only re-enqueue those dirty instances instead of all alive constraints. The optimization target never fires on treecalc_synth_flip — all `watermark==0` entries have zero alive constraints.

**Baseline:** 1482343us (median, all values: 1465662, 1481183, 1491257, 1492626, 1483504, 1466788, 1493920, 1526799, 1473581, 1475894)
**After:** 1508211us (median, all values: 1513733, 1471496, 1502689, 1542495, 1490591, 1517763, 1501850, 1533693, 1481073, 1553498)
**Improvement:** -1.75% (regression)
**Mann-Whitney U:** 22/100 (significant regression)
**Regression:** N/A

## Problem

`normalize_owned` with `watermark=0` calls `enqueue_all_alive_in`, which enqueues ALL alive constraints for fixpoint re-processing. The hypothesis was that when `apply_subst_to_data` changes only some constraint args, we could track which instances were dirtied and only re-enqueue those, avoiding O(N) work over unchanged constraints.

Profiling showed `normalize_owned` at 15.66% self-time, suggesting significant overhead in constraint processing.

## Solution Attempted

Added `dirty_cids: Option<SmallVec<[Cid; 8]>>` field to `ChrStateData`. Modified `apply_subst_to_data`, `remap_vars`, and `remap_and_apply_subst` to record which specific `Cid`s had their arguments changed. In `normalize_owned`, when `dirty_cids` is set and non-empty, only enqueue those specific instances instead of all alive constraints.

## Why it failed

**Critical finding through instrumentation:** The optimization target **never fires** on treecalc_synth_flip.

1. **Every `watermark==0` entry in `normalize_owned` has `alive_count=0`.** The watermark=0 path only fires when the constraint store is empty (initial normalization of a freshly-created ChrState). There are zero constraints to selectively enqueue.

2. **The `args_changed` branch (after `apply_subst_to_data`) never fires.** For treecalc_synth_flip, substitutions produced by `solve_to_fixpoint` never change constraint args. The code path that sets `watermark=0` with dirty constraints is dead for this workload.

3. **The incremental path (`watermark != 0`) is also trivial** — it fired exactly once with zero alive constraints.

4. **Root cause:** The treecalc_synth_flip workload's CHR constraints are consumed immediately by simplification rules during `solve_to_fixpoint`. By the time `normalize_owned` returns, the store is at fixpoint with all constraints either dead or stable. The "15.66% self-time in normalize_owned" is dominated by `rebuild_indexes`, `solve_to_fixpoint` itself, and Arc CoW overhead — not by re-processing unchanged constraints.

5. **V1 regression mechanism:** The `dirty_cids` tracking added per-instance overhead in `apply_subst_to_data`/`remap_vars`/`remap_and_apply_subst` (SmallVec allocation + push per changed instance), increased `ChrStateData` struct size affecting all clone/Arc CoW operations, and additional branching in `normalize_owned`.

## Files changed

- `src/chr/mod.rs` — Added `dirty_cids` tracking to ChrStateData, modified apply_subst_to_data/remap_vars/remap_and_apply_subst to populate it, modified normalize_owned to use selective enqueue. All changes reverted after instrumentation showed zero opportunity.

## Remaining opportunities

- The selective dirty enqueue optimization could benefit workloads where CHR constraints persist across multiple normalize calls and where substitutions frequently change constraint args. Would need a different primary benchmark to test this.
- The 15.66% normalize_owned self-time on treecalc_synth_flip is dominated by rebuild_indexes and solve_to_fixpoint — optimizing those directly would be more impactful.
