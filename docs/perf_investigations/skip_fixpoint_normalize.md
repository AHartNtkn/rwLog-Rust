# Investigation: Skip normalize_owned when already at fixpoint

## Summary

Attempted to short-circuit `normalize_owned` when `fixpoint_watermark >= next_cid` (all constraints already at fixpoint), avoiding the Arc::make_mut + rebuild_indexes + solve_to_fixpoint cycle. No significant improvement.

**Baseline:** 1337387us (median, all values: 1334574, 1311879, 1294148, 1340199, 1342196, 1308377, 1317026, 1345577, 1351599, 1341515)
**After:** 1332705us (median, all values: 1304001, 1314096, 1331944, 1335990, 1295835, 1329654, 1333465, 1338187, 1339093, 1334208)
**Improvement:** 0.35% (not significant)
**Mann-Whitney U:** 64/100 (not significant)
**Regression:** N/A

## Problem

`normalize_owned` is 17% of total runtime (~2,787 calls on treecalc_synth_flip). The hypothesis was that many calls have `fixpoint_watermark >= next_cid` (already at fixpoint), and by checking this BEFORE calling `Arc::make_mut` (which may clone ChrStateData), we could skip the entire clone+rebuild+solve cycle.

## Solution Attempted

Added early return in `normalize_owned` when `fixpoint_watermark >= next_cid`, checked via the existing Arc reference without triggering Arc::make_mut.

## Why it failed

1. **Arc::make_mut is cheap when refcount=1**: In most cases on this workload, the Arc has a single owner, so `make_mut` doesn't actually clone — it just returns a mutable reference. The "expensive clone" we aimed to avoid rarely happens.

2. **Empty-agenda solve_to_fixpoint is nearly free**: When the store is at fixpoint, `enqueue_above_watermark` produces an empty agenda, and `solve_to_fixpoint` immediately returns `true` after finding no agenda items.

3. **The watermark=0 path with alive_count=0 is already fast**: `rebuild_indexes` creates PredStore objects but iterates zero instances. The cost is just creating PredStore objects per predicate (1 predicate in treecalc_synth_flip), which is cheap.

4. **The real cost is in actual constraint solving**: The 17% normalize_owned hotspot is dominated by cases where there IS work to do — actual rule matching, firing, and constraint creation inside `solve_to_fixpoint`.

## Files changed

- `src/chr/mod.rs` — Added early return in `normalize_owned` when `fixpoint_watermark >= next_cid` (reverted, DISCARD)

## Remaining opportunities

- Reduce the frequency of `normalize_owned` calls at the call site level when nothing has changed.
- Optimize the actual `solve_to_fixpoint` matching loop (better indexing, cheaper match operations).
- The normalize_owned cost that matters is the actual rule matching/firing — architectural changes to reduce the number of rules tested or match attempts would be more impactful.
