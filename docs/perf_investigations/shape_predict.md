# Investigation: Pre-seed ComposeWork with Leading Emit Chain NFs

## Summary

Pre-seeded ComposeWork with immediately available NFs from leading Emit chains at construction time. KEEP: ~43.3% improvement on treecalc_synth_flip (U=100/100, complete separation). Eliminates redundant step_node calls for already-materialized NFs, reducing engine steps by 21% and compose attempts by 47%.

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 210890 us (median, all values: 206988, 210445, 214510, 210655, 212943, 214611, 212913, 211125, 205805, 206949)
**After:** 119586 us (median, all values: 119420, 119029, 120844, 123018, 118111, 119752, 120715, 118311, 118705, 120143)
**Improvement:** 43.3%
**Mann-Whitney U:** 100/100 (complete separation, p < 0.0001)
**Regression:** None observed on recursive_even_backward_first64 (U=52) or graph_reach_64 (U=46)

## Problem

When ComposeWork is created with a left or right node that is a chain of Emit nodes (already-materialized NFs followed by more computation), the standard DiagonalJoin machinery steps through each Emit one at a time via step_node calls. This is particularly wasteful in the handle_call replay path where `node_from_answers(snapshot)` produces a chain of Emit nodes that are immediately available — each requires a full step_node round-trip just to extract the NF that's already sitting right there.

Engine steps: 4978, compose attempts: 277,985 on treecalc_synth_flip baseline.

## Solution

Added `ComposeWork::new_preseed` that absorbs leading Emit chains at construction time:

1. Walk leading Emit nodes on both left and right sides, collecting NFs into seen vectors
2. If one side is exhausted (Node::Fail) with zero NFs, immediately return a dead join
3. Eagerly compose all pre-seeded pairs using the existing root functor tag compatibility check
4. Initialize DiagonalJoin with pre-populated seen vectors via new `new_with_seen` constructor
5. Set flip flag so the join pulls from the un-pre-seeded side next

### Key design decisions

1. **Absorb at construction, not at step time** — avoids per-step overhead and gets all available NFs immediately
2. **Eager composition of pre-seeded pairs** — compose compatible pairs during construction rather than waiting for the DiagonalJoin stepping protocol
3. **Early dead-join detection** — if one side is Fail with no NFs, skip creating join machinery entirely
4. **Applied to both replay and general Call paths** — handle_call's replay path (node_from_answers) and general path both benefit

## Files changed

- `src/work/compose.rs` — Added `ComposeWork::new_preseed` method (+64 lines)
- `src/work/diagonal.rs` — Added `DiagonalJoin::new_with_seen` constructor (+31 lines)
- `src/work/mod.rs` — Updated `wrap_compose_with_prefix_suffix` to use `new_preseed` (+11/-2 lines)
- `src/work/pipe.rs` — Updated `handle_call` paths and `advance_call` to thread `terms` and use `new_preseed` (+7/-7 lines)

## Why 43% instead of more

The optimization eliminates redundant step_node calls for pre-available NFs but doesn't change the compose_nf kernel itself. Engine steps dropped 21% (4978→3908) and compose attempts dropped 47% (277,985→147,465). The remaining compose attempts are from NFs produced incrementally by stepping, which can't be pre-seeded. The constraint normalization cache still handles redundant CHR work.

## Remaining opportunities

- Apply the same pre-seeding pattern to MeetWork for And/Meet nodes with leading Emit chains
- Further reduce compose attempts by extending pre-seeding to deeper Emit chains (Emit inside Or branches)
- The 147K remaining compose attempts could potentially be further reduced by better scheduling
