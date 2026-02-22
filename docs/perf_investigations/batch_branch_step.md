# Investigation: Batch Or-Branch Stepping

## Summary

Modified step_or to batch-step the leftmost Or-branch K times before rotating. DISCARD: 4.1x regression at K=2, stack overflow at K=4. Delaying rotation by even one extra step delays CHR pruning signals from sibling branches, causing exponential compose pair explosion. Same fundamental failure mode as adaptive_sched.

**No Mann-Whitney U measurement needed** — catastrophic regression (4.1x slower) is unambiguous.

**Baseline:** ~205 ms (treecalc_synth_flip)
**After (K=2):** ~849 ms (4.1x slower)
**Engine steps:** 4978 → 7576 (+52%)
**Compose attempts:** 277,985 → 888,364 (+3.2x)

## Problem

The hypothesis was that per-rotation overhead (Or spine walks, chain rebuilding, dispatch) could be amortized by doing K steps on the same branch before rotating. This preserves rotation order but does more work per turn.

## Solution Attempted

Modified `step_or` in `src/node.rs` to batch-step the leftmost branch up to K times before rebuilding the Or chain with siblings. Batching stops early on Emit, Exhausted, or when the branch splits into a new Or node.

## Why It Failed

1. **Rotation serves as the fairness mechanism for CHR pruning.** In treecalc_synth_flip, timely cross-branch pruning is critical. Delaying rotation by even one step delays pruning signals from sibling branches, causing exponential blowup in compose pairs.

2. **Same fundamental failure as adaptive_sched (Major Proposal 5).** That investigation also delayed rotation (via aggressive batch budgets) and caused exponential blowup on treecalc_synth_flip. This confirms it's a structural property, not an implementation detail.

3. **Or spine walks confirmed NOT the bottleneck.** Batching reduced or_spine_walks from 1547 to 1112 (-28%), confirming the mechanism works, but the regression from delayed pruning vastly outweighs any overhead savings.

4. **Stack overflow at K=4.** Increased stack frame depth from the batching loop within the recursive step_node → step_or → step_node chain caused stack overflow in debug builds.

## Files changed

- `src/node.rs` — Modified step_or for batch stepping

## Remaining opportunities

- Batch branch stepping is a dead end — rotation frequency is load-bearing for CHR pruning
- Any optimization that changes Or-rotation frequency is fundamentally incompatible with the current architecture
- The remaining Or optimization targets should focus on reducing per-rotation COST (faster spine walks, cheaper chain rebuilding), not rotation FREQUENCY
- All 5 Disjunction backlog items are now exhausted
