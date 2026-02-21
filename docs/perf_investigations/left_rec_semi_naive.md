# Investigation: Semi-Naive and Table Skip for left_rec_32

## Summary

Attempted to reduce left_rec_32 overhead via semi-naive replay optimization and skipping FixWork for already-done tables. DISCARDED: U=70/100 (threshold 73), ~1.8% improvement. The bottleneck is Or-spine walking (155K walks), not tabling replay.

**Baseline:** 69,286 us (median, all values: 69576, 71634, 70730, 67546, 67020, 69428, 66333, 67031, 69145, 70471)
**After:** 68,074 us (median, all values: 67525, 68981, 70398, 68295, 67889, 66054, 68340, 65710, 65632, 68258)
**Improvement:** ~1.8% (not significant)
**Mann-Whitney U:** 70/100 (p > 0.05, not significant)
**Verdict:** DISCARD

## Problem

left_rec_32 takes ~72ms with:
- 75,212 steps
- 69,762 compose attempts (52% success rate)
- 154,818 Or-spine walks (avg 1.6 siblings, max 13)

The semi-naive optimization (replay watermarks) merged earlier didn't help left_rec_32. This investigation asked WHY and what would help.

## Key Findings

### Why semi-naive doesn't help left_rec_32

1. **CallKey exact matching prevents replay optimization.** Semi-naive's `ReplayOnly` mode triggers when `replay_key == key` (exact match). Inner recursive calls in left_rec_32 have DIFFERENT right boundaries (b_N → b_(N+1)), creating different CallKeys each time. ReplayOnly never matches.

2. **Watermark is always 0 for inner tables.** The outer table does only 1 productive fixpoint iteration (producing all 33 answers). Each of the ~528 inner tables also iterates only once, so the watermark stays at 0. Even if matching was relaxed, watermark-based delta filtering would not reduce work.

3. **Table cascade is semantically necessary.** Each of 32 branches creates inner tables with unique right boundaries. Sharing answers across different boundaries produces WRONG results (verified: an attempt to share gave 1 answer instead of 33). Different boundaries mean different input domains — the cascade is required for correctness.

### The real bottleneck: Or-spine walking

154,818 Or-spine walks for 33 answers = ~4,700 walks per answer. The 33-branch Or tree requires O(depth) walk per step. Each inner table evaluates the full 33-branch body, multiplied across 528 tables. This is structural overhead from the interleaving search strategy applied to a deeply nested Or tree.

## Approaches Attempted

1. **Skip FixWork for done tables** — Skip creating FixWork when a table is already complete. U=70/100, ~1.8% — just under threshold.
2. **Relax CallKey matching for semi-naive** — Allow replay across similar-but-not-identical keys. Produces wrong results (different boundaries = different semantics).
3. **Watermark-based delta filtering** — Watermarks are always 0 since each table iterates only once.
4. **Table answer sharing** — Share answers across tables with different boundaries. Incorrect: 1 answer instead of 33.
5. **Dead code removal in semi-naive block** — Removed unreachable related-call logic.

## Files Changed (not merged)

- `src/work/pipe.rs` — Skip FixWork for done tables, dead code removal

## What Would Actually Help

- **Flat Or representation**: Replace binary Or tree with `Vec<Node>` to eliminate O(depth) spine walking. Prior investigation (flatten_or_spine) DISCARDED due to O(n) remove(0) with Vec and ring buffer overhead with VecDeque. A cursor/index-based approach might work.
- **Compiled dispatch for left_rec**: The root-functor dispatch (compiled_dispatch) already merged might help if the Or branches have distinct root functors. Worth checking.
- **Algebraic branch pruning**: Recognize at the relation level that most of the 33 branches will fail for a given boundary and prune before evaluation.
- **Subsumption-based tabling**: Tables with strictly weaker constraints reuse answers from tables with stronger constraints, reducing the 528 inner tables.
