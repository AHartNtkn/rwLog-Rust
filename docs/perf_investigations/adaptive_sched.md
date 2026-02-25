# Investigation: Adaptive Search Scheduling for Or-Spine Walks (Major Proposal 5)

## Summary

Tested three approaches to reduce Or-spine waste in step_or. The only approach with a measurable signal (aggressive batch stepping, 30% on left_rec_32) caused catastrophic regression on treecalc_synth_flip (hung 20+ minutes). The two semantics-preserving approaches showed zero improvement. Or-spine walks are confirmed NOT the bottleneck. DISCARDED.

**Verdict:** DISCARD (three approaches attempted, none viable)

## Problem

left_rec_32 has 155K Or-spine walks with avg_siblings=1.6, max_siblings=13. The hypothesis was that smarter scheduling or batching could reduce wasted work from stepping one branch at a time.

## Approaches Tested

### Approach 1: Aggressive Batch Stepping (step all siblings per Or visit)

When a leaf returns Continue, push to "stepped" list, pop next sibling, step it too. Repeat for all siblings with budget = siblings.len().

**left_rec_32:** 30% improvement (71ms → 50ms), U=100/100.

**treecalc_synth_flip:** CATASTROPHIC REGRESSION — baseline ~420s, optimized ran 20+ minutes before kill. Batch stepping changes interleaving order: each branch gets stepped once per Or visit instead of alternating. This delays pruning from Emit answers. For treecalc (where pruning from earlier answers is critical), this causes exponential search space blowup.

**Root cause:** Batch stepping violates rotation-based fairness. In the original, `Or(A,B)` → step A → `Or(B, A')` guarantees B is stepped next. With batch stepping, both A and B are stepped before results propagate, which delays CHR constraint pruning.

### Approach 2: Exhaustion-Only Batching (skip dead branches without rebuilding)

When a stepped branch returns Exhausted, immediately try next sibling instead of rebuilding chain and re-entering step_or.

**left_rec_32:** No improvement — timings identical to baseline.

**Reason:** Exhausted branches already get pruned during the left-spine walk (the `Node::Fail` case in the walk loop). The extra rebuilding and re-walking cost is negligible.

### Approach 3: SmallVec<[Node; 16]> for Siblings

Replace `Vec<Node>` with `SmallVec<[Node; 16]>` to avoid heap allocation for sibling lists. left_rec_32 max siblings = 13, fits inline.

**left_rec_32:** No improvement — timings identical to baseline.

**Reason:** Heap allocation cost per Vec is tiny compared to step_node computation and compose_nf costs that dominate.

## Raw Timings (Approach 1 — the only one with a signal)

**left_rec_32 (N=10):**

| Round | Baseline (us) | Optimized (us) |
|-------|--------------|----------------|
| 1 | 70,312 | 49,704 |
| 2 | 71,499 | 50,392 |
| 3 | 70,332 | 49,369 |
| 4 | 71,346 | 49,742 |
| 5 | 71,036 | 49,664 |
| 6 | 70,689 | 49,878 |
| 7 | 71,074 | 50,033 |
| 8 | 72,324 | 49,734 |
| 9 | 69,065 | 49,994 |
| 10 | 68,967 | 47,533 |

Baseline median: 71,055 us | Optimized median: 49,741 us | U=100/100

(Not measured on treecalc/secondary due to the hang.)

## Key Insights

1. **Or-spine walks are NOT the bottleneck for left_rec_32.** Despite 155K walks with up to 13 siblings, the walk cost is small compared to 70K compose_nf attempts and 36K compose successes. The compose operations dominate.

2. **Batch stepping helps left_rec_32 but is semantically dangerous.** The 30% improvement comes from reducing total engine steps (each step does more work), but the changed interleaving order causes exponential blowup on workloads where pruning depends on order (like treecalc).

3. **treecalc has only 1547 Or walks with max 5 siblings** — a completely different profile than left_rec_32. Any optimization that helps left_rec_32's Or scheduling is irrelevant to treecalc.

4. **Exhaustion tracking (Option A from the brief) is already implemented** in the original code. The left-spine walk prunes `Node::Fail` (exhausted branches become Fail via step_node's Work::Done → Continue(Fail) path).

5. **A principled batch-stepping approach that preserves interleaving semantics would require a fundamentally different search strategy** — something like "step branch, if it produces Continue and no structural change, try next" — but this is a heuristic that violates CLAUDE.md principles.

## Consistency with Prior Work

This confirms the or_index_step investigation's finding: Or-spine optimizations are not productive for left_rec_32. The real bottleneck is compose_nf (70K attempts, 34K failures). Three distinct approaches to Or optimization have now been discarded:
- Flat Vec with index-based stepping (28% regression)
- VecDeque/Vec flattening (0.8-1.6% regression)
- Adaptive scheduling (semantically incompatible)

## Files Changed (not merged)

- `src/node.rs` — Modified step_or function (three variants tested)
