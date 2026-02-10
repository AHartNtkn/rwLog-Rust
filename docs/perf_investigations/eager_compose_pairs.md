# Investigation: Eager Compose Pair Processing

## Summary

Replaced cursor-based one-pair-per-step compose processing with eager batch processing. When a new NF arrives from either side, all compose pairs are processed immediately in a tight loop instead of being enqueued as cursor entries on a VecDeque for one-per-step draining. ~50% improvement on `recursive_even_backward_first64`, ~32% on `treecalc_first16`.

**Baseline:** 13909 us (median)
**After:** 6987 us (median)
**Improvement:** ~50% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001)
**Regression:** None — secondary improved 32% (U=84/100)

## Problem

ComposeWork used a cursor-based VecDeque (`pair_queue`) to enumerate compose pairs. When a new NF arrived from one side, a `ComposeCursor` was pushed onto the queue specifying a range of opposite-side indices to compose with. The `pre_step` method would pop one cursor, process one pair (calling `compose_nf`), and re-enqueue the cursor if more pairs remained.

This design was O(1) amortized per pair but required one `step_in_place` call per pair to drain the queue. For 64 answers with 378 compose attempts, the engine executed 4793 total steps — most of which were cursor-drain steps that popped a cursor, called compose_nf once, and re-enqueued.

## Solution

Replaced the cursor queue with eager composition in `on_new_left`/`on_new_right`. When a new NF arrives at index `i`, immediately iterate through all opposite-side NFs and call `compose_nf` for each, pushing results directly to pending:

```rust
fn on_new_left(&mut self, join: &mut DiagonalJoin<C, Self>, left_idx: usize, terms: &mut TermStore) {
    for right_idx in 0..join.seen_r_len() {
        if let Some(nf) = Self::compose_pair(join.seen_l_at(left_idx), join.seen_r_at(right_idx), terms) {
            join.push_pending(nf);
        }
    }
}
```

This eliminates:
- The `ComposeCursor` enum entirely
- The `pair_queue: VecDeque<ComposeCursor>` field
- The `pre_step` override (no longer needed)
- The `process_pair_queue` method
- Queue state tracking in `check_done`

Net code change: -96 lines.

### Key design decisions

1. **Eager over lazy**: Processing all pairs at arrival time rather than one-per-step eliminates the cursor queue overhead and reduces total engine steps from 4793 to 697 (85% reduction). The compose_nf calls themselves are the same — we're just batching them.

2. **Removed JoinOutcome::More**: With eager processing, there's never a state where both sides are exhausted but pairs remain in the queue. `check_done` only needs to return `Done`, simplifying the JoinOutcome enum.

3. **No pre_step override needed**: The default no-op `pre_step` suffices because all compose results are pushed to pending immediately in `on_new_left`/`on_new_right`, and the existing `pop_pending` at the top of `step_in_place` drains them.

## Files changed

- `src/work/compose.rs` — Replaced ComposeStrategy internals: removed ComposeCursor, pair_queue, pre_step, process_pair_queue. Added eager loops in on_new_left/on_new_right. Simplified check_done.
- `src/work/diagonal.rs` — Removed JoinOutcome::More variant, simplified match arms in step/step_in_place.

## Why 50% instead of 85%

The step reduction is 85% (4793 → 697), but wall-clock improvement is ~50% because:
1. The eliminated cursor-drain steps were cheap — they didn't call `step_node` on children, just popped a cursor and called `compose_nf` once
2. The remaining 697 steps include the expensive `step_node` calls that actually walk the search tree
3. Per-step cost is higher for the remaining steps (they do real work)

The 50% wall-clock improvement reflects that ~50% of total runtime was spent on engine dispatch overhead (step_node pattern matching, Node allocation/deallocation, flip/rotation) for cursor-drain steps that did minimal actual work.

## Remaining opportunities

- The same eager pattern could apply to MeetWork (uses the same DiagonalJoin with a different strategy). If meet_nf calls are similarly cursor-drained, the same optimization would help conjunction-heavy workloads.
- With 697 steps remaining, the per-step overhead is now a smaller fraction. Profile the new baseline to identify the next hotspot — likely FixWork stepping or the compose_nf calls themselves.
- The 378 compose_nf calls are unchanged — reducing failed compose attempts (e.g., via selectivity filtering) would provide additional gains orthogonal to this optimization.
