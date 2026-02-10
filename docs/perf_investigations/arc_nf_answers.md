# Investigation: Arc-wrap NFs in Table Answers

## Summary

Wrapped NF values in `Arc` inside Table answer storage to eliminate expensive deep clones on every `answer_at()` call and in dedup operations. ~4.6% improvement on `recursive_even_backward_first64`.

**Baseline:** 21.19ms (median, all values: 20.51, 20.89, 21.20, 21.23, 21.17, 20.90, 21.28, 21.17, 26.39, 22.46)
**After:** 20.22ms (median, all values: 19.53, 20.21, 20.11, 20.23, 19.71, 20.56, 20.19, 20.48, 25.17, 22.34)
**Improvement:** ~4.6% (same-session comparison)
**Mann-Whitney U:** 82/100 (p < 0.01)
**Regression:** None observed on treecalc_first16 (U=37.5/100, not significant; high variance due to very fast benchmark ~1-2ms)

## Problem

From profiling of `recursive_even_backward_first64`:
- `Table::answer_at` = 3.83% of total time — acquires FastLock and deeply clones an NF
- `ChrState::clone` = 2.81% self-time
- `ChrStore::clone` = 4.33% self-time (involves cloning Vec<CInstance>, Vec<PredStore>, HashMaps)
- Combined: ~11% of execution in NF clone/drop from the Table answer path

`Table::answer_at` was:
```rust
pub fn answer_at(&self, index: usize) -> Option<NF<C>> {
    self.answers.lock().answers.get(index).cloned()
}
```

Every consumer (FixWork::step_in_place) called this on every step, deeply cloning the NF including ChrState → ChrStateData → ChrStore → Vec<CInstance> + Vec<PredStore> + HashMaps. These cloned NFs were used ephemerally (composed or met then discarded).

## Solution

Changed `TableAnswers` to store `Vec<Arc<NF<C>>>` instead of `Vec<NF<C>>`:

1. **`add_answer`**: Wraps the incoming NF in Arc before storing. Dedup set uses `Arc<NF<C>>` — cloning for the dedup insert is O(1) atomic increment.
2. **`answer_at`**: Returns `Arc<NF<C>>` — O(1) Arc clone instead of deep clone. Consumer unwraps with `Arc::unwrap_or_clone`.
3. **`all_answers`**: Returns `Vec<Arc<NF<C>>>` — each element is O(1) Arc clone.
4. **`node_from_answers`**: Accepts `Vec<Arc<NF<C>>>` and uses `Arc::unwrap_or_clone` to convert to owned NFs.

### Key design decisions

1. **Arc only in Table storage, not throughout the pipeline**: Only the Table answer list and related APIs use Arc. compose_nf/meet_nf continue to take NF<C> by value. This minimizes the blast radius while capturing the main benefit.

2. **`Arc::unwrap_or_clone` at consumption points**: When an NF is needed by value (for compose/meet), the Arc is unwrapped. Since the Table retains its reference (refcount=2), this still clones — but the clone happens outside the lock, reducing lock contention.

3. **Dedup set uses `Arc<NF<C>>`**: The dedup HashSet stores Arc clones (O(1)) instead of deep clones. This eliminates the most wasteful clone path (every answer was cloned for dedup insertion).

## Files changed

- `src/work/fix.rs` — Changed TableAnswers to store `Vec<Arc<NF<C>>>` and `FxHashSet<Arc<NF<C>>>`. Updated add_answer, answer_at, all_answers.
- `src/work/mod.rs` — Changed `node_from_answers` to accept `Vec<Arc<NF<C>>>` and use Arc::unwrap_or_clone.
- `src/work/pipe.rs` — Updated call sites of all_answers and node_from_answers.
- `src/work/tests.rs` — Updated test assertions for answer_at to use .as_deref() comparison.

## Why 4.6% instead of 8-12%

The estimated 8-12% assumed eliminating most clone overhead from the answer path. The actual 4.6% is lower because:

1. **answer_at still clones at unwrap time**: refcount is 2 (Table retains its copy), so `Arc::unwrap_or_clone` always clones. The savings come from moving the clone outside the lock and making dedup inserts O(1).
2. **The main win is in dedup and all_answers**: These paths genuinely avoid deep clones.
3. **To capture the full 8-12%**: Arc<NF<C>> would need to propagate further through the pipeline (NodeStep, DiagonalJoin emit paths, compose/meet argument passing). This is a much more invasive change.

## Remaining opportunities

- Propagate `Arc<NF<C>>` through NodeStep::Emit and DiagonalJoin seen_l/seen_r to avoid unwrapping Arcs that are immediately re-cloned for dedup.
- Use `Arc::try_unwrap` in FixWork::step_in_place when the consumer is the only reference (rare but possible when Table is done).
- Consider making compose_nf/meet_nf accept `&NF<C>` where possible to avoid the unwrap clone entirely.
