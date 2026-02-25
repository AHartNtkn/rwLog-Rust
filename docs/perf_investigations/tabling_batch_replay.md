# Investigation: Batch Consumer Answer Replay

## Summary

Added batch answer retrieval to FixWork to process multiple new answers per step instead of one at a time. DISCARD: U=8/100 (regression). Producers are stepped incrementally (one node step at a time), so multiple new answers per producer step is extremely rare. The extra lock acquisition + Vec allocation per step adds consistent overhead.

**Primary workload (recursive_even_backward_first64, 5 iters):**
**Baseline:** 10821 us (median, all values: 10923, 10811, 10852, 10765, 10802, 10739, 10848, 10574, 10547, 10668)
**After:** 10905 us (median, all values: 10905, 10879, 10899, 10999, 10880, 10907, 10858, 11034, 10975, 10925)
**Improvement:** -1.2% (regression)
**Mann-Whitney U:** 8/100 (significant regression)

## Problem

The hypothesis was that when multiple new answers accumulate in a table before a consumer gets scheduled, the consumer could batch-replay them in a single step to amortize per-replay overhead (lock acquisition, watermark comparison, continuation setup).

## Solution Attempted

1. Added `Table::answers_batch(start, max_count)` for single-lock batch retrieval of up to 16 answers
2. Added `FixStepResult::EmitBatch(Vec<NF>)` variant
3. After `step_table_producer`, batch-retrieve available answers instead of single `answer_at`
4. In `node.rs`, EmitBatch builds an Emit chain from batch answers

## Why It Failed

1. **Producers are stepped incrementally.** After a single `step_table_producer()` call, the producer almost always produces 0 or 1 new answers. Multiple new answers per producer step is extremely rare in the single-threaded model.

2. **Extra per-step overhead causes regression.** The additional `answers_batch()` call adds a FastLock acquisition + Vec allocation on every step, even when there are no new answers. This overhead is small but consistent across hundreds of thousands of calls.

3. **Per-answer overhead is dominated by downstream computation.** The cost of retrieving an answer (lock + array index) is tiny compared to the compose/meet operations that process it. Reducing retrieval cost has no meaningful impact.

4. **Two attempts both regressed.** Batching on both entry + post-producer paths: U≈2 (2% slower). Batching only post-producer: U≈8 (1-2% slower). The overhead cannot be avoided.

## Files changed

- `src/work/fix.rs` — Added batch answer retrieval and EmitBatch
- `src/node.rs` — Handle EmitBatch variant

## Remaining opportunities

- Tabling answer replay batching is a dead end — producers are one-step-at-a-time
- Tabling optimizations should focus on reducing the number of fixpoint iterations (algorithmic), not per-step overhead (mechanical)
- Producer prioritization (Tabling #8) addresses a different aspect — scheduling order, not per-step cost
