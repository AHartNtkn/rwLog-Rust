# Investigation: Semi-Naive Fixpoint Evaluation (Major Proposal 7)

## Summary

Added semi-naive fixpoint evaluation to tabling via replay watermarks. Consumers in subsequent fixpoint iterations only replay NEW (delta) answers instead of all accumulated answers. graph_reach_64 improved 96.6% (30x), compose attempts dropped from 5.38M to 131K.

**Baseline:** 190,395 us (median, all values: 190193, 190585, 192452, 189483, 190293, 190921, 187997, 192126, 186119, 183784)
**After:** 6,391 us (median, all values: 6353, 6379, 6351, 6430, 8591, 6456, 6382, 6593, 6421, 6304)
**Improvement:** ~96.6% (30x speedup)
**Mann-Whitney U:** 100/100 (p < 0.0001, complete separation)
**Regression:** None observed on treecalc_synth_flip (U=46) or recursive_even_backward_first64 (U~50)

## Problem

graph_reach_64 (transitive closure over 64-node linear chain) performed 5,384,994 compose attempts with only 2% success rate. The root cause: each fixpoint iteration replayed ALL accumulated answers against ALL consumers, causing O(n²) pairs per iteration. For k accumulated answers at iteration i, the system tried k×k pairs — most of which were already attempted in iteration i-1.

This is the classic problem that semi-naive evaluation solves in Datalog and logic programming systems.

## Solution

Added a `replay_watermark` to `TableProducer` in `src/work/fix.rs`. When a fixpoint verification cycle begins, the watermark records how many answers existed at the start. When consumers are created for the next iteration via `make_replay_producer`, they receive this watermark and only replay answers with index >= watermark (the delta set).

### Key design decisions

1. **Replay watermark in CallMode::ReplayOnly**: Extended `CallMode::ReplayOnly` to carry a `usize` watermark alongside the `Arc<CallKey<C>>`. The PipeWork replay path uses `answers_from(watermark)` instead of `all_answers()`.

2. **Table::answers_from(start)**: New method on Table that returns answers starting from index `start`, providing the delta set. Falls back to all_answers() when start=0 (first iteration).

3. **Watermark tracking in step_table_producer**: When advancing the fixpoint, record the current answer count as the watermark before starting the verification/replay cycle.

4. **Minimal file changes**: Only 3 files modified (fix.rs, mod.rs, pipe.rs). The change is surgical — it doesn't restructure the tabling architecture, just adds delta tracking to the existing replay mechanism.

## Files changed

- `src/work/fix.rs` — Added `replay_watermark` to TableProducer, `answers_from()` to Table, watermark tracking in step_table_producer, watermark parameter to make_replay_producer
- `src/work/mod.rs` — Extended `CallMode::ReplayOnly` with watermark field
- `src/work/pipe.rs` — Changed `all_answers()` to `answers_from(watermark)` in ReplayOnly branch

## Why 96.6% instead of higher

- The 6.4ms remaining is the actual compose work for ~131K necessary pairs (edges × reachable nodes)
- Parsing the 63-edge program and initial setup has fixed overhead
- The theoretical minimum for 64-node transitive closure is O(n²) = ~4096 compose successes; with O(n) edges × O(n) answers per iteration, ~131K attempts is close to optimal

## Additional observations

- **left_rec_32**: Neutral (69.6ms vs 68.1ms). Its recursion pattern (Atom;Call;Atom within Or branches) doesn't generate the same redundant replay pattern because each iteration produces answers through a different mechanism than graph_reach_64's simple transitive closure.
- **recursive_even_backward_first64**: Neutral. The even/odd mutual recursion has few fixpoint iterations with small delta sets, so semi-naive doesn't change the overall work significantly.

## Remaining opportunities (Major Proposal 7)

- **Answer tries**: Replace flat answer vectors with trie-indexed structures for O(1) duplicate detection instead of linear scan
- **SCC-based scheduling**: Group mutually recursive relations into strongly connected components and schedule fixpoint evaluation per-SCC
- **Semi-naive for meet/conjunction**: The same delta-tracking principle could apply to DiagonalJoin — only compose new NFs against existing ones, not all×all
- **Subsumption tabling**: Reuse answers from more-general calls when safe, reducing total tabling work
