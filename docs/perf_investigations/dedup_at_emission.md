# Investigation: Move Answer Dedup Closer to Emission Point

## Summary

Investigated whether answer deduplication could be moved closer to the branch emission point to catch duplicates earlier. DISCARD: instrumentation shows only 0.8% duplication rate across key workloads — the existing table-level dedup is already near-optimal.

**No performance measurement needed** — the opportunity is below threshold.

## Problem

The hypothesis was that Or branches within FixWork produce significant duplicate answers that travel through the full pipeline before being rejected at the table-level FxHashSet. Moving dedup earlier (e.g., per-branch dedup filters) could avoid wasted compose/normalize work on duplicates.

## Why It Failed

1. **Only 0.8% duplication across all workloads.** Instrumentation across three key workloads showed:
   - recursive_even_backward_first64: 4096 add_answer calls, 0 duplicates (0.0%)
   - treecalc_synth_flip: 1290 add_answer calls, 10 duplicates (0.8%)
   - left_rec_32: 35 add_answer calls, 34 duplicates (97.1%) — but negligible volume (35 total calls)
   - Grand total: 5421 calls, 44 duplicates (0.8%)

2. **Existing dedup is already O(1).** Table::add_answer uses FxHashSet::insert with NF's pre-computed cached_hash. Each duplicate costs ~15ns (FastLock + hash probe + Arc clone). Total savings from eliminating all 44 duplicates: ~660ns.

3. **Semi-naive watermarks prevent most duplicates at the source.** Replay watermarks ensure consumers only see delta answers, preventing the same answer from being re-produced across fixpoint iterations.

4. **No downstream work is wasted.** add_answer returns false for duplicates, and the caller ignores the return value — no consumer replay or pipeline processing happens for duplicates.

## Files changed

None — instrumentation only, no code changes merged.

## Remaining opportunities

- Table-level answer dedup is effectively solved — 0.8% duplication with O(1) rejection
- The left_rec_32 case has high duplication rate (97%) but only 35 total calls, making optimization irrelevant
- Dedup optimization should focus on other subsystems (e.g., compose pair dedup is also only 0.02% — see compose_memo investigation)
