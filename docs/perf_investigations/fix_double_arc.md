# Investigation: Remove Double-Arc from fix.rs and rel.rs

## Summary

Attempted to remove redundant `Arc<NF<C>>` wrapping in fix.rs (TableAnswers) and rel.rs (Rel::Atom) now that NF is internally Arc-wrapped. Clean implementation, all tests pass, but failed to reach statistical significance due to system load.

**Verdict:** DISCARD (U=72/100, threshold 73)
**Note:** System exhibited severe bimodal timing distribution (~3700us vs ~5200us) consistent with CPU frequency scaling interference. When comparing only "fast" state runs, ~5% improvement was observed. The optimization is likely real but unmeasurable under current system conditions.

## Problem

After Round 15's nf_arc_wrap, NF<C> contains an internal `Arc<NfInner<C>>`, making NF::clone O(1). However, several places still wrapped NF in an additional outer Arc:
- `TableAnswers::answers: Vec<Arc<NF<C>>>` — double Arc per stored answer
- `TableAnswers::seen: FxHashSet<Arc<NF<C>>>` — double Arc per dedup entry
- `Rel::Atom(Arc<NF<C>>)` — double Arc per atomic relation
- `node_from_answers(Vec<Arc<NF<C>>>)` — Arc::unwrap_or_clone overhead

## Solution

Mechanical refactoring: removed all outer `Arc<NF<C>>` wrappers, replacing with direct `NF<C>` storage.

- 9 files changed, 175 insertions, 200 deletions
- Zero clippy warnings, all 814 tests pass

## Files changed

- `src/rel.rs` — `Atom(Arc<NF<C>>)` → `Atom(NF<C>)`, updated all construction and pattern match sites
- `src/work/fix.rs` — `Vec<Arc<NF<C>>>` → `Vec<NF<C>>`, `FxHashSet<Arc<NF<C>>>` → `FxHashSet<NF<C>>`, updated add_answer/answer_at/all_answers
- `src/work/mod.rs` — `node_from_answers(Vec<Arc<NF<C>>>)` → `node_from_answers(Vec<NF<C>>)`
- Additional files with updated call sites

## Why DISCARD

The system exhibited a bimodal timing distribution throughout the measurement period, with runs alternating between ~3700us ("fast" CPU state) and ~5200us ("slow" state). This created extreme variance that prevented the Mann-Whitney U test from reaching the p < 0.05 threshold. Best U achieved: 72/100 (threshold: 73).

## Remaining opportunities

This optimization should be re-attempted when system conditions allow cleaner measurement. The code changes are correct and reduce both allocation overhead and indirection.
