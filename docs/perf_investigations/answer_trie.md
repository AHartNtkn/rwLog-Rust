# Investigation: Answer Trie — Double-Arc Elimination in Table Answers

## Summary

Investigated MP7 answer trie for dedup, pivoted to removing redundant Arc wrapping in table answers. KEEP: 1.7-2.9% improvement on tabling workloads (U=98 graph_reach_64, U=95 recursive_even), no regressions.

**Primary workload (graph_reach_64):**
**Baseline:** 6536.1 us (median, all values: 6701.2, 6504.3, 6617.5, 6388.3, 6429.2, 6643.0, 6567.9, 6538.0, 6534.3, 6495.1)
**After:** 6363.3 us (median, all values: 6404.3, 6342.2, 6254.3, 6383.5, 6384.4, 6346.0, 6380.6, 6197.1, 6474.1, 6335.2)
**Improvement:** ~2.6% (same-session comparison)
**Mann-Whitney U:** 98/100 (p < 0.001)

**Secondary workload (recursive_even_backward_first64):**
**Baseline median:** 10786.2 us
**After median:** 10601.2 us
**U:** 95/100 (~1.7% improvement)
**Regression:** None observed (treecalc_synth_flip U=54)

## Problem

Table answers were stored as `Vec<Arc<NF<C>>>` with dedup set `FxHashSet<Arc<NF<C>>>`. Since NF is already internally `Arc<NfInner<C>>` (O(1) clone, pointer-based hash/eq), wrapping in another Arc added unnecessary overhead:
- Extra atomic refcount operations per answer store/retrieve
- Arc::unwrap_or_clone on retrieval (unnecessary allocation check)
- Double indirection for hash/eq operations

## Solution

Removed the outer Arc wrapper. Changed `TableAnswers` from `Vec<Arc<NF<C>>>` + `FxHashSet<Arc<NF<C>>>` to `Vec<NF<C>>` + `FxHashSet<NF<C>>`. Updated `add_answer`, `answer_at`, `all_answers`, `answers_from` to work with `NF<C>` directly. Removed `Arc::unwrap_or_clone` from `step_in_place`.

### Key design decisions

1. **NF is already Arc-wrapped internally** — NF contains `Arc<NfInner<C>>`, making NF::clone() an O(1) atomic refcount bump. The outer Arc was pure waste.
2. **No answer trie needed** — The original investigation target (trie-based dedup) was unnecessary because NF already has O(1) cached hash, making FxHashSet dedup already efficient. The worker correctly identified the real opportunity.

## Files Changed

- `src/work/fix.rs` — Changed TableAnswers from Vec<Arc<NF>> to Vec<NF>, updated add_answer/answer_at/all_answers/answers_from
- `src/work/mod.rs` — Updated node_from_answers to take Vec<NF<C>>, removed Arc::unwrap_or_clone
- `src/work/tests.rs` — Updated test assertions from .as_deref() to .as_ref()

## Why 1.7-2.9% Instead of More

The double-Arc overhead is small per-operation (one extra atomic increment/decrement). The improvement is modest because:
- Table answer operations are a small fraction of total tabling work
- The main cost in tabling is compose_nf during replay, not answer storage
- NF's cached hash means dedup was already efficient regardless of wrapping

## Remaining Opportunities

- **Answer tries for structural indexing** — not needed for dedup (hash is fine) but could enable prefix-based filtering for subsumption checks
- **SCC-based scheduling** — standard improvement for mutually recursive groups, remains uninvestigated
