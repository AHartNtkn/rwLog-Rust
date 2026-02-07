# Investigation: compose_nf / meet_nf Memoization

**Status:** Completed — not worth pursuing
**Backlog item:** NF/Kernel Normalization Pipeline; Prioritization Candidate #1
**Branch:** `fast-flip`

## Hypothesis

Memoizing `compose_nf` and `meet_nf` by canonical hashing of their `(NF, NF)` input pairs could eliminate redundant kernel work. If the same compositions/meets are computed repeatedly, caching results would trade memory for CPU.

## Method

Added pair-hash tracking to `perf_counters` (behind the `enabled()` gate, zero overhead when disabled). Each call to `compose_nf`/`meet_nf` hashes its `(a, b)` input pair using `FxHasher` and inserts into a `HashSet<u64>`. This is semantically correct because the `TermStore` is hash-consed: structurally equal terms always receive the same `TermId`, so NF hashing based on TermIds is a semantic hash within a single evaluation.

Ran all 21 corpus cases (quick + stress tiers) and compared total calls vs unique input pairs.

## Results

### Per-case breakdown

| Case | Steps | Compose | Unique | Dup% | Meet | Unique | Dup% |
|------|------:|--------:|-------:|-----:|-----:|-------:|-----:|
| identity_atom | 12 | 2 | 1 | 50.0% | 0 | 0 | — |
| sequence_chain_len12 | 111 | 13 | 12 | 7.7% | 0 | 0 | — |
| sequence_chain_len64 | 579 | 65 | 64 | 1.5% | 0 | 0 | — |
| disjunction_wide_16 | 117 | 32 | 16 | 50.0% | 0 | 0 | — |
| disjunction_wide_64_first16 | 67 | 16 | 16 | 0.0% | 0 | 0 | — |
| disjunction_wide_256_first64 | 259 | 64 | 64 | 0.0% | 0 | 0 | — |
| conjunction_selective | 32 | 6 | 5 | 16.7% | 6 | 6 | 0.0% |
| conjunction_cross_16x16 | 154 | 33 | 32 | 3.0% | 256 | 256 | 0.0% |
| deep_term_depth_32 | 12 | 2 | 1 | 50.0% | 0 | 0 | — |
| deep_term_depth_128 | 12 | 2 | 1 | 50.0% | 0 | 0 | — |
| recursive_add_forward_n8 | 160 | 52 | 26 | 50.0% | 0 | 0 | — |
| recursive_add_backward_n8 | 268 | 68 | 34 | 50.0% | 0 | 0 | — |
| recursive_add_forward_n24 | 448 | 148 | 74 | 50.0% | 0 | 0 | — |
| recursive_add_backward_n24 | 1348 | 196 | 98 | 50.0% | 0 | 0 | — |
| recursive_even_backward_first10 | 203 | 54 | 54 | 0.0% | 0 | 0 | — |
| recursive_even_backward_first64 | 4793 | 378 | 378 | 0.0% | 0 | 0 | — |
| constraints_nonzero_success | 12 | 2 | 1 | 50.0% | 0 | 0 | — |
| constraints_nonzero_deep_success | 12 | 2 | 1 | 50.0% | 0 | 0 | — |
| constraints_range_between | 12 | 2 | 1 | 50.0% | 0 | 0 | — |
| treecalc_first_answer | 18 | 5 | 5 | 0.0% | 0 | 0 | — |
| treecalc_first16 | 331 | 81 | 81 | 0.0% | 7 | 5 | 28.6% |
| **TOTAL** | **8960** | **1223** | **965** | **21.1%** | **269** | **267** | **0.7%** |

### Aggregate metrics

| Metric | Value |
|--------|-------|
| Compose calls as % of engine steps | 13.6% |
| Compose duplication rate | 21.1% |
| Compose calls saveable by cache | 258 (2.9% of total steps) |
| Meet duplication rate | 0.7% |

### Frequency distribution

Every duplicate compose pair is called **exactly 2x** — never 3x or more. The distribution is:

- Cases with 50% duplication: every unique pair called 2x
- Cases with ~0% duplication: every pair called 1x
- No pair in any case is called 3x or more

## Root Cause Analysis

The exact-2x pattern is caused by the **tabling fixpoint iteration** in `src/work/fix.rs`. When a table's producer exhausts after discovering new answers, `make_replay_producer` creates a fresh pipe that re-executes the entire relation body to verify fixpoint (no new answers exist). This second pass repeats every `compose_nf` call identically.

For deterministic relations like `add`, each table produces exactly 1 answer:
1. **Pass 1**: Producer discovers the answer. All compose_nf calls happen.
2. **Pass 2**: Producer re-runs from scratch. Same compose_nf calls happen again. No new answers found → fixpoint confirmed.

The second pass is necessary for correctness (to confirm no new answers) but re-does all composition work.

## Conclusion

**compose_nf/meet_nf memoization is not worth implementing:**

1. **Too few saves**: Only 258 duplicate calls across all corpus cases.
2. **Low cache hit rate**: 21% — the 79% of misses add pure overhead (hash computation + lookup).
3. **Meet is worthless to cache**: 0.7% duplication.
4. **Root cause is fixpoint strategy, not kernel redundancy**: The duplication is structural, not algorithmic.

## Recommended Follow-up

The investigation reveals the real optimization target: **tabling fixpoint strategy** (Backlog: Tabling/Recursion Strategy #4, #5). Options:

1. **Semi-naive fixpoint**: Track which sub-computations depend on tables that gained new answers. Only re-run those parts, not the entire producer.
2. **Skip verification when trivially confirmed**: If no inner table gained new answers during the last pass, fixpoint is confirmed without re-running.
3. **Incremental producer suspension**: Suspend the producer rather than discarding it. Resume only when a dependent table updates.

These would eliminate not just the 258 duplicate compose calls but the entire redundant verification pass (thousands of engine steps).

## Artifacts

- Instrumentation: `src/perf_counters.rs` (pair-hash tracking behind `enabled()` gate)
- Instrumentation: `src/kernel/meet.rs` (hash computation via `record_meet_pair_hash`)
- Hook (not yet wired): `record_compose_pair_hash` exists in `perf_counters.rs` but is not called from `compose.rs`
- Measurement test: `tests/compose_meet_dedup_investigation.rs`
