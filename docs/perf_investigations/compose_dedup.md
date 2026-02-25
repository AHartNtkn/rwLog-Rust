# Investigation: Early Compose Result Dedup in DiagonalJoin

## Summary

Instrumented DiagonalJoin to measure duplicate rate of compose/meet result NFs entering the pending queue. DISCARD: 0% duplication across all 40 benchmark cases. No optimization possible.

## Problem

Hypothesis: different (a,b) compose pairs might produce the same output NF, creating redundant work in the DiagonalJoin pending queue and downstream dedup pipeline. If the duplicate rate were high enough, early dedup (checking against an emitted set before pushing to pending) could avoid unnecessary queue operations.

## Instrumentation Results

| Benchmark | push_pending total | unique | rejected (pending_set) | rejected (emitted_set) | dup_rate |
|---|---|---|---|---|---|
| treecalc_synth_flip | 19,610 | 19,610 | 0 | 0 | 0.0% |
| recursive_even_backward_first64 | 20,480 | 20,480 | 0 | 0 | 0.0% |
| Full corpus (40 cases) | 14,168 | 14,168 | 0 | 0 | 0.0% |

## Why It Didn't Work

1. **Zero duplication**: Every NF produced by compose_nf/meet_nf and pushed into DiagonalJoin's pending queue is unique. Different compose pairs never produce the same output NF within the same DiagonalJoin instance.
2. **Structural uniqueness**: The compose operation's substitution application produces structurally distinct terms from distinct input pairs. The variable routing through DropFresh ensures different inputs yield different outputs.
3. **Existing dedup is sufficient**: The pending_set in DiagonalJoin already catches any potential duplicates, but it's never triggered because there are none to catch.

## Files Changed

None merged (DISCARD).

## Insights

- Compose result dedup is a non-target: the computation itself produces unique results. This is consistent with the compose_memo finding (0.02% input pair duplication) — if inputs are unique, outputs are unique.
- The DiagonalJoin's existing dedup infrastructure (pending_set, DedupQueue) handles any theoretical duplicates but in practice catches none.
- This closes the compose dedup investigation space. Further work reduction must come from reducing the NUMBER of compose attempts (precheck/dispatch) or reducing per-compose COST (already exhausted).
