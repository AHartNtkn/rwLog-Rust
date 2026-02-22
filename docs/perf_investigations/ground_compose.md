# Investigation: Ground-Term Compose Fast Path

## Summary

Added a fast path in compose_nf for fully-ground NFs (no variables, no constraints). DISCARDED: existing pipeline already handles ground terms efficiently via `is_ground()` short-circuits.

**Full corpus U:** 46/100 (not significant)
**sequence_chain_len4096:** 84.5ms → 83.9ms (0.7%, negligible)
**Verdict:** DISCARD

## Problem

sequence_chain_len4096 does 4096 composes at 100% success rate on ground terms (86ms, 15.1% of corpus). Hypothesis: a fast path skipping full matching/substitution for ground-ground compose could reduce overhead.

## Implementation

At the top of `compose_nf_impl()`, when all match/build pats on both NFs are ground and both constraints are empty, skip the matching pipeline entirely. Matching reduces to TermId equality (hash-consed), and the result is trivially assembled: `NF(a.match_pats, identity(0), b.build_pats)`.

## Why It Failed

1. **Root functor precheck** already catches mismatches cheaply (one term store lookup per compose)
2. **`apply_subst` with `is_ground()` bit** already short-circuits for ground terms, returning the original TermId without traversal — so the existing pipeline does almost no work for ground terms
3. **The real bottleneck** for sequence_chain is engine-level step dispatch overhead (4096 step dispatches), not compose_nf itself. At ~20us per step with 4096 steps, compose is a small fraction of each step's cost

## Key Insight

sequence_chain_len4096's cost is dominated by engine stepping overhead (step_node dispatch, continuation management, pipe normalization), not compose_nf. This aligns with the pipeline_fuse investigation: fusing multiple deterministic steps into one is the correct approach for this workload, not faster compose.

## Files Changed (not merged)

- `src/kernel/compose.rs` — Added ground compose fast path (~30 lines)
