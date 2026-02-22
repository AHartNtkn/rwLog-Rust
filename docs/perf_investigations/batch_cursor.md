# Investigation: Batch Compose Cursor Processing

## Summary

Attempted to process all pending compose pairs per step (while preserving one-step delay). DISCARDED: engine steps are driven by emit count, not cursor processing count. Batching cursor processing doesn't reduce total steps.

**Full corpus U:** 50/100 (no improvement)
**Verdict:** DISCARD

## Problem

ComposeWork processes one compose pair per step via cursor-based iteration. The hypothesis was that processing multiple pairs in a single step_in_place call could reduce step overhead for compose-heavy workloads.

## Implementation

Modified ComposeStrategy to process all available compose pairs in a single pre_step call instead of advancing the cursor by one position per call.

## Why It Failed

Engine steps are driven by **emit count** (how many NFs are produced and propagated), not by cursor processing count. When compose succeeds, an NF is emitted and flows through the pipeline, driving another engine step regardless of how many cursor advances preceded it. When compose fails (99%+ for treecalc), the cursor advances are trivially cheap.

Batching cursor advances within a step doesn't reduce the number of emitted NFs, so total engine steps remain unchanged. The per-cursor-advance cost (one compose_nf call) is the actual work — combining multiple compose_nf calls into one step just moves work between steps without eliminating any.

## Key Insight

For compose-heavy workloads, the cost is dominated by compose_nf calls themselves, not the stepping/dispatch overhead around them. This is consistent with the adaptive_sched findings: the structural overhead (Or-spine walks, step dispatch) is negligible compared to the computational work (compose, matching, substitution).

## Files Changed (not merged)

- `src/work/compose.rs` — Modified cursor processing in ComposeStrategy
