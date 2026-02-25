# Investigation: Inline Small Deterministic Relation Bodies at Definition Time

## Summary

Replaced `Rel::Call(id)` with `Rel::Atom(nf)` at construction time for single-Atom Env bindings. DISCARDED: existing `try_batch_advance_calls` already handles this at runtime, making compile-time inlining redundant.

**Full corpus U:** 34/100 (not significant)
**sequence_chain_len4096 U:** 31/100 (not significant)
**Verdict:** DISCARD

## Problem

sequence_chain_len4096 (87ms, 15.1% of corpus) involves 4096 chained Call nodes. Hypothesis: inlining Call nodes to Atoms at definition time would eliminate per-call dispatch overhead and allow `normalize_mid_atoms` to fuse adjacent Atoms directly.

## Implementation

Applied in three locations:
1. `rel_to_node` — for `Rel::Seq` factors and standalone `Rel::Call` nodes
2. `PipeWork::from_rel` — for Seq factors
3. `PipeWork::from_rel_with_boundaries` — for producer pipe body factors

When an Env binding is a single `Rel::Atom(nf)` (guaranteed non-recursive since Atoms contain NFs, not Rel sub-expressions), replaced the `Rel::Call(id)` with `Rel::Atom(nf.clone())` at construction time.

## Why It Failed

1. **`try_batch_advance_calls` already handles this** — It loops through Calls at pipe ends, resolves single-Atom bodies via `env.lookup` (O(1) with HashMap), and composes directly into the boundary in a tight loop. Per-call overhead is just: env.lookup, pattern match on Rel::Atom, and absorb_at (same compose_nf call).

2. **Inlining just shifts work** — Converting Calls to Atoms at construction moves the same compose_nf operations from `try_batch_advance_calls` to `normalize_mid_atoms`, with no net reduction in total work.

3. **The real bottleneck is compose_nf count** — sequence_chain_len4096 requires 4096 compose_nf operations regardless of whether they happen via call resolution or atom normalization. Reducing the number of compositions (e.g., batching multiple into one, or fusing the whole chain at the Rel level) is the only path forward.

## Key Insight

For sequence_chain_len4096, the per-call dispatch overhead is negligible compared to the 4096 compose_nf operations. `try_batch_advance_calls` is already an efficient O(1)-per-call resolver. To improve this workload further requires reducing compose operation count, not dispatch overhead.

## Files Changed (not merged)

- `src/work/pipe.rs` — Added compile-time Call→Atom inlining in from_rel, from_rel_with_boundaries
- `src/eval.rs` — Added compile-time Call→Atom inlining in rel_to_node
