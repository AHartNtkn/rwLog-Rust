# Investigation: Deterministic Compose Fast-Path (MP1 Precursor)

## Summary

Added fast-path in ComposeWork::step_in_place for Emit+Fail compose pairs. DISCARDED: most compose_nf calls already bypass ComposeWork via PipeWork's batch advance, so the fast-path rarely triggers.

**Full corpus U:** 67/100 (not significant)
**Improvement:** 0.7%
**Verdict:** DISCARD

## Problem

deep_rewrite_depth256 (53ms, 9.4% of corpus) involves many deterministic compose operations. Hypothesis: detecting Emit(nf, Fail) + Emit(nf, Fail) compose pairs and short-circuiting diagonal join machinery would eliminate per-step overhead for deterministic composes.

## Implementation

In `ComposeWork::step_in_place`, added a check: when both left and right nodes are `Emit(nf, Fail)` (the simplest deterministic compose pattern), call `compose_nf` directly instead of going through the 3-step diagonal join sequence (pull-left, pull-right, compose). Collapses 3 steps into 1.

## Why It Failed

1. **Most compose_nf calls bypass ComposeWork entirely.** deep_rewrite depth64 shows `steps=6, compose=388` — meaning 388 compose_nf calls happen via `PipeWork::absorb_at()` and `normalize_mid_atoms()` directly, not through ComposeWork/DiagonalJoin. The `try_batch_advance_calls` fast-path in PipeWork already handles deterministic chain patterns.

2. **ComposeWork is for nondeterministic cases.** When ComposeWork IS created (via advance_fix, advance_call), both sides are typically `Work(Pipe(...))` nodes, NOT simple `Emit(nf, Fail)` nodes. The Emit+Fail fast-path rarely triggers.

3. **compose_nf kernel cost is the bottleneck**, not step dispatch overhead. Since PipeWork already batches deterministic chains, there's no step-level overhead left to optimize.

4. **Retry-loop approach breaks fairness.** Looping within step_in_place when More is returned caused hangs in stress-tier benchmarks by violating fairness guarantees for nondeterministic composes with Or branches.

## Key Insight

PipeWork's `try_batch_advance_calls` and `normalize_mid_atoms` already serve as the "pipeline fusion" for deterministic sequences. ComposeWork/DiagonalJoin is only created for cases that genuinely need nondeterministic search. The MP1 (bytecode compilation) path would need to fuse at the Rel level before pipe construction, not at the ComposeWork step level.

## Files Changed (not merged)

- `src/work/compose.rs` — Added Emit+Fail fast-path in step_in_place (+20 lines)
