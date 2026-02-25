# Investigation: Simplify FixWork Hot-Path State Machine

## Summary

Fused FixWork::step_in_place into a single Table::step_consumer() method with cold-path outlining. DISCARD: no measurable improvement (U=50/100) — FastLock is already zero-cost, and the profile is too flat for state machine optimization to help.

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 216703 us (median, all values: 199781, 209940, 210918, 212005, 211551, 218359, 216988, 220133, 221743, 218418)
**After:** 214271 us (median, all values: 210253, 208870, 211688, 208312, 206763, 220334, 221007, 221943, 220098, 214271)
**Improvement:** ~0% (within noise)
**Mann-Whitney U:** 50/100 (not significant)

## Problem

FixWork::step_in_place handles multiple states (answer checking, producer stepping, fixpoint detection) with separate match arms, function calls, and repeated lock acquisitions. The hypothesis was that fusing these into a single inlined flow with cold-path outlining could reduce per-step overhead.

## Solution Attempted

- Fused FixWork::step_in_place into a single `Table::step_consumer()` method combining answer check, producer state check + try-mark-active, single producer step, deactivation, and answer re-check
- Outlined cold paths (init_and_step_producer, handle_producer_exhausted) with `#[cold] #[inline(never)]`
- Added `#[inline]` to hot-path Table methods

## Why It Failed

1. **FastLock is already zero-cost.** It's an UnsafeCell with no-op lock/unlock, so consolidating lock acquisitions provides no actual benefit — the "repeated locks" in the original code are already free.

2. **Profile is too flat for state machine optimization.** No function exceeds ~5% self-time. FixWork stepping is spread across many functions, and the overhead is dominated by the actual `step_node` call into the producer, not the scaffolding around it.

3. **Compiler already makes similar inlining decisions.** The cold-path outlining and `#[inline]` hints didn't produce measurable changes because LLVM at -O2 already handles this well.

## Files changed

- `src/kernel/fix.rs` — Fused step_in_place into Table::step_consumer()

## Remaining opportunities

- FixWork state machine optimization is a dead end — the overhead is in the actual computation (step_node, compose_nf, normalize_owned), not the dispatch scaffolding
- Further FixWork improvements would require reducing the number of steps needed (algorithmic change), not making each step cheaper (micro-optimization)
