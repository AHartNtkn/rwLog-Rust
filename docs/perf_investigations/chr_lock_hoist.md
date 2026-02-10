# Investigation: Hoist TermStore read_lock out of match_head

## Summary

Attempted to hoist `terms.read_lock()` acquisition out of `match_head` into the caller's `SearchCtx` to avoid per-call lock overhead. No improvement.

**Baseline:** 1418855us (median, all values: 1452308, 1419124, 1392721, 1407196, 1426266, 1396517, 1418586, 1411669, 1421324, 1432875)
**After:** 1411010us (median, all values: 1411219, 1396122, 1397557, 1405155, 1410801, 1441728, 1448551, 1422520, 1407985, 1436316)
**Improvement:** 0.55% (noise)
**Mann-Whitney U:** 52/100 (not significant)
**Regression:** N/A

## Problem

`match_head` (src/chr/mod.rs:1694) acquires `terms.read_lock()` on every invocation. It is called from `find_match_by_ids_reuse` (once per anchor head) and from `search_steps_inner` (in a tight loop over candidates for each join step). `match_head` was 2.68% of total runtime in profiles.

## Solution Attempted

Added `term_guard: TermReadGuard<'a>` to `SearchCtx`. Changed `match_head` to accept `&TermReadGuard<'_>` instead of `&TermStore`. Acquired the lock once in `find_match_by_ids_reuse` and passed it through SearchCtx to all match_head calls.

Implementation was correct: 716 tests passed, zero clippy warnings.

## Files changed

- `src/chr/mod.rs` — Added `term_guard` to `SearchCtx`, changed `match_head` signature, updated both call sites.

## Why it failed

1. **Parking_lot read lock is extremely cheap uncontended**: In a single-threaded benchmark, the parking_lot RwLock read acquisition is ~10ns (atomic load + compare-and-swap). This is negligible compared to the actual pattern matching work in match_head.

2. **Profile attribution includes entire function**: The 2.68% attributed to `match_head` includes predicate comparison, argument length check, argument iteration, and pattern matching — not just the lock. The lock is a tiny fraction of that cost.

3. **Would matter more under contention**: This optimization would be more impactful in a multi-threaded context where read lock contention exists, but the benchmark is single-threaded.

## Remaining opportunities

- In a future multi-threaded implementation, this optimization would be worth revisiting.
- The actual pattern matching work inside match_head (via `match_pat_bind_locked`) is the real cost and could potentially be optimized with better indexing or early rejection.
