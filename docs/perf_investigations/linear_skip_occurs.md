# Investigation: Skip Occurs Check for Linear (No Repeated Vars) Patterns

## Summary

Attempted to skip the occurs check entirely for NFs with linear patterns (no repeated variables). DISCARD: ~28% regression (U=0/100). The cost of computing linearity on every compose/meet call far exceeds the savings from skipping the already-cheap fast_occurs check.

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 211244 us (median, all values: 208669, 212343, 208315, 204946, 208308, 205364, 208393, 220735, 219386, 223146)
**After:** 268108 us (median, all values: 269256, 263909, 270091, 260277, 261628, 262961, 277231, 274674, 274059, 261432)
**Improvement:** -28% (catastrophic regression)
**Mann-Whitney U:** 0/100 (complete separation, wrong direction)

## Problem

After fast_occurs (18.4% improvement), occurs checks use O(1) var_range lookups but still do some tree walking for non-ground terms. The hypothesis was that linear patterns (where each variable appears at most once) can never create cyclic bindings, so the occurs check always returns false. Pre-tagging NFs as linear and skipping occurs checks during matching could save the remaining overhead.

## Approach

Added `pats_are_linear()` function in nf.rs that walks pattern trees to check whether every variable appears at most once. Uses a 64-bit bitmap for variables < 64 and falls back to HashSet for higher indices. Called this check in compose_nf and meet_nf before matching, passing a `skip_occurs` flag down to the matching functions.

Files changed: src/nf.rs (linearity check), src/matching.rs (skip_occurs parameter), src/kernel/compose.rs (call linearity check), src/kernel/meet.rs (call linearity check), src/kernel/util.rs (plumb flag).

## Why It Failed

1. **Linearity check cost on hot path**: `pats_are_linear()` walks the entire pattern tree with a stack, reads from `TermStore::nodes` (taking a read lock), and does bitmasking/HashSet operations. This runs on EVERY compose/meet call — 278K compose attempts per evaluation. Even a fast tree walk at that frequency is devastating.

2. **fast_occurs already very cheap**: After the fast_occurs optimization, occurs checks are O(1) for the common case (var_range disjoint from term's range). The remaining occurs check overhead is tiny — perhaps 1-2% of total time. Saving 1% by adding a check that costs 30% is catastrophic.

3. **Should have been cached at construction time**: If linearity were computed once when the NF is created (as a flag in the NF struct), the per-call cost would be zero. But the worker computed it on every compose/meet invocation, turning an O(1) flag into an O(n) per-call computation on the hot path.

## Files changed

- `src/nf.rs` — Added pats_are_linear() function
- `src/matching.rs` — Added skip_occurs parameter to matching functions
- `src/kernel/compose.rs` — Called linearity check before matching
- `src/kernel/meet.rs` — Called linearity check before matching
- `src/kernel/util.rs` — Plumbed skip_occurs flag

## Remaining opportunities

- A corrected version that stores linearity as a flag in NfInner (computed once at NF construction time, zero cost at compose/meet time) could still be worth investigating, but the expected savings are very small (1-2% at most) since fast_occurs already makes occurs checks nearly free
- The broader insight: any per-call check on the compose hot path (278K calls) must be cheaper than the work it saves. Even O(1) checks with significant constant factors can regress.
