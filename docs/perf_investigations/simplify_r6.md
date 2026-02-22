# Investigation: Consolidation Round 6 — occurs_check_impl! Macro

## Summary

Consolidated `occurs_locked` and `occurs_unlocked` (90% identical, ~70 lines each) into a single `occurs_check_impl!` macro with expression fragments for the three differing operations. KEEP (consolidation): -33 net lines, neutral performance (U=46/100).

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 319253 us (median, all values: 322816, 320192, 318314, 323710, 316849, 317283, 318034, 321247, 319253, 320655)
**After:** 319413 us (median, all values: 330499, 319113, 323379, 322534, 320949, 316948, 320174, 324458, 318652, 319015)
**Improvement:** ~0% (neutral)
**Mann-Whitney U:** 46/100 (not significant — expected for consolidation)
**Regression:** None observed on recursive_even (U=52), join_high_overlap (U=47)

## Problem

`occurs_locked` and `occurs_unlocked` in `src/matching.rs` were two ~70-line functions with 90% identical logic. The only differences were:
1. How to get a term's var_range (locked vs unlocked TermStore access)
2. How to dereference substitution variables (locked vs unlocked)
3. How to get term children (locked vs unlocked)

This duplication made maintenance error-prone — any optimization to the occurs check algorithm (like the recent fast_occurs var_range tracking) had to be applied to both functions identically.

## Solution

Replaced both functions with an `occurs_check_impl!` macro that takes three expression fragments as parameters:
- `$var_range`: expression to get a term's (min_var, max_var) range
- `$deref`: expression to dereference a variable through substitution
- `$get_term`: expression to get a Term from a TermId

The macro contains the full occurs check algorithm once: worklist-based traversal, var_range fast rejection, ground-term skipping, and post-deref ground check. The two public functions become thin wrappers that invoke the macro with the appropriate locked/unlocked expressions.

### Key design decisions

1. **Macro over generic function with closures**: A generic function parameterized by closures would add runtime overhead (indirect calls) in a hot path. The macro expands to identical machine code as the original hand-written functions, with zero abstraction cost.

2. **Expression fragments over trait-based dispatch**: A trait like `TermAccess` with locked/unlocked impls would be cleaner but risks the compiler failing to monomorphize and inline in this performance-critical code. Expression fragments are guaranteed to inline.

## Files changed

- `src/matching.rs` — Replaced `occurs_locked` (~70 lines) and `occurs_unlocked` (~70 lines) with `occurs_check_impl!` macro (~50 lines) + two thin wrappers (~5 lines each). Net reduction: -33 lines.
- `src/work/pipe.rs` — Minor formatting change (line wrapping in dispatch_cache closure).

## Remaining opportunities

- Similar consolidation pattern could apply to other locked/unlocked function pairs in the codebase (deref chains, term access patterns)
- The occurs_check_impl! macro could be extended if future occurs check variants are needed (e.g., for different substitution representations)
