# Investigation: Short-Circuit Constraint Pipeline for Empty Constraints

## Summary

Attempted to skip the constraint pipeline (apply_subst + combine_owned + normalize_owned) when both NFs have empty constraints. DISCARD: full short-circuit breaks ChrState identity/dedup; safe partial version (skip normalize_owned only) is too narrow to matter.

**Primary workload (recursive_even_backward_first64, 5 iters):**
**Baseline:** 10967 us (median, all values: 11318, 10640, 12275, 12037, 11156, 10917, 10575, 10860, 11017, 10867)
**After:** 11210 us (median, all values: 12345, 11058, 11021, 10896, 12083, 11554, 11029, 12001, 11073, 11348)
**Improvement:** -2.2% (noise)
**Mann-Whitney U:** 29/100 (not significant)

## Problem

The compose_nf success path always runs the full constraint pipeline: apply_subst → combine_owned → normalize_owned. For workloads without constraints (recursive_even with UnitConstraint), these should be complete no-ops. For treecalc_synth_flip (ChrState), the a-side constraint is usually empty while b-side has a ChrState, so partial short-circuiting could help.

## Approaches Tried

### 1. Full short-circuit (skip apply_subst + combine_owned + normalize_owned)

**Result: Correctness failure.** ChrState::default() creates a ChrProgram::empty() with a unique `program_id` via atomic counter, which breaks Hash+Eq dedup. Cloning input constraints also breaks dedup because internal state differs from what the full pipeline produces. Both approaches caused either test failures (duplicate answers) or massive regression (treecalc_synth_flip: 330ms → 2800ms due to compose count 278K → 1.5M from broken dedup).

### 2. Safe partial short-circuit (skip only normalize_owned when combined result is empty)

**Result: No measurable improvement (U=29/100).** For UnitConstraint, the compiler already eliminates the entire constraint pipeline via `ALWAYS_EMPTY = true` constant. For ChrState, the apply_subst + combine_owned calls dominate constraint cost, not normalize_owned. Skipping normalize_owned alone saves too little.

### Key design decisions

1. **ChrState identity is semantically meaningful**: program_id uniqueness makes ChrState fundamentally incompatible with naive short-circuiting. Two "empty" ChrStates with different program_ids produce different hashes, breaking the normalize_owned cache and the entire constraint dedup mechanism.

2. **UnitConstraint is already optimized away**: The compiler's monomorphization with `ALWAYS_EMPTY = true` eliminates constraint operations at compile time for non-CHR workloads. No runtime short-circuit can improve on that.

## Files changed

- `src/kernel/compose.rs` — Added is_empty() check after combine_owned to skip normalize_owned
- `src/kernel/meet.rs` — Same optimization pattern

## Remaining opportunities

- Making ChrState::combine_owned itself short-circuit when both inputs are empty (returning self without allocating new state) — but this requires careful handling of program_id identity
- The real remaining constraint cost is in apply_subst_to_data for non-empty ChrStates, not in the empty-constraint path
