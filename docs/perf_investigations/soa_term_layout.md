# Investigation: Structure-of-Arrays Layout for TermStore

## Summary

Investigated whether TermStore could benefit from SoA (Structure-of-Arrays) layout instead of AoS (Array-of-Structures). DISCARD: Term struct is only 32 bytes (2 fit per cache line), dominant access pattern reads full struct, and var_ranges is already a separate parallel array. Current hybrid layout is already optimal.

**No performance measurement needed** — structural analysis shows no opportunity.

## Problem

The hypothesis was that TermStore's AoS layout wastes cache capacity when traversals only need one or two fields per term. SoA layout (parallel arrays for functors, children, ground bits, var_ranges) would improve cache line utilization.

## Why It Failed

1. **Term is only 32 bytes.** Two entire Term structs fit in one 64-byte cache line. Accessing any field brings the entire struct into L1 — no wasted capacity.
   - Term::Var(u32): 8 bytes
   - Term::App(FuncId, SmallVec<[TermId; 4]>): 32 bytes

2. **Dominant access pattern reads full struct.** Matching checks functor+arity then immediately reads children. apply_subst reads the full structure. compose_nf reads functors and children together. These are not independent single-field accesses.

3. **SoA would actively hurt.** Splitting into parallel arrays would turn each logical "term access" into 2+ separate memory lookups (functor array + children array) instead of one, doubling cache misses for the common case.

4. **Infrequent fields already separated.** var_ranges: Vec<(u32, u32)> is already stored as a separate parallel array, not inside Term. This is the one field accessed independently (for range-based skipping in apply_subst). The current design already has the right SoA/AoS split.

5. **Inline TermId handles light-access cases.** Variables and nullary constants are encoded directly in TermId (no store access). Terms that hit the store are App nodes with children, which always need functor + children together.

## Files changed

None — analysis only, no code changes.

## Remaining opportunities

- Term representation SoA is a dead end — the current hybrid layout is already optimal
- Arena indices for TermStore (Term Rep #1) could still help with allocation locality but not cache line utilization
- The flat profile (no function above 5% self-time) suggests term access is well-distributed and not a bottleneck at the per-access level
