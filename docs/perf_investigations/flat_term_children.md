# Investigation: Flat Term Children Arena for Cache Locality

## Summary

Attempted to improve cache locality for tree-walking operations (apply_subst 33%, occurs 17%, shift_term 3%) by changing Term::App's child storage. DISCARD: SmallVec<[TermId; 4]> is already at minimum 24 bytes — capacity reduction has zero effect. Full arena redesign too complex for uncertain gain.

## Problem

~50% of total runtime on treecalc_synth_flip is spent in tree-walking functions (apply_subst, occurs_unlocked, shift_term). These walk term trees by looking up children in TermStore. Term::App stores children in SmallVec<[TermId; 4]>, which is interleaved with other terms' data in the nodes Vec.

## Approaches Investigated

### 1. SmallVec capacity reduction (SmallVec<[TermId; 1]>)

SmallVec<[TermId; 1]> and SmallVec<[TermId; 4]> are both **24 bytes** on this platform. SmallVec's minimum size is `(ptr, usize, usize)` = 24 bytes for the heap-allocated case, and `[TermId; 4]` = 16 bytes fits within that 24-byte minimum. Reducing capacity does not shrink Term at all.

### 2. Fixed-size array

The Term enum is 32 bytes (24 SmallVec + 4 FuncId + 4 discriminant). Any fixed-size array approach would still need dynamic dispatch for variable arity, providing no size benefit.

### 3. Full children arena redesign

Changing `Term::App(FuncId, SmallVec<[TermId; 4]>)` to `Term::App(FuncId, u32, u16)` with a separate `children: Vec<TermId>` arena would shrink Term from 32 to ~12 bytes (2.67x density improvement). However:
- Requires changing 120+ call sites across 8 files
- Requires replacing the hashcons HashMap with custom hash lookup
- Requires new TermData struct for both nodes and children under same lock
- Every `Term::App(f, children)` pattern match must be rewritten
- For treecalc workload (arity 0-2), SmallVec never spills to heap — benefit is purely from density

## Files changed

None (research only — DISCARD before implementation).

## Remaining opportunities

- The full arena redesign remains theoretically viable but would be a major architectural change. It should only be attempted if profiling confirms cache misses in the nodes Vec are a significant contributor.
- Alternative: SoA (struct-of-arrays) layout where FuncIds, children offsets, and children data are stored in separate Vecs for better SIMD-friendly traversal.
