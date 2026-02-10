# Investigation: Cached NF Hash

## Summary

Added a pre-computed `cached_hash: u64` field to the `NF<C>` struct, computed once at construction time. All `Hash` trait operations return this cached value instead of re-hashing the full NF content. ~10% improvement on `recursive_even_backward_first64` (measured independently; ~7.8% combined with arc_pending_nf).

**Baseline:** 17.98ms (median)
**After:** 16.19ms (median)
**Improvement:** ~10% (independent measurement)
**Mann-Whitney U:** 100/100 (p < 0.01)
**Regression:** None on treecalc_first16 (neutral, 0.84ms both)

## Problem

From profiling of `recursive_even_backward_first64`:
- `DropFresh::hash` = 0.84% of total time (direct)
- `HashMap insert/get/rehash` = ~1.7% combined
- Total NF hashing overhead estimated at 5-10% when including SmallVec and TermId hashing within NF

NF is hashed repeatedly for dedup operations in FxHashSets throughout the system (DiagonalJoin seen/pending sets, Engine dedup, Table dedup). Each hash computation walks:
1. `match_pats: SmallVec<[TermId; 1]>` — element-by-element
2. `drop_fresh: DropFresh<C>` — in_arity, out_arity, SmallVec<[(u32,u32); 4]>, constraint
3. `build_pats: SmallVec<[TermId; 1]>` — element-by-element

This is redundant since NF content is immutable after construction.

## Solution

1. Added `cached_hash: u64` private field to NF
2. Removed derived `Hash`, `PartialEq`, `Eq` — implemented manually:
   - `Hash`: writes only `self.cached_hash` (one u64)
   - `PartialEq`: compares `cached_hash` first as fast rejection, then compares content fields
   - `Eq`: empty impl
3. Added `compute_nf_hash()` helper using `FxHasher` to hash all content fields
4. Changed `impl<C>` to `impl<C: Hash>` for constructors, computing hash at creation
5. Updated all direct NF construction sites to go through `NF::new()`

## Files changed

- `src/nf.rs` — Added cached_hash field, manual Hash/PartialEq/Eq impls, updated constructors

## Why 10% instead of 2-3%

The flat profile understates the true NF hashing cost because:
1. `DropFresh::hash` at 0.84% only counts DropFresh's own `hash` method, not the time spent hashing its SmallVec contents or constraint field
2. SmallVec hashing, TermId hashing, and ChrState hashing are distributed across generic trait impls that don't show up as distinct entries
3. The `PartialEq` fast-path (compare u64 hash before full content) also eliminates expensive equality checks for non-matching entries in hash tables

## Notes

The cached hash adds 8 bytes per NF (112B → 120B), still fitting in 2 cache lines. The PartialEq implementation accepts false positives from hash collisions by falling through to full content comparison, maintaining correctness. Combined with arc_pending_nf, the overlapping benefits on pending_set operations result in ~7.8% combined improvement rather than the sum.
