# Investigation: Arc-wrap Pending NFs in DiagonalJoin

## Summary

Extended Arc<NF<C>> wrapping from DiagonalJoin's seen vectors (already Arc'd) to the pending VecDeque and pending_set FxHashSet. Eliminates deep NF clones when inserting into pending dedup set. ~7.6% improvement on `recursive_even_backward_first64` (measured independently; ~7.8% combined with cached_nf_hash).

**Baseline:** 18.00ms (median)
**After:** 16.64ms (median)
**Improvement:** ~7.6% (independent measurement)
**Mann-Whitney U:** 100/100 (p < 0.01)
**Regression:** None on treecalc_first16 (0.84ms → 0.83ms, slight improvement)

## Problem

From profiling of `recursive_even_backward_first64`:
- `ChrState::clone` = 2.21% of total time
- Additional NF clone overhead hidden in SmallVec clone, DropFresh clone

DiagonalJoin's `push_pending` deep-cloned every NF before inserting into the pending_set for dedup:
```rust
pub(crate) fn push_pending(&mut self, nf: NF<C>) {
    if self.pending_set.insert(nf.clone()) {  // Deep clone here
        self.pending.push_back(nf);
    }
}
```

Each deep clone copies: 2 SmallVecs + DropFresh (SmallVec + ChrState with Arc<ChrProgram> atomic increment). With thousands of push_pending calls per evaluation, this is significant.

## Solution

Changed field types:
- `pending: VecDeque<NF<C>>` → `VecDeque<Arc<NF<C>>>`
- `pending_set: FxHashSet<NF<C>>` → `FxHashSet<Arc<NF<C>>>`

`push_pending` now wraps NF in Arc once, then uses `Arc::clone()` (O(1) atomic increment) for the set insert:
```rust
pub(crate) fn push_pending(&mut self, nf: NF<C>) {
    let arc = Arc::new(nf);
    if self.pending_set.insert(Arc::clone(&arc)) {
        self.pending.push_back(arc);
    }
}
```

`pop_pending` uses `Arc::try_unwrap` to recover the owned NF without cloning (refcount is 1 after set removal):
```rust
pub(crate) fn pop_pending(&mut self) -> Option<NF<C>> {
    let arc = self.pending.pop_front()?;
    self.pending_set.remove(&*arc);
    Some(Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone()))
}
```

The public API is unchanged (`push_pending` takes `NF<C>`, `pop_pending` returns `Option<NF<C>>`).

## Files changed

- `src/work/diagonal.rs` — Changed pending/pending_set types and push/pop logic

## Why 7.6% instead of 1-2%

The estimated 0.5-1.5% was very conservative. The actual improvement is larger because:
1. `push_pending` is called for every compose/meet result in the diagonal join — thousands of times per evaluation
2. The deep NF clone included ChrState::clone (Arc atomic increment), SmallVec clones (heap allocation for non-inline), and DropFresh SmallVec clone
3. Eliminating these clones also reduces allocation pressure, improving overall cache behavior
4. The 2.21% ChrState::clone in the profile only counted the constraint portion; full NF clone cost was distributed across many functions

## Notes

After pop_pending removes the Arc from pending_set, the refcount is exactly 1 (only the popped Arc remains). `Arc::try_unwrap` succeeds without cloning. The `unwrap_or_else` fallback clone is a safety net that should never trigger in practice. This extends the same Arc pattern already proven in seen_l/seen_r (Round 3, arc_diagonal_join).
