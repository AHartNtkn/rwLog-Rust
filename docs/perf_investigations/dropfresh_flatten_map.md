# Investigation: Remove Redundant Arc from DropFresh Map

## Summary

Removed the `Arc` wrapper from DropFresh's `map` field, reverting to direct `SmallVec` storage now that NF itself is Arc-wrapped. ~2.7% improvement on recursive_even_backward_first64.

**Baseline median:** 3947.044us (worker measurements)
**After median:** 3841.192us (worker measurements)
**Improvement:** ~2.7% (same-session comparison)
**Mann-Whitney U:** 74/100 (p < 0.05)
**Regression:** None observed on treecalc_first16 (U=46/100, neutral)

## Problem

In Round 14 ("dropfresh_arc_map"), the DropFresh `map` field was changed from `SmallVec<[(u32,u32); 4]>` to `Arc<SmallVec<[(u32,u32); 4]>>` to make DropFresh cloning O(1). This was worthwhile when NF::clone was expensive (deep-copying DropFresh).

In Round 15 ("nf_arc_wrap"), NF itself was wrapped in `Arc<NfInner>`, making NF::clone just an atomic ref count bump. DropFresh is never independently cloned anymore — it only lives inside NfInner which is shared via Arc. The map's Arc wrapper became pure overhead: one `Arc::new()` heap allocation on every NF construction without any benefit.

## Solution

Reverted `map` field to direct `SmallVec<[(u32,u32); 4]>` storage:

```rust
// Before (Round 14):
pub map: Arc<SmallVec<[(u32, u32); 4]>>,

// After:
pub map: SmallVec<[(u32, u32); 4]>,
```

Removed `Arc::new()` wrapping from all construction sites.

### Key design decisions

1. **Revert rather than new optimization**: The Arc wrapper was added for a specific reason that no longer applies. Removing it is the correct response to the superseding optimization.
2. **SmallVec inline buffer**: SmallVec<[(u32,u32); 4]> stores up to 4 pairs inline (32 bytes). Most DropFresh maps have 0-3 entries, so this rarely heap-allocates.

## Files changed

- `src/drop_fresh.rs` — Changed field type, removed Arc wrapping in identity(), identity_with_constraint(), new(), disconnect(), compose()
- `src/nf.rs` — Removed Arc wrapping in NF::factor() and factor_tensor()
- `src/kernel/dual.rs` — Removed Arc wrapping in dual_drop_fresh() and test sites
- `src/kernel/compose.rs` — Removed Arc wrapping in test construction site

## Why 2.7% instead of more

The Arc::new allocation cost was a small per-NF overhead. With 378 compose calls per query (each creating at least one NF), the savings of ~378 Arc::new calls amounts to a modest improvement. The SmallVec inline buffer means we also avoid the SmallVec heap allocation for small maps, but this was already the case before (Arc just added overhead on top).

## Remaining opportunities

- DropFresh could be further simplified by inlining its fields directly into NfInner (eliminating the DropFresh struct entirely), but this would be a large refactoring with unclear benefit.
- The `compose()` method on DropFresh still allocates a new SmallVec — this could use a pre-allocated buffer.
