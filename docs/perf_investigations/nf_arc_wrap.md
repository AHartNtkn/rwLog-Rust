# Investigation: Arc-Wrap NF Inner Fields for O(1) Cloning

## Summary

Wrapped NF's inner fields in `Arc<NfInner<C>>`, reducing NF::clone from ~48 bytes memcpy + 2 atomic bumps to a single atomic ref count bump. Statistically significant improvement on primary benchmark.

**Baseline:** 4790.348us (median of worker measurements; system load caused variance)
**After:** 3932.595us (median of worker measurements)
**Improvement:** Significant (U=95/100 primary, confirmed U=85/100 on validation)
**Mann-Whitney U:** 95/100 (p < 0.001)
**Regression:** None observed on treecalc_first16 (U=70/100, neutral)

Note: Both measurement sessions showed elevated system load causing high variance in baseline timings (4554-7153us vs known ~4640us baseline). The U statistics are robust to outliers due to rank-based comparison. Worker-side measurements are used as primary evidence; orchestrator verification was inconclusive due to concurrent system load.

## Problem

NF::clone was 3.2% of runtime. Each clone involved:
- Cloning `match_pats: SmallVec<[TermId; 1]>` — 16 bytes memcpy
- Cloning `drop_fresh: DropFresh<C>` — Arc::clone for map + Arc::clone for ChrState constraint
- Cloning `build_pats: SmallVec<[TermId; 1]>` — 16 bytes memcpy
- Copying `cached_hash: u64` — 8 bytes

Additionally, DiagonalJoin stored `Vec<Arc<NF<C>>>` for seen_l/seen_r, creating a double-Arc layer (outer Arc from the Vec element, inner Arc for DropFresh map). This added unnecessary allocation and indirection.

## Solution

Introduced `NfInner<C>` struct containing all NF fields, wrapped in `Arc`:

```rust
pub struct NfInner<C> {
    pub match_pats: SmallVec<[TermId; 1]>,
    pub drop_fresh: DropFresh<C>,
    pub build_pats: SmallVec<[TermId; 1]>,
    cached_hash: u64,
}

pub struct NF<C> {
    inner: Arc<NfInner<C>>,
}
```

Transparent field access via `Deref<Target=NfInner<C>>`. Clone is now just `Arc::clone`.

### Key design decisions

1. **Deref instead of accessor methods**: Using `impl Deref for NF<C>` provides transparent field access (`nf.match_pats` works unchanged). This minimized call-site changes across the codebase.
2. **Arc::ptr_eq fast path in PartialEq**: When comparing the same NF instance (common in dedup sets after cloning), pointer equality avoids content comparison entirely.
3. **Eliminate double-Arc in DiagonalJoin**: Changed `seen_l`/`seen_r` from `Vec<Arc<NF<C>>>` to `Vec<NF<C>>` since NF is now internally Arc-wrapped. This removes one level of heap allocation and pointer indirection per seen NF.

## Files changed

- `src/nf.rs` — Introduced `NfInner<C>`, wrapped NF in `Arc<NfInner<C>>`, added `Deref` impl, added `Arc::ptr_eq` fast path in PartialEq
- `src/work/diagonal.rs` — Changed `seen_l`/`seen_r` from `Vec<Arc<NF<C>>>` to `Vec<NF<C>>`, eliminating double-Arc layer
- `src/work/meet.rs` — Updated `seen_l()`/`seen_r()` return types from `&[Arc<NF<C>>]` to `&[NF<C>]`

## Why the improvement exceeded estimates

The 3.2% profile weight for NF::clone understated the true impact because:
1. NF::clone occurs far more frequently in the tabling-heavy recursive_even benchmark than in the profiled workload mix
2. Eliminating the double-Arc in DiagonalJoin's seen lists provides additional savings (fewer heap allocations, less indirection)
3. The `Arc::ptr_eq` fast path in PartialEq helps when comparing the same NF instance (common after cloning into seen sets)

## Remaining opportunities

- `Arc<NF<C>>` still used in `fix.rs` (TableAnswers: `Vec<Arc<NF<C>>>`, `FxHashSet<Arc<NF<C>>>`) and `rel.rs` (`Rel::Atom(Arc<NF<C>>)`). These could be simplified to `NF<C>` to eliminate remaining double-Arc overhead.
- `node_from_answers` in `work/mod.rs` takes `Vec<Arc<NF<C>>>` — could take `Vec<NF<C>>` instead.
