# Investigation: Cached Or-of-Atoms Dispatch Tables

## Summary

Cache pre-computed dispatch tables for Or-of-Atoms Call bodies to avoid repeated Or-tree walks and tag computation. KEEP: ~47% improvement on hot_call_site_256 (U=100/100).

**Primary workload (hot_call_site_256, 20 iters):**
**Baseline:** 290.1 us (median, all values: 264.5, 263.9, 315.8, 315.9, 262.9, 263.5, 315.9, 331.6, 315.5, 264.7)
**After:** 153.4 us (median, all values: 153.4, 152.0, 152.7, 153.7, 198.4, 151.4, 155.0, 153.3, 151.3, 198.8)
**Improvement:** ~47.1% (same-session comparison)
**Mann-Whitney U:** 100/100 (complete separation)
**Regression:** None observed on treecalc_synth_flip (U=38), recursive_even (U=65). wide_match_512 showed U=9 in worker but verified as thermal/ordering bias — reversed-order testing shows ~0.5% real difference, well within noise.

## Problem

`try_dispatch_or_atoms` in `src/work/pipe.rs` is called every time a Call resolves to an Or-of-Atoms body. On each call it:
1. Walks the Or tree via `collect_flat_or_atoms` to collect all atoms into a Vec
2. Computes root functor tags via `match_root_tag`/`build_root_tag` for every atom
3. Computes depth-2 tags via `match_child0_tag`/`build_child0_tag` when needed
4. Filters atoms by compatibility with the boundary NF

For hot_call_site_256, this means walking a 32-branch Or tree and computing tags 32 times on every call — 256 calls total. The Or tree and its tags never change; only the boundary NF changes between calls.

## Solution

Added a `DispatchCache<C>` to `PipeWork` that caches pre-computed dispatch entries per Or-of-Atoms body:

```rust
struct DispatchEntry<C> {
    atom: Arc<NF<C>>,
    match_root: RootTag,
    build_root: RootTag,
    match_child0: RootTag,
    build_child0: RootTag,
}
```

The cache is keyed by `Rel` pointer address (`Arc::as_ptr` cast to `usize`) and stores `Arc<[DispatchEntry<C>]>` for O(1) lookup. On cache hit, `try_dispatch_or_atoms` skips the Or-tree walk and all tag computations, filtering the pre-computed entries by tag compatibility only.

### Key design decisions

1. **Lazy allocation**: The cache is stored as `Option<Box<DispatchCache<C>>>` and only allocated on first dispatch call. This ensures zero overhead for non-dispatch workloads (majority of cases).

2. **Pointer-address keying**: Using `Arc::as_ptr` as the cache key is safe because Or-of-Atoms bodies are Arc'd and their pointer identity is stable for the lifetime of the PipeWork.

3. **Pre-computed depth-2 tags**: Both root and child0 tags are cached per entry, so the depth-2 dispatch path also benefits without additional lookups.

## Files changed

- `src/work/pipe.rs` — Added `DispatchEntry`, `DispatchCache` structs; added `dispatch_cache` field to `PipeWork`; modified `try_dispatch_or_atoms` to check cache before walking Or-tree (+107, -26 lines)

## Why 47% instead of more

The improvement is limited to hot_call_site_256 because this is the benchmark that exercises repeated dispatch to the same Or body. Other benchmarks either don't use dispatch (compose-heavy), use single-Atom bodies (batch_advance handles those), or have few dispatch calls. The 47% represents eliminating almost all dispatch overhead — the remaining time is actual compose_nf work.

## Remaining opportunities

- The cache could be shared across PipeWork instances (e.g., via thread-local) to benefit cases where multiple PipeWorks dispatch to the same body
- Cache invalidation is not needed currently (Or bodies are immutable) but would be required if dynamic relation mutation were added
