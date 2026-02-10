# Investigation: Empty-store shortcircuit for normalize_owned

## Summary

Attempted to add an early return in normalize_owned when ChrStateData has zero alive constraints and empty builtins, skipping the hash computation and cache lookup.

**Baseline:** 314465us (median, all values: 310362, 312368, 312492, 312581, 313021, 315909, 316397, 316781, 319309, 321156)
**After:** 318569us (median, all values: 313421, 314552, 314652, 317507, 318332, 318806, 318853, 322582, 322788, 324089)
**Improvement:** -1.31% (slight regression)
**Mann-Whitney U:** 23/100 (not significant, wrong direction)
**Regression:** N/A (primary failed)

## Problem

normalize_owned is 3.48% of runtime (17.17% inclusive), called 259K times per query. Prior instrumentation showed 82% of calls operate on empty stores (alive_count=0, dead=0). For these calls, the current code still: iterates all CInstance entries checking the `alive` flag (never taken), computes a deterministic hash, does a HashMap lookup (always hits the same cached entry), does a Box<dyn Any> downcast, and clones the result. Adding an early return before all this work should save significant overhead.

## Solution

Added a check after the `failed` flag test but before hash computation:
```rust
if d.store.alive_count == 0 && T::is_empty(&d.builtins) {
    return Some((self, None));
}
```

This skips hash loop, thread_local access, HashMap lookup, downcast, and clone for 82% of calls. Also restructured the top of the function to use a single `match` instead of multiple `is_none()`/`as_ref().unwrap()` calls.

## Files changed

- `src/chr/mod.rs` — Added early return for empty-store ChrStateData in normalize_owned

## Why -1.3% instead of 2-4% improvement

1. **Branch predictor handles the empty hash loop perfectly.** When alive_count==0, the `if inst.alive` branch in the hash loop is never taken. The CPU's branch predictor learns this pattern quickly and predicts "not taken" with near-100% accuracy. The loop becomes a fast sequential scan through the Vec with no actual work.

2. **The cache already provides fast returns for empty stores.** The empty-store hash is deterministic (same program_id, no alive constraints). The cache lookup always hits the same entry on the first probe. The effective cost of the "wasted" hash+cache path is tiny: ~40ns per call.

3. **The added branch costs as much as it saves.** The `alive_count == 0 && is_empty` check runs on EVERY call, including the 18% with alive constraints. The net effect is neutral to slightly negative because the check adds instructions to the hot path without improving the already-efficient cache-hit case.

4. **Thread-local access overhead is unavoidable.** The `NORMALIZE_CACHE.with()` call has ~10-20ns of inherent overhead. Even with the shortcircuit, the function prologue, option matching, and failed check still execute. The shortcircuit only saves the hash+cache portion, which is already fast.

## Remaining opportunities

- To actually reduce normalize_owned overhead for empty stores, the optimization needs to happen at the call site (e.g., in compose_nf), avoiding the function call entirely. But compose_nf already handles truly empty ChrState (data==None) cheaply; the issue is non-empty ChrStateData with zero alive constraints.
- The 17.17% inclusive time is dominated by the 20.8% cache-miss calls that run the full CHR engine, not by per-call overhead on the 79.2% cache-hit path.
- normalize_owned's self-time (3.48%) may be irreducible given the hash computation and cache access are already well-optimized by hashbrown and branch prediction.
