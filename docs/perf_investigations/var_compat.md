# Investigation: Variable-Occurrence Compatibility Precheck

## Summary

Investigated Correctness-Preserving Pruning backlog item 2 — cached root functor fields on NfInner to eliminate get_unlocked() lookups in compose precheck. DISCARD: U=61/100 (not significant), 0.75% improvement.

**Primary workload (treecalc_synth_flip):**
**Baseline:** 414151 us (median, all values: 464969, 583303, 419961, 416628, 414151, 409224, 410874, 407086, 401534, 400134)
**After:** 411046 us (median, all values: 437090, 411359, 414860, 412181, 411046, 409539, 405410, 396244, 402418, 402825)
**U statistic:** 61/100 (not significant)

## Problem

Hypothesis: replacing get_unlocked() term store lookups in compose_nf's root functor precheck with cached u32 fields on NfInner could eliminate ~600K pointer indirections per run.

## Why It Didn't Work

The existing get_unlocked() path is already extremely cheap:
1. `is_inline()` bit check (~0.5ns)
2. `UnsafeCell::get()` pointer cast (~0ns)
3. `Vec::get(idx)` array index (~1ns, single cache-line hit)

Total savings: ~2-3ns × 300K calls = ~0.6-0.9ms, which is <0.2% of the 400ms workload — well within noise.

## Files Changed

None merged (DISCARD).

## Insights

- The compose precheck design space is exhausted for treecalc_synth_flip. This is the third investigation confirming no further precheck gains (after depth2_precheck U=59, multi_pos_precheck U=56).
- get_unlocked() compiles to a raw pointer cast + array index — essentially zero overhead to eliminate.
- Remaining compose_nf avenues: reduce compose attempt COUNT (indexing, caching), optimize success path (~2,800 successes dominate after precheck), or optimize the matching algorithm itself.
