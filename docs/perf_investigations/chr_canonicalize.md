# Investigation: Constraint-State Canonicalization + Global Interning (Major Proposal 9)

## Summary

Attempted to optimize ChrState Hash/PartialEq/combine/normalize with cached hashes, Arc pointer fast-paths, and empty-store shortcuts. DISCARDED: regression on primary benchmark. CHR constraint operations are not the bottleneck for treecalc_synth_flip.

**Baseline:** ~397,652 us (median)
**After:** ~405,570 us (median)
**Mann-Whitney U:** ~0/100 (clear regression — all optimized values exceed most baseline values)
**Verdict:** DISCARD

## Problem

treecalc_synth_flip is 61% of total corpus time (~369ms) with 278K compose attempts at 99% failure rate. The hypothesis was that ChrState operations (Hash via freeze_chr, PartialEq, combine_owned, normalize_owned) were a significant fraction of compose cost, and that caching/interning would reduce this overhead.

## What Was Implemented

1. **Cached hash on ChrState** — eagerly computed `cached_hash: u64` after `normalize_owned`, used in `Hash::hash` to avoid repeated `freeze_chr` calls
2. **Arc pointer fast-path in PartialEq** — same `Arc<ChrStateData>` returns true without `freeze_chr`
3. **Hash mismatch fast-path in PartialEq** — different cached hashes return false without `freeze_chr`
4. **combine_owned fast-paths** — skip full merge when one side has alive_count == 0 and empty builtins
5. **normalize_owned fast-path** — skip when `fixpoint_watermark >= next_cid` and agenda is empty

## Why It Failed

1. **Constraint operations only run on compose successes**: Of 278K compose attempts, 99% fail at the matching step (functor precheck + term matching). Constraint combine/normalize only runs for the ~2,780 successes.

2. **freeze_chr is called once per NF creation**: The NF hash is cached, so subsequent lookups are O(1). Adding a cached hash to ChrState adds an EXTRA freeze_chr + FxHasher call in normalize_owned (~2,780 extra freeze_chr calls that weren't needed before).

3. **Fast-path checks add branch overhead**: Every PartialEq and every combine_owned call now has additional conditional branches in the hot path, even when the fast-paths don't fire.

4. **Net effect**: The overhead of caching exceeds the savings from the fast-paths.

## Key Insight

The CHR constraint system is NOT the bottleneck for treecalc_synth_flip. The existing normalize cache (commutative hash + thread-local HashMap) already eliminates redundant normalization. The 99% compose failure rate is dominated by the matching step, not constraint operations. To improve treecalc_synth_flip further, focus on reducing the NUMBER of compose attempts, not making individual constraint operations faster.

## Files Changed (not merged)

- `src/chr/mod.rs` — Added cached_hash field, Arc pointer fast-path, hash mismatch fast-path, combine/normalize shortcuts

## Raw Timings

| Round | Baseline (us) | Optimized (us) |
|-------|--------------|----------------|
| 1 | 395,943 | 404,983 |
| 2 | 397,652 | 405,835 |
| 3 | 392,098 | 405,570 |
| 4 | 397,692 | 405,951 |
| 5 | 401,467 | 403,778 |
| 6 | 399,220 | 401,870 |
| 7 | 395,176 | 401,946 |
| 8 | 395,469 | 407,188 |
| 9 | 403,643 | 405,974 |
| 10 | 401,354 | 404,474 |

## Remaining Opportunities for Major Proposal 9

- **Full structural interning of ChrState** (hash-consing with ChrStateId) might still help if it eliminates clones entirely, but the evidence suggests constraint operations are too small a fraction of compose cost to matter.
- **Constraint-aware compose filtering** — checking constraint compatibility before attempting compose_nf — is unlikely to help because the 99% failure rate is already caught by functor matching.
- The real remaining lever for treecalc_synth_flip is reducing compose attempt COUNT, not individual attempt cost.
