# Investigation: Deep Functor Indexing for treecalc_synth_flip (Major Proposal 8)

## Summary

Attempted to reduce compose pair explosion in treecalc_synth_flip via multi-level functor indexing in DiagonalJoin. DISCARDED: both approaches (DeepTag linear scan U=42, HashMap TagIndex U=34) showed slight regression. The structural indexing design space is exhausted for this workload.

**Approach 1 (DeepTag linear scan):**
**Baseline:** 384,816 us (median, all values: 379643, 376161, 383987, 385645, 378751, 385958, 382021, 402809, 396020, 401262)
**After:** 389,437 us (median, all values: 397997, 384252, 399052, 385868, 375878, 385826, 383063, 393733, 395686, 393005)
**Mann-Whitney U:** 42/100 (not significant, slight regression)

**Approach 2 (HashMap TagIndex):**
**Baseline:** 390,011 us (median, all values: 390498, 395812, 389330, 387549, 388612, 383644, 389524, 392971, 396351, 399752)
**After:** 394,762 us (median, all values: 396912, 390268, 377037, 391102, 389069, 393217, 396306, 400026, 398367, 398829)
**Mann-Whitney U:** 34/100 (not significant, slight regression)

**Verdict:** DISCARD

## Problem

treecalc_synth_flip performs 277,985 compose attempts with ~99% failure rate (only ~2,800 succeed). The existing root functor indexing already reduced attempts from ~324K to ~278K but 276K failures remain. The hypothesis was that deeper (depth 1-2) functor indexing would filter more incompatible pairs before compose_nf.

## Approaches

### Approach 1: DeepTag with linear scan

Extended `RootTag` to a `DeepTag` struct with `(root, child0, child1)` functor signatures. `compatible_*_indices` filters by all three levels. Reduced compose attempts from 277,985 to 262,503 (~5.6% reduction, ~15.5K fewer).

### Approach 2: HashMap TagIndex

Added `TagIndex` struct mapping root tag to NF index lists for O(1) root lookup, with child-level deep tag filtering on HashMap results. Same compose attempt reduction (~15.5K fewer).

## Why It Failed

1. **Tiny functor vocabulary:** Tree calculus uses only 3 functors (K, S, App). Root-level filtering already catches most structural mismatches.

2. **Variable-heavy children:** Most NFs that pass root filtering have variable-headed children (Wildcard at child0/child1). Wildcard is compatible with everything, so depth-1/2 checks can't filter them.

3. **Marginal filtering power:** Deep tags only reduce attempts by ~5.6% (278K → 262K). At ~1.4us per compose_nf, that saves only ~22ms on a ~400ms benchmark.

4. **Overhead exceeds savings:** Deeper tag extraction (3 term store lookups per NF arrival) and comparison (3 tags per iteration vs 1) costs more than the ~15.5K avoided compose_nf calls save.

5. **Confirms prior investigations:** Consistent with depth2_precheck (U=59), multi_pos_precheck (U=56), and nf_functor_sig (which only helped via lock-free access, not deeper checking). The compose precheck/indexing design space is exhausted for treecalc_synth_flip.

## Files Changed (not merged)

- `src/work/mod.rs` — DeepTag struct, extraction functions
- `src/work/compose.rs` — TagIndex HashMap, DeepTag integration

## What Would Actually Help treecalc_synth_flip

The 278K compose attempts with 99% failure rate cannot be reduced by structural indexing because failures share structural signatures at all cheaply-checkable depths. The remaining opportunities are:

- **Work avoidance at the scheduling level**: Avoid generating compose pairs entirely — e.g., semi-naive for the meet/conjunction path, or memoization of compose results across DiagonalJoin instances
- **Faster compose_nf failure path**: The current ~1.4us per failed compose includes matching setup, term store access, and substitution allocation. If failures could bail out earlier in the matching algorithm (not just at the functor level), this would help.
- **PGO (Profile-Guided Optimization)**: Previously showed 14% improvement on synth_flip (U=100) but 3.2% regression on even64. If the regression could be mitigated, PGO would be the single largest remaining lever.
- **Constraint-state canonicalization (Major Proposal 9)**: If identical constraint states across branches become pointer-identical, dedup/caching can avoid redundant work at a higher level than compose indexing.
