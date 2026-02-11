# Investigation: Mega-Stack (All R46 Micro-Optimizations Combined)

## Summary

Combining all four R46 micro-optimizations into a single mega-stack produced only 1.05% improvement (worse than the individual R46 candidates), failing to reach significance. DISCARDED.

**Baseline:** 70231.115 us (median, all values: 74410.984, 69419.287, 70079.129, 69040.255, 69611.349, 70615.174, 70465.778, 70621.126, 69719.193, 70383.102)
**After:** 69495.296 us (median, all values: 69225.487, 70989.801, 69153.277, 68758.347, 69765.106, 70272.459, 68689.394, 69145.777, 70761.789, 74079.339)
**Improvement:** ~1.05% (not significant)
**Mann-Whitney U:** 61/100 (p > 0.1, not significant)
**Regression:** N/A (primary failed threshold)

## Problem

R46's two candidates (stacked_micro_opts_2 at U=70/1.73% and subst_smallvec at U=69/1.10%) both showed directional improvements but individually failed to cross the U>=73 threshold. The hypothesis was that combining all 4 changes would produce additive ~2.5-3.0% improvement.

## Solution

Four changes implemented together:

1. **#[inline(always)] on resolve_var_chain_unlocked** — Force-inline the variable chain resolution in the 38% apply_subst hotspot
2. **SmallVec<[usize; 8]> for compose indices** — Eliminate Vec allocation for compatible index lists
3. **Cached root functor in NfInner** — Avoid terms.get_unlocked() per compose_nf precheck
4. **SmallVec<[Option<TermId>; 16]> for Subst bindings** — Eliminate heap allocation for substitutions

## Files changed

- `src/subst.rs` — #[inline(always)] + SmallVec for Subst
- `src/work/compose.rs` — SmallVec for compose indices + cached root tag usage
- `src/nf.rs` — cached_build_root/cached_match_root in NfInner
- `src/kernel/compose.rs` — Use cached root functors in precheck

## Why 1.05% instead of 2.5-3.0%

The changes are not additive — they interfere:

1. **NfInner enlargement hurts cache locality**: Adding cached_build_root and cached_match_root to NfInner increases the Arc<NfInner> allocation size. Since NFs are cloned, stored in seen lists, and compared frequently, the larger allocation worsens cache behavior on the compose hot path.

2. **SmallVec<[Option<TermId>; 16]> is too large**: At 128 bytes inline (16 × 8 bytes per Option<TermId>), the Subst struct is 5× larger than Vec's 24 bytes. This increases stack frame sizes in the matching function and causes cache pressure when multiple Substs are alive simultaneously.

3. **The individual R46 U values (70 and 69) may have been optimistic**: If the true effect of each change is ~0.5% rather than ~1.5%, combining them yields ~2% which is still below detection at N=10 with ~2% CV.

## Remaining opportunities

- **The stacking approach has reached diminishing returns** for this codebase. Individual micro-optimizations produce <2% effects that cannot be reliably measured at N=10.
- **Smaller SmallVec capacity**: SmallVec<[Option<TermId>; 4]> or SmallVec<[Option<TermId>; 8]> for Subst would reduce stack pressure while still covering most cases.
- **The optimization frontier is approximately reached**: After 47 rounds and 70+ sub-investigations, treecalc_synth_flip has been optimized from ~840ms to ~70ms (12× speedup). The remaining ~70ms is dominated by irreducible computation (term tree walks, hash table lookups, CHR solving).
