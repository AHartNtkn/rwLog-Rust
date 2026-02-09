# Investigation: Depth-2 compose precheck

## Summary

Attempted to extend the compose_nf root functor precheck to also check the first child's root functor, rejecting mismatches one level deeper. No significant improvement — within noise.

**Baseline:** 1443773us (median, all values: 1432097, 1435099, 1446864, 1445985, 1470637, 1441560, 1438858, 1440338, 1460204, 1472721)
**After:** 1440231us (median, all values: 1439764, 1435102, 1450720, 1422838, 1440697, 1465106, 1435656, 1428614, 1461443, 1448478)
**Improvement:** 0.25% (not significant)
**Mann-Whitney U:** 59/100 (not significant)
**Regression:** N/A

## Problem

`compose_nf_impl` has a 99.14% failure rate on treecalc_synth_flip (~324K attempts, ~2,787 successes). The existing root functor precheck catches most mismatches cheaply, but the remaining failures that pass the root check still enter `collect_tensor` + `match_term_lists_shifted`. The hypothesis was that checking one level deeper (first child's root functor) could reject more failures before the expensive matching path.

## Solution Attempted

In `compose_nf_impl`, after the existing root functor precheck passes, added a depth-2 check: extract the first child of both the left and right terms and compare their root functors. If both are non-variable App terms with mismatched functors, reject immediately.

## Why it failed

1. **The existing root functor precheck is already near-optimal.** It catches the vast majority of structural mismatches. The remaining failures that pass the root check mostly involve variable-headed children where no structural precheck can help.

2. **The depth-2 check adds overhead per call.** Each check requires 2-3 additional memory lookups (term store accesses) costing ~60-90ns each. On the ~324K compose calls, this adds non-trivial overhead that offsets any savings from early-rejecting the few hundred extra calls it catches.

3. **Consistent with previous multi_pos_precheck failure (U=56/100).** That investigation tried extending the precheck across multiple positions (arity > 1) rather than depth. Both approaches fail, confirming that the compose precheck design space is essentially exhausted for this workload.

4. **Instruction cache effects.** Two implementations were tested — one that cloned SmallVecs (U=67/100, ~1%) and one using only Copy types (U=59/100, 0.25%). The "improved" version was worse, suggesting instruction layout perturbation dominates over the actual logic cost.

## Files changed

- `src/kernel/compose.rs` — Added depth-2 child functor precheck in `compose_nf_impl` (reverted, DISCARD)

## Remaining opportunities

- The compose precheck design space appears exhausted. Further compose improvements should target the success path (which runs only ~2,787 times) or the algorithmic structure (avoiding compose attempts entirely via better indexing or caching).
- `collect_tensor` is called even for failures — lazy/streaming collection that aborts early on mismatch could help if many failures pass the root precheck but fail partway through collection.
