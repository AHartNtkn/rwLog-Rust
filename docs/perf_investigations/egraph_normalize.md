# Investigation: E-Graph-Based NF Structural Dedup

## Summary

Investigated e-graph-based NF deduplication via skeleton (structural shape) equivalence. DISCARD: skeleton overlap is high (up to 89% in recursive workloads) but does not translate to cacheable compose/meet result dedup because NFs with identical skeletons have different variable content, producing unique results. Combined with prior data (compose_memo 0.02%, compose_dedup 0%), this closes the e-graph NF normalization approach.

## Problem

The hypothesis was that NFs with structurally equivalent shapes (same root functors, arities, DropFresh shapes) but different variable content might be normalized into equivalence classes via e-graph equality saturation, enabling compose/meet result reuse across the equivalence class.

## Why It Failed

1. **High skeleton overlap, zero cacheable overlap.** Instrumentation across 7 workloads showed skeleton overlap up to 89% (even/odd first 10) and 75% (addition). But prior investigations proved 0.02% full NF pair duplication (compose_memo) and 0% compose result duplication (compose_dedup).

2. **Variable content differences are genuine, not naming differences.** Same-skeleton NFs at different recursion depths have progressively deeper/different terms flowing through. `B(A(A(0)),1)` vs `B(A(0),1)` are genuinely different computations, not equivalent under any normalization.

3. **Alpha-canonical forms already eliminate naming differences.** factor_tensor produces canonical variable numbering (0..n-1 in first-occurrence order). E-graph normalization would only help with structural equivalences beyond alpha-renaming, but those don't exist in this workload.

4. **Meet skeleton overlap is low (11%).** Meet operations use more diverse structural patterns, further limiting potential for skeleton-based dedup.

## Skeleton Overlap Data

| Workload | Compose Attempts | Unique Skeletons | Skeleton Dedup | Meet Attempts | Meet Unique |
|---|---|---|---|---|---|
| add 2+3 | 7 | 4 | 43% | 0 | 0 |
| add backward sum=3 | 12 | 5 | 58% | 0 | 0 |
| add 5+5 | 16 | 4 | 75% | 0 | 0 |
| add backward sum=5 | 20 | 5 | 75% | 0 | 0 |
| even/odd first 10 | 36 | 4 | 89% | 0 | 0 |
| graph reach 5 nodes | 20 | 10 | 50% | 0 | 0 |
| meet f & g | 0 | 0 | - | 9 | 8 |

## Files changed

None in final state — instrumentation was temporary.

## Remaining opportunities

- E-graph NF normalization is a dead end — skeleton overlap doesn't translate to cacheable dedup
- The compose/meet caching design space is exhausted: input memoization (0.02%), result dedup (0%), skeleton-based normalization (no cacheable overlap)
- Future compose/meet improvements must focus on reducing the number of attempts (shape_predict approach) or making individual attempts cheaper, not caching results
