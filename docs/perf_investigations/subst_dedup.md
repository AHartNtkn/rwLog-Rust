# Investigation: Per-Call apply_subst Dedup for Hash-Consed Subtree Sharing

## Summary

Attempted to add a per-call FxHashMap<TermId, TermId> result cache to apply_subst_core to avoid re-walking shared subterms in hash-consed term DAGs. DISCARD: ~86% regression (U=0/100). HashMap allocation/lookup overhead per invocation far exceeds any savings from avoided subtree traversal.

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 211016 us (median, all values: 210927, 212244, 210223, 208716, 213086, 212836, 206596, 211016, 209818, 212869)
**After:** 389224 us (median, all values: 396246, 392012, 393804, 389763, 385935, 387473, 384866, 382215, 389224, 380504)
**Improvement:** -86% (catastrophic regression)
**Mann-Whitney U:** 0/100 (complete separation, wrong direction)

## Problem

apply_subst_core walks term trees via a worklist. Since terms are hash-consed (interned), the same TermId can appear as a child of multiple App nodes, making the logical tree actually a DAG. The hypothesis was that caching `TermId -> TermId` results within a single call would avoid redundant subtree traversal.

## Approach

Added a local `FxHashMap<TermId, TermId>` at the start of `apply_subst_core`. Before visiting each non-ground, non-inline term, checked the cache. On completing a visit, inserted the result. Only cached store-ref terms (not ground or inline).

## Why It Failed

1. **HashMap overhead dominates**: Creating and using an FxHashMap on every apply_subst_core invocation is extremely expensive relative to the actual traversal work. apply_subst is called hundreds of thousands of times per evaluation, and most individual calls involve relatively small terms.

2. **Low intra-call sharing**: While hash-consing creates DAG structure across the global term store, within a single apply_subst call the term being traversed is typically a tree of modest depth/width. The same TermId appearing as a child of multiple App nodes within one call is rare.

3. **Fundamental mismatch**: apply_subst is a hot, tight loop with very low per-node cost (ground bit check, inline var resolution, var_range skip). Any per-call data structure allocation adds unacceptable overhead. The ~86% regression confirms that even FxHashMap (the fastest Rust hash map) is too slow for this use case.

## Files changed

- `src/subst.rs` — Added FxHashMap cache in apply_subst_core (reverted)

## Remaining opportunities

- apply_subst improvements must be zero-allocation and leverage existing data structures
- The var_range skip (subst_var_range, 36.5% improvement) already captures the main opportunity by skipping entire subtrees at the metadata level
- Cross-call caching was previously tried (apply_subst_memo, U=62) and also failed due to fingerprint overhead
- The apply_subst design space appears increasingly exhausted — remaining improvements likely need to come from reducing the NUMBER of apply_subst calls (e.g., lazy substitution) rather than making individual calls faster
