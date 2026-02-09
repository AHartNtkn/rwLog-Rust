# Investigation: compose_result_memo

**Status:** DISCARD
**Round:** 14
**Date:** 2025-02-09

## Hypothesis

compose_nf is called 378 times per query. If many calls involve the same NF pairs (from different search tree branches), a memo cache keyed by (left_hash, right_hash) could skip re-computation of factor_tensor (3.7%), apply_subst (5.9%), and matching.

## Changes Made

- `src/term.rs`: Added type-erased compose cache to TermStore
- `src/kernel/compose.rs`: Added cache lookup/insert around compose_nf_impl
- `src/constraint.rs`: Added `'static` bound to ConstraintOps

## Measurement

### Primary: recursive_even_backward_first64
**U = 35/100 — DISCARD (~1.1% regression)**

## Analysis

The hypothesis is FALSE. All 378 compose calls produce unique NF pairs — 0% cache hit rate. The DiagonalJoin already deduplicates NFs by hash on each side (via `seen_l_set`/`seen_r_set`), so within a single compose node, each (left, right) pair is composed exactly once. Across different compose nodes in the search tree, the NF pairs are also unique — search tree branches produce distinct intermediate NFs that don't recombine into the same pairs.

The cache adds only overhead: type-erased Any downcast, hash key computation, HashMap lookup/insert on every compose call — producing a slight regression.

## Remaining Opportunities

- **Cross-query caching:** If the same relations are queried repeatedly, cross-query memoization could help. But single-query optimization is the current target.
- **Compose fusion:** Instead of caching results, fuse multiple compose operations into a single pass to avoid intermediate NF materialization.
