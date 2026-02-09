# Investigation: term_intern_cache

**Status:** DISCARD
**Round:** 13
**Date:** 2025-02-09

## Hypothesis

Term interning via intern_unlocked drives ~7.7% of runtime through HashMap operations (get_inner 4.9%, insert 1.5%, rehash 1.3%). A direct-mapped cache (64 entries) for recently interned terms should intercept repeat lookups and skip HashMap access.

## Changes Made

- `src/term.rs`: Added `InternCache` (64-entry direct-mapped cache) to TermStore. Added cache lookup to `var_unlocked` and `app_from_slice_unlocked`.

## Measurement

### Primary: recursive_even_backward_first64
**U = 50/100 — DISCARD (no improvement)**

## Analysis

The cache showed no measurable improvement because existing optimizations already eliminate most repetitive interning:
- `var_unlocked` already has a `var_cache: Vec<Option<TermId>>` that provides O(1) lookup for previously seen variable indices
- `apply_var_renaming` uses an `all_same` check to avoid unnecessary intern calls when children haven't changed
- `apply_subst_core` similarly avoids re-interning unchanged subtrees

The remaining intern calls are mostly for genuinely new terms (new substitution results, new constructor applications) that wouldn't benefit from a small cache since they're unique. The profile's 7.7% hashmap overhead is irreducible cost of hashconsing — the cache adds overhead (hash computation + comparison) that roughly equals the savings from cache hits.

## Remaining Opportunities

- **Arena-based term storage:** Replace hashconsing entirely with structural equality checks during matching. This would eliminate all intern overhead but requires architectural changes to how terms are compared.
- **Batch interning:** Collect all terms to be interned during a substitution pass and intern them in a single batch, improving cache locality for the HashMap operations.
