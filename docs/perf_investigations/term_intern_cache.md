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

## Round 19 Re-investigation (treecalc_synth_flip)

Re-investigated with treecalc_synth_flip as primary workload (HashMap::get_inner was 11.91% of runtime). Added a 64-entry direct-mapped cache to `intern_unlocked` and `app_from_slice_unlocked`. Result: **U=15/100 — actively 1.7% SLOWER**. The cache overhead (hash computation, comparison, cache line pollution) exceeds any savings from cache hits. The treecalc workload creates many unique terms with low repetition, so the cache hit rate is poor and the cache pollutes L1 with entries that are never reused.

## Remaining Opportunities

- **Arena-based term storage:** Replace hashconsing entirely with structural equality checks during matching. This would eliminate all intern overhead but requires architectural changes to how terms are compared.
- **Batch interning:** Collect all terms to be interned during a substitution pass and intern them in a single batch, improving cache locality for the HashMap operations.
