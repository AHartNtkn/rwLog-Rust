# Investigation: Top-Constructor Fast-Rejection in compose_nf

## Summary

Added a top-level constructor mismatch prefilter to compose_nf to skip expensive tree-walking matching when top-level constructors differ. No statistically significant improvement.

**Verdict:** DISCARD
**Result:** U=72/100 (run 1), U=43/100 (run 2) — both below threshold of 73.

## Problem

compose_nf calls match_term_lists_shifted for every composition attempt. The hypothesis was that checking top-level constructors of a.build_pats vs b.match_pats could cheaply reject many failed matches without walking the full term tree.

## Approach

Added `top_constructor_mismatch` function that iterates paired build_pats/match_pats, reads the top-level Term node via TermStore::read_lock, and returns true if both are App nodes with different functor symbols.

## Results

### Primary Workload: recursive_even_backward_first64
- Run 1: U=72/100, 3.18% improvement (borderline, below threshold)
- Run 2: U=43/100, -2.48% (noise, no improvement)

## Why It Failed

1. **Small constructor vocabulary.** The even/odd workload uses s, z, cons — most compose failures match at the top but fail deeper in the structure.
2. **Only 378 compose attempts** total for 64 answers. Even 50% early rejection saves negligible work vs ~14ms total.
3. **read_lock overhead.** The prefilter acquires a read_lock on TermStore for every compose call, adding overhead even to calls that pass the check.

## Insights

Top-constructor rejection would help workloads with diverse constructor vocabularies where many different top-level functors compete. The current primary benchmark has a focused constructor set where most compose attempts are "close misses."
