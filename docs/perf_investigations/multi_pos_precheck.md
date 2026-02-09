# Investigation: multi_pos_precheck

**Status:** DISCARD
**Round:** 20
**Date:** 2025-02-09

## Hypothesis

The existing root functor precheck (from Round 18) only checks position 0 of build/match patterns. Extending to check ALL positions should catch an additional 5-15% of compose failures that have compatible first-position functors but incompatible later positions, saving the cost of collect_tensor + matching for those calls.

## Changes Made

- `src/kernel/compose.rs`: Extended the root functor precheck loop to iterate over all pattern positions (not just position 0), comparing root functors at each position.

## Measurement

### Primary: treecalc_synth_flip
**Baseline median:** 2302833us
**Optimized median:** 2294194us
**U = 56/100 — DISCARD (not statistically significant)**

## Analysis

The optimization showed no significant improvement because most NFs in the treecalc_synth_flip workload are arity-1 (single match pattern, single build pattern). For arity-1 NFs, the multi-position check degenerates to the same single-position check already in place.

The few multi-arity NFs that do exist either:
1. Already fail at position 0 (caught by existing precheck)
2. Have variable-rooted later positions (which must be skipped by the precheck since variables can match anything)
3. Have compatible functors at all positions but fail deeper in the pattern structure

The -0.38% measured change is within noise (U=56 is close to the null hypothesis U=50).

## Remaining Opportunities

- **Deeper structural precheck**: Instead of just root functor, compare the first 2-3 levels of pattern structure. This would catch failures where both sides start with the same functor but differ in child structure.
- **Arity-based filtering for multi-arity workloads**: The multi-position precheck may be valuable for workloads with higher-arity NFs. Worth re-evaluating if such workloads emerge.
