# Investigation: Speculative Normalize Cache Probe to Skip apply_subst

## Summary

Added a speculative normalize cache probe that attempts to compute the cache key without calling apply_subst. Resulted in a statistically significant regression on treecalc_synth_flip due to 98.6% bail rate.

**Baseline:** 385.35ms (median, all values: 389.56, 382.80, 384.85, 388.51, 384.28, 386.80, 385.85, 387.83, 382.65, 381.24)
**After:** 392.49ms (median, all values: 397.79, 388.08, 399.70, 386.00, 391.90, 393.10, 386.26, 396.08, 391.88, 393.25)
**Improvement:** -1.9% (regression)
**Mann-Whitney U:** 10/100 (significant regression)
**Regression:** Self is the regression

## Problem

In `compose_nf`, after matching succeeds, the constraint pipeline does `apply_subst` + `combine_owned` + `normalize_owned`. The normalize cache has a ~79% hit rate, meaning most of that expensive work (apply_subst at 1.97% + combine_owned at 0.59% = 2.56% of runtime) is wasted on cache hits.

## Solution

Added a speculative probe path in the constraint pipeline:

1. Before calling `apply_subst`, resolve each constraint argument through the substitution's variable chain using `resolve_var_chain_unlocked` — cheap pointer chasing, no term creation
2. If all args resolve to simple terms (ground or inline), compute the normalize cache key from the resolved args
3. Check the cache: on hit, skip the entire `apply_subst` + `combine_owned` pipeline
4. On miss or bail (args resolve to non-ground compound terms), fall through to the normal path

Implementation added:
- `resolve_arg_through_subst` — resolves a TermId through a Subst via variable chain walking
- `speculative_normalize_combined` trait method on `ConstraintOps`
- `speculative_normalize_combined_impl` on `ChrState` — computes hash from resolved args and probes cache

## Why -1.9% instead of +2%

**98.6% bail rate.** Debug instrumentation revealed per ~6 iterations:
- 22,533 cache hits (speculative probe succeeds)
- 1,960 cache misses (speculative probe computes key, but cache misses)
- 1,787,107 bails (speculative probe cannot resolve args cheaply)

The bail happens because constraint args are typically variables that resolve through the substitution chain to non-ground compound terms (App nodes with unresolved variables inside). The `resolve_arg_through_subst` function correctly identifies these as cases where it cannot determine the final TermId without a full tree walk + term creation, and bails.

When the probe does NOT bail, the cache hit rate is 92% (excellent), but this path is reached only 1.4% of the time. The other 98.6% pays the overhead of the speculative resolution attempt for nothing.

**Quantitative ceiling**: Even with a 100% hit rate and zero probe overhead, maximum savings = 2.56% * 79% = ~2.0%. With N=10 samples, effects below ~3-5% are hard to detect. This optimization was always close to the measurement floor.

### Key design decisions

1. **Variable chain resolution** — Chose `resolve_var_chain_unlocked` (pure pointer chasing) over `apply_subst` (full tree walk) for the speculative path. This made the probe cheap on bail, but also meant it could only handle simple resolutions.
2. **Conservative bail** — Bail on any non-ground compound term. This is correct but means the probe almost never succeeds on this workload.

## Files changed

- `src/constraint.rs` — Added `speculative_normalize_combined` trait method
- `src/chr/mod.rs` — Implemented speculative probe with `resolve_arg_through_subst` and `speculative_normalize_combined_impl`
- `src/kernel/compose.rs` — Added speculative probe call before normal constraint pipeline
- `src/bin/perf_corpus_health.rs` — Fixed pre-existing clippy warnings
- `src/bin/perf_corpus_trend.rs` — Fixed pre-existing clippy warnings
- `tests/chrstate_perf_bench.rs` — Fixed pre-existing clippy warning

## Why this and Round 43 both failed

Round 43 (speculative_normalize_probe) attempted the same goal with a different strategy: calling `apply_subst` per-arg. That does the same tree walk as the normal path, saving nothing. This attempt used variable chain resolution instead, but the args are too complex for chain resolution to succeed.

**The fundamental blocker**: For the probe to be useful, it needs to compute the cache key cheaply. But the cache key requires knowing the final TermIds after substitution. When args are non-ground compound terms, the only way to get final TermIds is `apply_subst` — which is the work we're trying to skip.

## Remaining opportunities

- **Structural hashing without interning**: Hash the term tree structure directly (without creating new TermIds) to compute the cache key. This requires a different cache key scheme but avoids the chicken-and-egg problem.
- **Reducing compose successes**: Instead of optimizing the post-match constraint pipeline, reduce the number of matching successes that reach it. Most compose attempts fail at the root functor precheck; further early-exit paths could reduce the volume of constraint work.
- **Close the constraint pipeline investigation**: ChrState::apply_subst (1.97%) + combine_owned (0.59%) = 2.56% of runtime. Two failed attempts at this target. The remaining headroom is ~2%, which is below the practical measurement threshold. Recommend deprioritizing this target.
