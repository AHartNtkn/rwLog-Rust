# Investigation: Identity/Annihilator NF Propagation

## Summary

Investigated NF/Kernel backlog item 9 — identity/annihilator propagation to skip trivial composes. DISCARD: identity NFs occur in only 0.2% of compose_nf calls, far below threshold for meaningful impact.

## Problem

Hypothesis: some NFs are structurally identity (match_pats == build_pats, identity DropFresh, no constraint). Composing with identity is a no-op. If identity NFs are common, short-circuiting compose_nf could save significant work.

## Instrumentation Results

On treecalc_synth_flip (the dominant workload):
- **Total compose_nf calls:** ~277,985
- **a is identity:** 582 (0.2%)
- **b is identity:** 34 (0.0%)
- **Either is identity:** 616 (0.2%)

On secondary workloads (recursive_even, sequence_chain): compose volumes too small to matter (378 and 4,096 calls respectively).

## Why Identity NFs Are Rare

The engine's factoring and normalization pipeline inherently avoids producing identity NFs. Rules that are structurally identity get simplified away earlier in the pipeline. The 0.2% frequency means even perfect elimination of identity compose costs would save at most ~556 compose calls out of 278K — completely negligible.

## Files Changed

None (instrumentation only, reverted).

## Insights

- Identity NFs are exceedingly rare in practice due to upstream normalization.
- The root functor precheck already provides O(1) rejection for the vast majority of failing compose pairs. Identity NFs bypass this precheck (identity matches anything), but their rarity makes this irrelevant.
- Annihilator NFs would be even rarer since contradictory patterns are not naturally produced by the factoring pipeline.
- This direction is exhausted — no further identity/annihilator work is warranted.
