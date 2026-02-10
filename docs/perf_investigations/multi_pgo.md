# Investigation: Multi-Workload Profile-Guided Optimization (PGO)

## Summary

Balanced multi-workload PGO training produced a 3.9% regression on treecalc_synth_flip, making it WORSE than the LTO-only baseline. DISCARDED.

**Baseline:** 74555.361 us (median, all values: 74555.361, 74137.411, 75965.074, 77599.106, 74589.414, 74638.476, 73896.457, 74816.089, 73490.371, 73339.478)
**After:** 77322.170 us (median, all values: 74416.441, 80125.295, 77322.170, 82098.476, 74856.003, 76164.329, 77589.115, 79551.270, 77790.400, 76193.011)
**Improvement:** -3.9% (regression)
**Mann-Whitney U:** 12/100 (p < 0.0001, significant regression)
**Regression:** Primary workload itself regressed

## Problem

Single-workload PGO (Round 44) showed a massive 14.0% improvement on treecalc_synth_flip but was DISCARDED due to a 3.2% regression on recursive_even_backward_first64. The hypothesis was that balanced PGO training (equal weight on both workloads) could capture most of the 14% primary improvement without the secondary regression.

## Solution

Used LLVM PGO pipeline with balanced training:

1. Built with `-Cprofile-generate=/tmp/pgo-data` to instrument the binary
2. Ran treecalc_synth_flip 3x AND recursive_even_backward_first64 3x to collect profiles
3. Merged profiles with `llvm-profdata merge`
4. Rebuilt with `-Cprofile-use=/tmp/pgo-data/merged.profdata`

### Key design decisions

1. Equal training weight: 3 runs of each workload (vs 3:1 ratio in Round 44's single-workload PGO).
2. Same base profile as Round 44 (lto=true, codegen-units=1).

## Files changed

- `.cargo/config.toml` (new in worktree) -- PGO RUSTFLAGS
- `scripts/build_pgo.sh` (modified in worktree) -- balanced training script

## Why regression instead of improvement

The balanced training diluted the profile data, producing conflicting branch prediction hints. treecalc_synth_flip is compose-heavy (63775 composes, 2922 steps) while recursive_even_backward_first64 is step-heavy (4793 steps, 378 composes). These exercise opposing code paths:

- compose-heavy: apply_subst hot, matching hot, constraint pipeline hot
- step-heavy: FixWork stepping hot, tabling lookups hot, answer replay hot

When PGO tries to optimize for both, the branch predictor hints become ambiguous -- neither workload's hot paths get clear optimization signals. The result is worse than LTO's static analysis, which at least makes consistent decisions without conflicting runtime data.

This is the fundamental PGO training dilemma: single-workload training produces large gains but risks regression on other workloads; balanced training produces no gains (or regression) because it can't commit to any optimization direction.

## Remaining opportunities

- **Workload-specific PGO builds**: If only the primary workload matters, single-workload PGO provides 14% improvement. Could ship PGO profiles alongside the release build.
- **BOLT post-link optimization**: Reorders functions for instruction cache utilization without conflicting branch hints. May be more workload-agnostic than PGO.
- **PGO appears fundamentally incompatible with multi-workload optimization for this codebase** due to the opposing hot path profiles.
