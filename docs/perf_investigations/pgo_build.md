# Investigation: Profile-Guided Optimization (PGO)

## Summary

LLVM Profile-Guided Optimization showed a massive 14.0% improvement on treecalc_synth_flip (U=100/100, complete separation) but was DISCARDED due to a 3.2% regression on recursive_even_backward_first64 (U=13/100).

**Baseline:** 73546.954 us (median, all values: 76231.147, 73429.980, 73663.929, 77334.744, 71927.943, 75334.563, 76938.150, 72371.738, 73099.950, 72714.513)
**After:** 63240.127 us (median, all values: 63463.841, 61883.694, 65001.661, 65512.599, 62863.960, 64882.748, 63270.664, 62004.015, 63209.590, 63004.356)
**Improvement:** ~14.0% on primary (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001, complete separation)
**Regression:** +3.2% on recursive_even_backward_first64 (U=13/100, significant regression)

## Problem

After 43+ rounds of code-level optimization, the remaining hotspots (apply_subst at 38.45%, exec_body_inline at 9.35%) are dominated by irreducible computation that cannot be improved through code changes. The hypothesis was that compiler-level optimization via PGO — which provides branch prediction hints, function layout optimization, and better inlining decisions based on actual execution profiles — could unlock improvements unreachable through source code changes alone.

## Solution

Used LLVM PGO pipeline:

1. Built with `-Cprofile-generate=/tmp/pgo-data` to instrument the binary
2. Ran treecalc_synth_flip 3x and recursive_even_backward_first64 1x to collect profiles
3. Merged profiles with `llvm-profdata merge`
4. Rebuilt with `-Cprofile-use=/tmp/pgo-data/merged.profdata`

### Key design decisions

1. Training workload was primarily treecalc_synth_flip (3 runs) with 1 run of the secondary benchmark.
2. Used the existing release profile (lto=true, codegen-units=1) as the base for PGO builds.
3. Created a `scripts/build_pgo.sh` automation script for reproducibility.

## Files changed

- `scripts/build_pgo.sh` (new) — PGO build automation script

## Why regression on secondary workload

PGO optimizes hot paths at the expense of cold paths. The training was dominated by treecalc_synth_flip (compose-heavy: 63775 composes, 2922 steps) which exercises apply_subst, normalize_owned, combine_owned, and the constraint pipeline. The secondary benchmark recursive_even_backward_first64 is step-heavy (4793 steps, only 378 composes) and exercises different code paths that PGO deprioritized.

The 3.2% regression on the secondary workload (U=13) exceeds the regression threshold (U <= 27), requiring DISCARD per protocol.

## Remaining opportunities

- **Multi-workload PGO training**: A PGO training set that includes equal weight for both treecalc_synth_flip and recursive_even_backward_first64 could potentially capture most of the 14% primary improvement without the secondary regression.
- **BOLT post-link optimization**: After PGO, BOLT (Binary Optimization and Layout Tool) could further improve instruction cache utilization. BOLT may be less prone to cross-workload regression since it primarily reorders functions.
- **Workload-specific PGO builds**: If only the primary workload matters, PGO provides a massive 14% improvement that dwarfs all code-level optimizations attempted in recent rounds.
- The 14% improvement confirms that a significant portion of the remaining overhead is due to suboptimal branch prediction and code layout, not algorithmic inefficiency.
