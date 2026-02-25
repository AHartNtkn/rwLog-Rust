# Investigation: Compose Chain Fusion — Reinvestigation with Targeted Benchmark

## Summary

Reinvestigation of compose_chain_fuse with inline_amplification_256 as primary benchmark. KEEP: 34.7% improvement (U=100/100), no regression on full corpus.

**Baseline:** 948.7 us (median, all values: 1316.7, 1331.8, 1293.7, 944.2, 948.4, 946.9, 950.6, 948.9, 942.2, 937.3)
**After:** 619.3 us (median, all values: 622.8, 885.0, 883.6, 599.8, 599.2, 937.1, 605.3, 732.0, 615.0, 615.9)
**Improvement:** ~34.7% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001)
**Regression:** None observed on full corpus (U=38, well above 27)

## Problem

inline_amplification_256 involves 256 chained simple wrapper calls (`$x -> (f $x)`). Each compose_nf call is O(1) but there are 256 of them in sequence. The original investigation showed 38% improvement but was incorrectly discarded due to measuring against the full corpus (U=59) where this workload is only 0.15% of total time.

## Solution

Detect consecutive simple wrapper Calls at the front of the pipeline and fuse them into a single NF in O(n) instead of O(n^2) individual compose_nf calls. A "simple wrapper" is a Call whose body is `Rel::Atom(nf)` where the NF has single match/build patterns, identity DropFresh, and a single variable in the match pattern that appears exactly once in the build pattern.

When a chain of N such wrappers is detected, build the nested term `f_N(f_{N-1}(...f_1(boundary)...))` bottom-up in a single pass, producing one NF instead of N compose_nf calls.

### Key design decisions

1. **Detection at pipeline front only** — wrapper chains only appear at Call-chain boundaries, not in the middle of pipes. Checking only the front avoids overhead elsewhere.
2. **Strict "simple wrapper" criteria** — single match/build pats, identity DropFresh, single-var match. This avoids false positives that would produce incorrect results.
3. **Bottom-up term building** — builds `f_N(...f_1(x)...)` in O(N) by iterating through collected FuncIds and nesting intern calls.

## Files Changed

- `src/work/pipe.rs` — Added `simple_wrapper_func()`, `build_wrapper_chain_nf()`, `try_fuse_wrapper_chain()` (+127 lines)

## Why 34.7% Instead of More

The optimization eliminates 255 of 256 compose_nf calls, but the remaining work includes:
- Pipeline setup and NF construction overhead
- The one remaining compose_nf call to merge the fused wrapper with the boundary
- Engine stepping overhead (though minimal for this case)

## Remaining Opportunities

- **Broader chain patterns**: Non-wrapper chains (multi-variable, ground-to-ground) could benefit from similar fusion but require more complex detection.
- **env.lookup O(n^2)** for sequence_chain_len4096: A separate bottleneck in Env's linear scan, not addressed here.
