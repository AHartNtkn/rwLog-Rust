# Investigation: target-cpu=native

## Summary

Building with `-Ctarget-cpu=native` to enable AVX2 and other CPU-specific instructions showed no statistically significant improvement. DISCARDED.

**Baseline:** 72206.215 us (median, all values: 72210.818, 74283.760, 72436.554, 69437.333, 70952.113, 71306.905, 73930.577, 72206.215, 69644.580, 70301.050)
**After:** 71341.868 us (median, all values: 70454.174, 75092.628, 70620.155, 71649.314, 72138.860, 73024.880, 70325.595, 70021.121, 70461.106, 71341.868)
**Improvement:** ~1.2% (within noise)
**Mann-Whitney U:** 53/100 (not significant, p > 0.3)
**Regression:** N/A (primary failed threshold)

## Problem

The default Rust target (`x86_64-unknown-linux-gnu`) only uses SSE2 instructions. Modern CPUs support AVX2 and other extensions that could theoretically improve performance through wider SIMD operations, better instruction selection, and more efficient memory operations.

## Solution

Added `-Ctarget-cpu=native` to RUSTFLAGS to enable all CPU-specific instruction set extensions available on the build machine.

### Key design decisions

1. Applied via `.cargo/config.toml` and `pinned_env.sh` to ensure both build and benchmark use native instructions.
2. Verified the flag had effect: `objdump` showed 14,721 AVX2 instructions in the native binary vs only 2 in the baseline.

## Files changed

- `.cargo/config.toml` (new in worktree) -- RUSTFLAGS with target-cpu=native
- `scripts/perf/pinned_env.sh` (modified in worktree) -- added target-cpu=native to RUSTFLAGS

## Why no improvement

Despite generating 14,721 AVX2 instructions (vs 2 in baseline), the treecalc_synth_flip workload is dominated by pointer-chasing patterns that don't benefit from wider SIMD:

1. **Hash table probing**: hashbrown's SwissTable uses SIMD for group probing, but groups are 16 bytes (SSE2-width). AVX2's 32-byte registers provide no benefit for 16-byte probes.

2. **Term tree traversal**: apply_subst walks term trees via TermId indices into a Vec. This is pointer-chasing through indirect indices -- memory latency bound, not compute bound.

3. **SmallVec operations**: Most hot-path data structures use SmallVec with small inline capacities (4-8 elements). Operations on these are scalar register operations, not SIMD-vectorizable.

4. **Branch-heavy control flow**: CHR matching, pattern matching, and substitution involve many conditional branches. SIMD excels at data-parallel operations on contiguous arrays, not branchy decision logic.

The 1.2% median difference (U=53/100) is indistinguishable from measurement noise. U=53 is essentially coin-flip territory (50 = no difference).

## Remaining opportunities

- **target-cpu=native is not worth pursuing** for this codebase. The workload is fundamentally latency-bound (pointer chasing, hash table lookups, tree walks) rather than throughput-bound (data-parallel computation).
- Future optimization should focus on reducing WORK (algorithmic improvements) rather than doing the same work faster at the instruction level.
- The stacking approach (combining borderline micro-optimizations) remains the most viable strategy for incremental gains.
