# Investigation: Eliminate O(n²) to_vec() in PipeWork::normalize_mid_atoms

## Summary

Added a `mid_normalized` flag to PipeWork that skips redundant normalize_mid_atoms() calls, eliminating O(n²) Arc clone overhead for long sequence chains. ~6.3% total corpus improvement.

**Baseline:** 5,016,894 us (mean, all values: 4920780, 5234970, 4864982, 4944283, 5293257, 4906365, 5001323, 5177545, 4869321, 4956111)
**After:** 4,702,608 us (mean, all values: 4714207, 4552562, 4699570, 4715513, 4860595, 4672193, 4644247, 4624434, 4612854, 4929907)
**Improvement:** ~6.3% (same-session comparison)
**Mann-Whitney U:** 96/100 (p < 0.001)
**Regression:** None observed on treecalc_synth_flip (U=45) or recursive_even_backward_first64 (U=59)

## Problem

`PipeWork::normalize_mid_atoms()` was called on every step and always called `self.mid.to_vec()`, which copies ALL elements from the Factors rope structure into a fresh Vec. For a 4096-element sequence chain, this meant ~4096 + 4095 + ... + 1 ≈ 8.4M Arc clones across all 36,867 steps — O(n²) total work where n is the chain length.

The `sequence_chain_len4096` case consumed 83.8% of total corpus time (4.15s out of 4.96s). Perf profile showed 26% in DiagonalJoin::pull_side_in_place, 25% in step_node, 21% in ComposeWork::step_in_place — all driven by the excessive per-step overhead from normalize_mid_atoms.

## Solution

Added a `mid_normalized: bool` flag to PipeWork that tracks whether the mid factors have already been scanned and found to contain no normalizable structure (no Seq, And, Zero, or adjacent Atom pairs).

### Key design decisions

1. **Dirty flag over rope iteration**: Rather than adding methods to iterate the Factors rope without copying (which was also done as `Factors::iter()`), the dirty flag approach is simpler and more effective — it skips the entire normalization function, not just the allocation.

2. **Conservative invalidation**: The flag is cleared (set to false) whenever elements are pushed into mid or when mid is rebuilt after normalization. Popping from ends preserves the invariant because removing elements cannot introduce new normalizable structure.

3. **Default-true for empty mid**: An empty mid is trivially normalized, so the default PipeWork starts with `mid_normalized: true`.

## Files changed

- `src/work/pipe.rs` — Added `mid_normalized` flag to PipeWork, gated `normalize_mid_atoms` on it, invalidated on push/rebuild
- `src/factors.rs` — Added `iter()` method and `FactorsIter` struct for zero-copy rope iteration
- `src/work/tests.rs` — Fixed struct literal to use constructor (pre-existing)
- `src/bin/perf_corpus_health.rs` — Fixed clippy warnings (pre-existing)
- `src/bin/perf_corpus_trend.rs` — Fixed clippy warnings (pre-existing)
- `tests/chrstate_perf_bench.rs` — Fixed clippy warning (pre-existing)

## Why 6.3% instead of 83%

The initial hypothesis predicted that eliminating to_vec() would reduce sequence_chain_len4096 from ~4.15s to under 100ms. The actual reduction was from ~4.1s to ~3.7s (~10% on that case). The gap is because:

1. **to_vec() was not the only O(n²) cost**: The 36,867 steps × 4097 compose operations involve other per-step work that scales with chain length, including compose_nf calls and DiagonalJoin stepping.
2. **The constant factor of to_vec() was small**: Each Arc clone is ~5-10ns, and the normalization scan itself was cheap. The O(n²) was present but with a low multiplier relative to other per-step costs.
3. **The flag eliminates redundant scans, not the initial scan**: The first call still does the full to_vec() and scan. Subsequent calls skip it via the flag. For steps that follow structural changes (Seq flattening, splits), the flag is properly invalidated.

## Remaining opportunities

- **sequence_chain_len4096 is still 80%+ of total time** (~3.7s). The remaining bottleneck is O(n) compose/step overhead per chain element. Addressing this requires:
  - Plan compilation/caching (Proposal 1 in PERFORMANCE_INVESTIGATIONS.md): compile the 4096-step pipeline into a fused bytecode rather than stepping through one at a time
  - Seq batching: recognize deterministic pipelines and process multiple steps in batch
- **to_vec() in try_split_call_atom_call()**: Still converts full mid to Vec just to check 3 elements. Could be replaced with direct rope access via `Factors::get(idx)`.
