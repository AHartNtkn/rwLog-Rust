# Investigation: Multi-Target Codebase Simplification Round 2 (Consolidation)

## Summary

Reduced public API surface in nf.rs with 5 visibility tightening changes. No performance regression.

**Full corpus U:** 50/100 (neutral, consolidation threshold: U > 27)
**treecalc_synth_flip U:** 64/100 (no regression)
**Verdict:** KEEP

## Changes

### nf.rs API Surface Reduction

- `collect_vars_ordered`: `pub` → `pub(crate)` (only used from kernel/util.rs, chr/mod.rs)
- `collect_vars_ordered_list`: `pub` → `fn` (private, only used within nf.rs)
- `renumber_vars`: `pub` → `pub(crate)` (only used within crate)
- `SubstParams` struct: `pub` → `pub(crate)` (only used from kernel/compose.rs)
- `factor_tensor_with_subst`: `pub` → `pub(crate)` (only used from kernel/compose.rs)

## Surveyed But Not Changed

- **kernel/util.rs**: Already `mod util` (private module), no public API to reduce
- **engine.rs**: No dead public functions found
- **matching.rs**: Only `match_terms_disjoint` is pub (used by integration tests)
- **drop_fresh.rs**: Test-only methods exist but `#[cfg(test)]` gating caused layout-sensitive performance noise on treecalc_synth_flip — reverted

## Key Insight

The codebase is well-maintained after the first simplification round (-608 lines). Remaining cleanup opportunities are limited to minor visibility changes and documentation improvements. The `#[cfg(test)]` gating approach for removing test-only code from release builds is unreliable due to code layout sensitivity in treecalc_synth_flip benchmarks.

## Files Changed

- `src/nf.rs` — 5 visibility reductions (pub → pub(crate) or private)
