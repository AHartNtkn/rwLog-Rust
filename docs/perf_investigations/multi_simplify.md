# Investigation: Multi-Target Codebase Simplification (Consolidation)

## Summary

Multi-target simplification removing 608 lines across 4 files with no performance regression. Unified factor_tensor duplication, removed dead metrics module, cleaned up variable renaming functions, reduced chr/mod.rs API surface.

**Net change:** -608 lines (42 additions, 650 deletions)
**Full corpus U:** 73/100 (no regression, consolidation threshold: U > 27)
**treecalc_synth_flip U:** 74/100 (no regression)
**Verdict:** KEEP

## Changes

### Target 1: Unified factor_tensor duplication in nf.rs
Extracted `build_factor_wiring()` helper to consolidate ~80 duplicated lines between `factor_tensor` and `factor_tensor_with_subst`. Both functions shared identical logic for bitset membership testing, rhs ordering, constraint renaming, and DropFresh map building. The shared helper handles steps 3-5 and 7 of the factoring pipeline.

### Target 2: Removed metrics.rs (497 lines)
`src/metrics.rs` was never imported outside itself. The module defined `EvalMetrics` for aggregate statistics but was completely dead code. Removed the module and its `pub mod metrics` declaration in `lib.rs`.

### Target 3: Cleaned up nf.rs variable renaming functions
Removed dead `constraint_var_renaming` and `combined_var_renaming` functions (neither had any callers). Made `combined_var_renaming_with_extra` private (only used within nf.rs).

### Target 4: chr/mod.rs API surface reduction
Reduced visibility of `match_pat_nobind`, `instantiate_pat`, `freeze_chr` from `pub` to `pub(crate)`. Gated `thaw_chr` and `ByteReader` behind `#[cfg(test)]` (only used in test code). This also resolved 3 clippy dead_code warnings.

## Files Changed

- `src/nf.rs` — Extracted build_factor_wiring helper, removed dead functions, reduced visibility (-141 lines)
- `src/metrics.rs` — Deleted entirely (-497 lines)
- `src/lib.rs` — Removed `pub mod metrics` (-1 line)
- `src/chr/mod.rs` — Reduced visibility, added #[cfg(test)] gating (-11 lines, +11 lines)
