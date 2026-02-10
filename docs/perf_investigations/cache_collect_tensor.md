# Investigation: cache_collect_tensor

**Status:** DISCARD
**Round:** 21
**Date:** 2025-02-09

## Hypothesis

`collect_tensor` is called 648K times during compose_nf (2 per attempt x 324K) but there are only ~1K unique NFs. Each call walks the build_pats term tree via `apply_var_renaming_list` to remap variables through DropFresh. Caching the renaming result in NfInner should eliminate ~647K redundant tree walks, saving ~3% of runtime.

## Changes Made

- `src/nf.rs`: Added `cached_rhs_direct: Option<SmallVec<[TermId; 1]>>` to `NfInner`. Pre-computed in `factor_tensor` and `NF::factor`. `collect_tensor` checks for cached value and returns directly if present.

## Measurement

### Primary: treecalc_synth_flip
**Baseline median:** 2091546us
**Optimized median:** 2100422us
**U = 47/100 — DISCARD (no improvement)**

## Analysis

The caching overhead at NF construction time offset the savings from avoiding redundant tree walks:

1. **Eager construction cost**: `compute_rhs_direct` is called in `factor_tensor` for EVERY newly-constructed NF, including the output of every `compose_nf` and `meet_nf` call. Many of these NFs are short-lived — composed once and then discarded without ever having `collect_tensor` called on them. The cache pays the construction cost even when it's never read.

2. **Memory overhead**: Adding 32 bytes per NfInner (`Option<SmallVec<[TermId; 1]>>`) increases the Arc allocation size, potentially hurting cache locality for the frequently-accessed `match_pats`/`drop_fresh`/`build_pats` fields.

3. **Small per-call cost**: While `collect_tensor` is called 648K times, each individual call processes very small term trees (typically 1-2 patterns with 2-5 nodes). The `apply_var_renaming_list` tree walk for such small terms is extremely fast, making the absolute time saved per cached hit negligible.

## Remaining Opportunities

- **Lazy caching via OnceLock**: Only compute the cached value on first access, not at construction. But `NfInner` is inside `Arc` which requires `Send+Sync`, and `OnceLock` synchronization overhead would likely exceed the tree walk cost for small terms.
- **External cache**: Maintain a separate `HashMap<*const NfInner, SmallVec<[TermId; 1]>>` in the compose/meet callers. This avoids increasing NfInner size but adds HashMap lookup overhead.
