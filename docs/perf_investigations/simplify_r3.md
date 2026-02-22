# Investigation: Multi-Target Codebase Consolidation Round 3

## Summary

Removed dead code from perf_counters.rs and tightened visibility in kernel modules. KEEP as consolidation (U=41, no regression). Net -43 lines.

**Full corpus U:** 41/100 (consolidation threshold: U > 27)
**Verdict:** KEEP (consolidation)

## Changes

1. **kernel/util.rs**: `compose_subst` visibility `pub fn` → `fn` (only used within util.rs)
2. **kernel/dual.rs**: `dual_drop_fresh` reduced from `pub fn` to `#[cfg(test)] fn` (only used in tests); moved `DropFresh` and `SmallVec` imports to `#[cfg(test)]`
3. **kernel/mod.rs**: Removed `dual_drop_fresh` from `pub use` re-export (never used outside dual.rs)
4. **perf_counters.rs** (-34 lines): Removed dead `FrequencyHistogram` type alias, `pair_frequency_histograms()` function, `record_compose_pair_hash()` frequency tracking, and COMPOSE_PAIR_FREQ/MEET_PAIR_FREQ statics
5. **tests/compose_meet_dedup_investigation.rs** (-12 lines): Removed dead frequency histogram display block

## Files Changed

- `src/kernel/util.rs` — Tightened compose_subst visibility
- `src/kernel/dual.rs` — Moved dual_drop_fresh to test-only
- `src/kernel/mod.rs` — Removed unused re-export
- `src/perf_counters.rs` — Removed 34 lines of dead frequency tracking code
- `tests/compose_meet_dedup_investigation.rs` — Removed 12 lines of dead histogram display
