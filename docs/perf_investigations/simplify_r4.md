# Investigation: Multi-Target Codebase Consolidation Round 4

## Summary

Removed dead code and tightened visibility across term, subst, and rel modules. KEEP as consolidation (U=49, no regression). Net -67 lines.

**Full corpus U:** 49/100 (consolidation threshold: U > 27)
**Verdict:** KEEP (consolidation)

## Changes

1. **term.rs**: Removed unused `TermStore::app_from_slice` method (0 callers)
2. **subst.rs**: Removed `Subst::with_capacity` (only used in own test); gated `is_bound` and `len` with `#[cfg(test)]` (only used in test modules); removed `with_capacity_creates_empty_subst` test
3. **rel.rs**: Removed 30-line `structurally_equal` helper function from tests; replaced ~20 call sites with `assert_eq!` (safe because `Rel` derives `PartialEq` and `NF` has custom `PartialEq`)

## Files Changed

- `src/term.rs` — Removed unused app_from_slice (-10 lines)
- `src/subst.rs` — Removed/gated test-only APIs (-16 lines)
- `src/rel.rs` — Replaced structurally_equal with assert_eq! (-41 net lines)

## Notes

The codebase is very clean — clippy produces zero warnings, no TODO/FIXME/HACK comments, minimal dead code remaining. Future consolidation rounds would need to target architectural simplification rather than dead code removal.
