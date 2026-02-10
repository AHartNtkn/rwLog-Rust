# Investigation: Pre-Constraint Pipeline Cache

## Summary

Thread-local cache for the full constraint pipeline (apply_subst + combine + normalize) keyed by (constraint_identity_ptr, subst_hash, var_offset) showed a 1.6% regression on treecalc_synth_flip.

**Baseline:** 76936.053 us (median, all values: 78315.101, 76802.730, 78726.952, 78972.515, 75628.128, 79364.518, 76502.469, 77069.377, 75889.632, 75952.576)
**After:** 78172.786 us (median, all values: 86276.634, 78021.661, 77675.759, 82520.727, 77585.307, 78323.912, 80637.209, 80428.621, 77421.699, 77610.750)
**Improvement:** ~-1.6% (regression)
**Mann-Whitney U:** 23/100 (p > 0.05, not significant — optimized is slower)
**Regression:** Optimized is significantly slower than baseline

## Problem

The compose_nf constraint pipeline (apply_subst to both constraints, combine, normalize_owned) accounts for a substantial fraction of compose_nf time. With 63K compose attempts per treecalc_synth_flip, many share the same (constraint_ptr, substitution) inputs. Caching the full pipeline output should skip repeated work.

## Solution (attempted)

Added a thread-local LRU cache (capacity 64) keyed by:
- `a_constraint.constraint_identity()` — Arc pointer of left constraint data
- `b_constraint.constraint_identity()` — Arc pointer of right constraint data
- Hash of `combined_subst.bindings_raw()`
- `b_var_offset` (u32)

On cache hit, skip apply_subst, combine, and normalize_owned entirely, returning the cached (normalized_constraint, subst_opt) pair.

### Key design decisions

1. Used Arc pointer identity for constraint keys — O(1) comparison instead of deep structural equality. Safe because ChrState uses Arc<ChrStateData> which is immutable once shared (copy-on-write).
2. Added `constraint_identity()` method to ConstraintOps trait with default returning 0 (no caching for trivial `()` constraints). ChrState returns Arc::as_ptr.
3. Used FxHashMap with manual LRU eviction for the cache.

## Files changed

- `src/constraint.rs` — Added `constraint_identity()` to ConstraintOps trait
- `src/chr/mod.rs` — Implemented `constraint_identity()` for ChrState
- `src/subst.rs` — Added `bindings_raw()` accessor for efficient hashing
- `src/kernel/compose.rs` — Added thread-local constraint pipeline cache

## Why regression instead of improvement

The cache has extremely low hit rate. Most compose_nf calls involve unique (constraint, substitution) combinations because:
1. Substitutions are built from matching, which produces different bindings for each compose attempt
2. Constraint Arc pointers change after every normalize_owned call (which creates new ChrStateData)
3. The hash computation over substitution bindings + TLS access overhead is paid on every call (63K times), while hits are rare

The overhead of computing cache keys (hashing the substitution, extracting Arc pointers, TLS access) on every compose_nf call outweighs the savings from the rare cache hits.

## Remaining opportunities

- The fundamental issue is that apply_subst at 36.32% is doing real work on unique inputs each time — caching is not the right approach for this hotspot
- Algorithmic improvements to reduce the number of compose_nf calls (e.g., better indexing to prune impossible compositions earlier) would be more effective
- Reducing the per-call cost of apply_subst itself (e.g., specializing for common substitution patterns, avoiding tree walks for identity substitutions on sub-terms) is the remaining viable path
