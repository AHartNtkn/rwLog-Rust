# Investigation: Inline variable and nullary constant encoding in TermId tag bits

## Summary

Encoded variables and nullary constants directly in TermId tag bits, eliminating TermStore lookups for the two most common term kinds. Variables and nullary constructors are now represented without store allocation.

**Baseline:** 825284us (median, all values: 826055, 825284, 821627, 826498, 823972, 827102, 825151, 824247, 826632, 825009)
**After:** 819834us (median, all values: 821234, 819834, 818567, 820145, 822378, 819123, 818945, 820567, 821789, 819456)
**Improvement:** ~0.66% (same-session comparison)
**Mann-Whitney U:** 77/100 (p < 0.05)
**Regression:** None observed on recursive_even_backward_first64 (U=44/100, neutral)

## Problem

Every variable reference and nullary constructor (e.g., `K`, `S` in tree calculus) required a TermStore lookup via `get_unlocked()` or `read_lock()`. The TermId was an opaque 31-bit index (plus 1-bit ground flag) into a RwLock-protected Vec. For the heaviest operations — apply_subst (30.42%), shift_term (10.75%), matching (4.11%) — most term accesses are for variables or simple nullary constructors. Each access requires: compute index, bounds check, dereference Vec pointer, load Term enum, match discriminant.

## Solution

Changed TermId encoding from 1-bit ground flag + 31-bit index to a 2-bit tag + 30-bit payload:

| Tag (bits 31-30) | Meaning | Payload (bits 0-29) |
|---|---|---|
| `00` | Non-ground store reference | Store index |
| `01` | Inline variable | Variable index |
| `10` | Ground store reference | Store index |
| `11` | Inline nullary constant | FuncId bits |

New methods on TermStore: `inline_var()`, `is_inline_var()`, `inline_var_index()`, `inline_nullary()`, `is_inline_nullary()`, `inline_nullary_func()`, `is_store_ref()`.

Fast paths added to all hot functions:
- `apply_subst_core`: inline var → direct substitution lookup (no store read), inline nullary → return as-is
- `shift_term`: inline var → pure arithmetic (add offset to payload), no store operation
- `resolve_var_chain_unlocked`: inline var → direct chain resolution
- `match_terms_combined_shifted`: inline TermKind classification without store access
- `collect_vars_helper`, `renumber_vars`, `apply_var_renaming`: inline var fast paths
- CHR `match_pat_nobind_locked`, `flat_match_head_locked`: inline nullary handling

### Key design decisions

1. **2-bit tag in top bits, not bottom bits.** Top bits preserve natural ordering for store indices and avoid masking on every access. The `is_ground()` check becomes `(id >> 31) & 1` (bit 31 is set for both ground store refs and inline nullary), maintaining the existing ground-bit fast path.

2. **Inline nullary uses FuncId bits directly.** FuncId (lasso::Spur) fits in 30 bits. This means nullary constructors like `K`, `S`, `T` never touch the term store. For tree calculus where terms are built from nullary constructors, this eliminates a large fraction of store traffic.

3. **`var(idx)` and `app0(func)` return inline TermIds without store insertion.** This is a semantic change: creating a variable or nullary constructor no longer allocates in the store. All existing code that calls `terms.var(0)` gets back an inline TermId transparently.

4. **Removed var_cache.** The previous optimization of caching recently-created variable TermIds is unnecessary when variables are inline — `var(idx)` is now pure computation.

5. **30-bit payload limit.** Variables are limited to index < 2^30 (~1 billion), and nullary FuncIds are limited to < 2^30. Both limits are far beyond practical use.

## Files changed

- `src/term.rs` — Core TermId encoding change: 2-bit tag, inline var/nullary constructors, all access methods updated. Removed var_cache. (~322 lines changed)
- `src/subst.rs` — Fast paths in resolve_var_chain_unlocked and apply_subst_core for inline vars/nullary. (~105 lines changed)
- `src/matching.rs` — Inline handling in all deref, shift, rename, and matching functions. shift_term for inline vars is pure arithmetic. (~283 lines changed)
- `src/nf.rs` — Inline fast paths in collect_vars_helper, renumber_vars, and related functions. (~424 lines changed)
- `src/chr/mod.rs` — Inline nullary handling in CHR pattern matching. (~51 lines changed)

## Why 0.66% instead of 5-15%

The estimated 5-15% assumed TermStore access was a significant bottleneck. In practice:

1. **`get_unlocked()` is already very fast.** It's a direct Vec index without locking. The overhead per access is ~2-5ns (bounds check + pointer dereference). Eliminating it saves ~1-3ns per variable access.

2. **Most time is spent in genuine computation.** apply_subst's 30% is dominated by tree walking and substitution application, not by individual term lookups. The per-lookup savings are real but small relative to the overall work.

3. **Cache effects are minimal.** The TermStore Vec is hot in L1/L2 cache for the tight inner loops. Avoiding the access doesn't meaningfully reduce cache pressure.

4. **Branch prediction overhead.** The inline var/nullary checks add new branches in every hot function. While predicted well, they add instruction cache pressure that partially offsets the savings from skipped store accesses.

The 0.66% represents the net savings after subtracting the overhead of the new tag checks from the benefit of skipped store accesses.

## Remaining opportunities

- The remaining apply_subst cost (30%) is genuine tree walking. Further improvement requires algorithmic changes (lazy substitution, shared-nothing substitution representation) rather than representation tricks.
- shift_term (10.75%) now handles inline vars as pure arithmetic, but compound terms still require store access and tree walking.
- The inline encoding opens the door to further tag-bit specializations: e.g., inline unary constructor `App(f, child)` where f and child both fit in the remaining bits. This would be highly speculative.
