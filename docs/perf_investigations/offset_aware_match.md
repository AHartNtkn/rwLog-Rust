# Investigation: Offset-Aware Matching in compose_nf

## Summary

Added an offset-aware variant of `match_terms_combined` that handles right-side variable shifting internally during matching traversal, eliminating the need for a separate `apply_subst_shifted` tree walk before matching. ~2.2% improvement on treecalc_synth_flip.

**Baseline:** 2084479us (median, all values: 2074778, 2108657, 2084286, 2070518, 2072426, 2119345, 2151363, 2084672, 2072960, 2111175)
**After:** 2038999us (median, all values: 2024048, 2053051, 2039187, 2038810, 2029187, 2069948, 2043455, 2048517, 2030160, 2036779)
**Improvement:** ~2.2% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001, complete separation)
**Regression:** None observed on recursive_even_backward_first64 (U=51/100, neutral)

## Problem

In `match_term_lists_shifted` (used by compose_nf), for each compose attempt the right-side term is shifted via `apply_subst_shifted` before matching. For arity-1 NFs (the common case in synth_flip, 324K compose attempts), the matching loop runs exactly once with an empty substitution. But `apply_subst_shifted` with non-zero offset and empty subst still walks the ENTIRE right-side term tree to shift every variable by the offset. This caused 324K full tree walks just to shift variables before matching — most of which immediately failed at the root functor precheck or during matching.

`apply_subst_shifted` was 5.16% of total runtime in profiles.

## Solution

Added `match_terms_combined_shifted` in `matching.rs` — an offset-aware variant of `match_terms_combined` that handles right-side variable shifting internally during traversal. Modified `match_term_lists_shifted` in `util.rs` to use this fast path when the accumulated substitution is empty and shifted_vars are available.

The shifted matcher uses a worklist with entries `(left_term, right_term, right_is_raw)` where `right_is_raw` tracks whether the right-side term's variables still need shifting. Key design decisions:

### Key design decisions

1. **Lazy materialization of shifted subtrees**: When a left-side variable binds to a right-side App subtree that is still "raw" (unshifted), the subtree is materialized with shifted variables via `shift_term()` only at binding time. For the 99%+ of compose attempts that fail, no shifting ever occurs — the matcher fails at functor mismatch without materializing anything.

2. **Careful equality short-circuit**: When both sides resolve to the same TermId, an equality check can skip further processing. But when the right side is "raw" (unshifted), `a_deref == b_deref` doesn't mean semantic equality because children still contain unshifted variable indices. The short-circuit fires only when: (a) right side is already shifted, (b) right side was dereferenced through shifted_vars (so it's in the shared namespace), or (c) both terms are ground.

3. **Lock-free access via `&mut TermStore`**: The shifted matcher uses `terms.nodes.get_mut()` (lock-free via `RwLock::get_mut()`) for term lookups instead of holding a read lock, since it may need to intern new shifted terms during binding.

4. **Fallback for multi-arity**: When the accumulated substitution is non-empty (second+ iterations of multi-arity NFs), the original `apply_subst_shifted` + `match_terms_combined` path is used. This is a rare case in synth_flip where NFs are predominantly arity-1.

## Files changed

- `src/matching.rs` — Added `match_terms_combined_shifted()` with offset-aware matching, plus helper functions `deref_unlocked`, `deref_shifted_unlocked`, `occurs_unlocked`, and `shift_term`
- `src/kernel/util.rs` — Modified `match_term_lists_shifted()` to use the fast path when subst is empty and shifted_vars is non-empty

## Why 2.2% instead of 5.16%

The theoretical maximum was ~5.16% (the full cost of apply_subst_shifted in profiles). The actual improvement is lower because:

1. **Root functor precheck already filters many pairs**: The existing root functor precheck in compose_nf_impl rejects many incompatible pairs before they reach `match_term_lists_shifted`. Those pairs never called `apply_subst_shifted` to begin with.

2. **Successful matches still need shifting**: When a match succeeds and binds a left variable to a right-side subtree, `shift_term()` is called to materialize the shifted version. This is necessary for correctness but does work similar to the old `apply_subst_shifted`.

3. **Not all apply_subst_shifted calls are from compose matching**: Some are from the `apply_subst_shifted_list` calls in compose_nf (after matching succeeds) and from meet_nf, which still use the original code path.

## Remaining opportunities

- Extend the offset-aware approach to the full matching loop (not just the first empty-subst iteration) to handle multi-arity NFs
- Apply similar lazy-shifting to meet_nf's `apply_subst_shifted_list` calls
- The `shift_term` function could be further optimized with structural caching for frequently shifted terms
