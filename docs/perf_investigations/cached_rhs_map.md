# Investigation: Cache DropFresh rhs_map in NfInner for faster compose matching

## Summary

Cached the DropFresh reverse mapping (rhs_map) in NfInner and wrote an inline-renaming matcher to avoid per-compose `apply_var_renaming_list` tree walks. Eliminates physical term creation for 99.14% of failing compose attempts.

**Baseline:** 1180234us (median, all values: 1179969, 1177096, 1183066, 1171385, 1185507, 1180506, 1180499, 1172186, 1203513, 1176206)
**After:** 1136427us (median, all values: 1134365, 1135867, 1141891, 1134121, 1134576, 1133733, 1137551, 1136986, 1144519, 1137291)
**Improvement:** ~3.71% (same-session comparison)
**Mann-Whitney U:** 100/100 (complete separation, p < 0.0001)
**Regression:** None observed on recursive_even_backward_first64 (U=66/100, neutral)

## Problem

In `compose_nf_impl`, every compose attempt (324K calls) eagerly called `collect_tensor(a, terms)` which internally computed `apply_var_renaming_list(a.build_pats, rhs_map, terms)`. This walked each build pattern tree and created new interned terms with renamed variables. For the 99.14% of compose attempts that fail, these renamed terms are wasted — they persist in the TermStore forever but are never referenced.

The rhs_map itself (derived from the NF's DropFresh) is deterministic and identical every time a given NF is used, yet was recomputed from scratch on every `collect_tensor` call.

## Solution

1. **Cached rhs_map in NfInner:** Added `cached_rhs_map: SmallVec<[u32; 4]>` to NfInner, computed once at NF construction time. The map encodes how build-side factored variables map to direct-form variables.

2. **Inline-renaming matcher:** Added `match_terms_combined_shifted_with_left_renaming()` in matching.rs that applies the rhs_map to left-side variables on-the-fly during matching. When visiting a left Var(idx), it does `rhs_map[idx]` (one array lookup) instead of requiring a pre-renamed TermId.

3. **Deferred collect_tensor:** In compose_nf_impl, `collect_tensor(a)` is no longer called. The matcher works directly with `a.build_pats` + `a.cached_rhs_map`. `collect_tensor(b)` is deferred to the success path only (0.86% of attempts).

### Key design decisions

1. **SmallVec<[u32; 4]> for rhs_map:** Build-side arities are typically small (1-4). The SmallVec stores up to 4 entries inline, avoiding heap allocation for the common case. Each entry is the direct-form variable index (not Option<u32> — all slots are filled by construction).

2. **Separate matcher variant rather than modifying existing:** The inline-renaming matcher is a new function rather than adding a flag to the existing matcher. This keeps the non-renaming fast path unaffected and allows the compiler to optimize each variant independently.

3. **Fast path for first term pair only:** The list-level wrapper `match_term_lists_shifted_with_left_renaming` uses the inline-renaming matcher for the first (often only) term pair, then falls back to materializing renamed terms for subsequent pairs. For arity-1 NFs (the dominant case), the fallback never triggers.

## Files changed

- `src/nf.rs` — Added `cached_rhs_map` field to NfInner, `compute_rhs_map()` helper, updated `NF::new()` and `NF::identity()`, updated `collect_tensor()` and `direct_rule_terms()` to use cached map
- `src/matching.rs` — Added `match_terms_combined_shifted_with_left_renaming()` and helpers
- `src/kernel/util.rs` — Added `match_term_lists_shifted_with_left_renaming()` list-level wrapper
- `src/kernel/compose.rs` — Updated `compose_nf_impl()` to use inline-renaming matcher, defer collect_tensor to success path

## Why 3.71% instead of more

The optimization eliminates `apply_var_renaming_list` for the a-side (324K calls) and `collect_tensor(b)` for failing attempts. The remaining compose cost is dominated by match_term_lists_shifted itself (matching the actual term structures), which still requires TermStore reads for the left side's term tree. The renaming was a fraction of the total matching cost.

## Remaining opportunities

- The b-side's `apply_var_renaming_list` is now only called on the 2787 success path via `collect_tensor(b)`. This could be further deferred into `factor_tensor_with_subst` (which already handles substitution resolution inline).
- The inline-renaming matcher currently materializes renamed terms for arity > 1 patterns on subsequent iterations. A fully virtual approach that threads the renaming through compose_subst could eliminate this.
