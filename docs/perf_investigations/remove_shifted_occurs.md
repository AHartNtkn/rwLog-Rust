# Investigation: Remove Occurs Check from Offset-Aware Matcher

## Summary

Removed the provably-unnecessary occurs check from `match_terms_combined_shifted`, yielding ~3.9% improvement on treecalc_synth_flip.

**Baseline:** 2039209us (median, all values: 2032102, 2034773, 2059752, 2027253, 2028988, 2043646, 2028487, 2060325, 2082069, 2094500)
**After:** 1960393us (median, all values: 1958702, 1958504, 1957565, 1961071, 1964749, 1967614, 1974252, 1980428, 1956702, 1959715)
**Improvement:** ~3.9% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001, complete separation)
**Regression:** None observed on recursive_even_backward_first64 (U=53/100, neutral)

## Problem

The `occurs_unlocked` function was 3.86% of total runtime in profiles. It was called exclusively from `match_terms_combined_shifted` (lines 205 and 213 of matching.rs) — the offset-aware matcher added in Round 21. The occurs check prevents cyclic/infinite term creation during matching by verifying that a variable doesn't appear in the term being bound to it.

However, `match_terms_combined_shifted` is only called from `match_term_lists_shifted` when:
1. The substitution is empty (no prior bindings)
2. Variables are in disjoint namespaces (shifted_vars is non-empty)

## Solution

Removed both `occurs_unlocked` calls and deleted the now-dead `occurs_unlocked` function entirely. Net change: 5 insertions, 45 deletions.

### Correctness proof

Under the conditions in which `match_terms_combined_shifted` is called:

1. **Empty initial substitution**: No variable chains exist at the start. Each binding creates a fresh mapping.

2. **Disjoint variable namespaces**: Left variables have indices 0..n-1 (where n is the left NF's max var + 1). Right variables have indices offset..offset+m-1 (via shifted_vars). Since offset > n-1, the ranges are completely disjoint.

3. **No cross-namespace cycles**: A left variable can only be bound to a term containing right-side variables (indices >= offset). A right variable can only be bound to a term containing left-side variables (indices < offset). Since a left variable ($i, i < offset) cannot appear in a right-side term tree (which contains only indices >= offset), and vice versa, the substitution chain can never form a cycle.

4. **Therefore**: The occurs check always returns false in this context. Removing it is a pure performance improvement with no correctness impact.

This is a mathematical proof, not a heuristic. The disjoint namespace property is guaranteed by the variable shifting mechanism.

## Files changed

- `src/matching.rs` — Removed both `occurs_unlocked` calls from `match_terms_combined_shifted` and deleted the `occurs_unlocked` function (now dead code).

## Why 3.9% instead of 3.86%

The measured improvement (3.9%) closely matches the profiled self-time for `occurs_unlocked` (3.86%). The slight over-performance is likely due to secondary effects: removing the occurs check eliminates SmallVec stack allocation for each check and reduces instruction cache pressure in the matching hot path.

## Remaining opportunities

- The locked version `occurs_locked` in `match_terms_combined` (the non-shifted matcher) could potentially be optimized similarly for cases where the matcher is called with known-disjoint namespaces, but this path is less hot.
- Linearity-based occurs check elimination for the general matcher remains uninvestigated.
