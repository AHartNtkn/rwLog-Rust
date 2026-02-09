# Investigation: Defer shift_term in compose matcher to post-match success path

## Summary

Attempted to defer shift_term() calls during compose matching to avoid tree walks for the 99.14% of compose attempts that fail. No improvement — slight regression.

**Baseline:** 1103214us (median, all values: 1109604, 1110745, 1100075, 1091307, 1140372, 1125165, 1085740, 1094242, 1096136, 1107502)
**After:** 1116032us (median, all values: 1093151, 1118384, 1092355, 1113679, 1142588, 1104998, 1123906, 1099680, 1135400, 1148248)
**Improvement:** -1.11% (slight regression, not significant)
**Mann-Whitney U:** 34/100 (not significant)
**Regression:** N/A

## Problem

In the compose matcher (`match_terms_combined_shifted_with_left_renaming`), `shift_term()` at 8.97% of total runtime walks entire right-side subtrees to create physically shifted terms when binding left-side variables to right-side App nodes. Since 99.14% of compose attempts fail, the hypothesis was that deferring these tree walks to the success path would eliminate most of the cost.

## Solution Attempted

Changed `match_terms_combined_shifted_with_left_renaming` to store raw (unshifted) terms in the substitution during matching, tracking deferred shifts in a `SmallVec<[(u32, TermId); 4]>`. After matching succeeded, the deferred shifts and renames were materialized. A `DeferredMatchResult` struct was returned carrying both the substitution and deferred info.

## Why it failed

1. **shift_term is concentrated in successful/near-miss matches, not early failures.** The compose_nf root functor precheck (lines 59-73 in compose.rs) already eliminates most incompatible pairs before the matcher is invoked. The remaining calls that reach the matcher tend to progress deep enough to encounter Var-App bindings — these are predominantly the 0.86% of successful matches (where deferral provides no savings) plus a relatively small number of near-miss failures.

2. **SmallVec bookkeeping overhead.** Initializing two `SmallVec<[(u32, TermId); 4]>` (96 bytes of stack) on every matcher call (324K calls per evaluation) added measurable overhead that negated any savings from the few deferred shift_term calls on the failure path.

3. **The 8.97% attribution was misleading.** The profiler attributed 8.97% to shift_term, but this includes all callers — the compose matcher, match_term_lists_shifted, and potentially other paths. The fraction attributable to failed compose attempts specifically was much smaller than assumed.

## Files changed

- `src/matching.rs` — Added `DeferredMatchResult` struct, modified matcher to defer shift_term/rename_term
- `src/kernel/util.rs` — Modified `match_term_lists_shifted_with_left_renaming` to apply deferred shifts after successful matching (reverted, DISCARD)

## Remaining opportunities

- A more effective approach might be to avoid interning shifted terms entirely by using a "virtual shift" wrapper in the substitution that is only resolved when consumed (lazy shifting at point of use).
- Alternatively, reducing the NUMBER of compose_nf calls via stronger prechecks (deeper functor matching, structural fingerprinting) could eliminate more of the 324K calls before they reach the matcher at all.
