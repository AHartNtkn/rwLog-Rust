# Investigation: Eliminate Occurs Checks from Compose-Path Matchers

## Summary

Attempted to remove occurs checks from `match_terms_combined_shifted_with_left_renaming` and `match_terms_combined`. Tests hang (lam_eq tests) — occurs checks are necessary for correctness.

**Baseline:** N/A (correctness failure, no measurement)
**After:** N/A
**Improvement:** N/A
**Mann-Whitney U:** N/A
**Regression:** N/A — tests fail

## Problem

`occurs_unlocked` consumes 19.15% of `treecalc_synth_flip` runtime. Two of the four matching functions (`match_terms_combined_shifted_with_left_renaming` at lines 423/434 and `match_terms_combined` at lines 265/271) call occurs checks on every variable binding. A previous investigation had already removed occurs checks from `match_terms_combined_shifted` on the basis that disjoint variable namespaces make self-referential bindings impossible. The hypothesis was that the same reasoning applies to the other matchers.

## Solution (Failed)

Removed all `occurs_unlocked` calls from `match_terms_combined_shifted_with_left_renaming` and `match_terms_combined`, replacing them with unconditional `true` (always succeed without checking).

## Why It Failed

**The hypothesis was wrong.** Even with disjoint variable namespaces, cross-namespace substitution cycles are possible through the combined substitution:

1. During matching, Var(i) (left namespace) gets bound to a term containing Var(j) (right namespace)
2. Later in the same worklist, Var(j) gets bound to a term containing Var(i)
3. This creates a cycle: `Var(i) -> term_with_Var(j) -> subst(Var(j)) -> term_with_Var(i) -> ...`

Concrete example:
- Subst already has `Var(2) -> App(F, Var(0))`
- Now matching `Var(0)` with `App(G, Var(2))`
- Without occurs check: bind `Var(0) -> App(G, Var(2))`
- Substitution now has: `{Var(2) -> App(F, Var(0)), Var(0) -> App(G, Var(2))}` — a cycle
- `apply_subst` on either variable generates infinite terms

The `lam_eq` test suite exercises exactly this pattern through lambda calculus beta reduction, where nested function applications create cross-referencing binding chains.

**Key insight**: The previous removal of occurs checks from `match_terms_combined_shifted` may have been correct for that specific matcher's usage context (where cross-namespace cycles cannot form due to the monotone binding order), but this does NOT generalize to the other matchers where the binding order is not constrained.

### Key design decisions

1. **Reverted all changes** — there is no safe partial removal of occurs checks from these matchers without a proof that cross-namespace cycles cannot form in their specific call contexts
2. **The previous investigation that removed occurs checks from `match_terms_combined_shifted` should be re-examined** — it may be correct, but the reasoning does not transfer

## Files changed

None (all changes reverted).

## Why N/A instead of X%

Correctness failure. The optimization cannot be applied as conceived.

## Remaining opportunities

- **Cheaper occurs checks**: Instead of a full recursive tree walk, track which variables are reachable from which other variables in the substitution and do a simple set lookup. This would reduce the cost from O(term_size) to O(1) per check, but requires maintaining an auxiliary data structure.
- **Occurs check batching**: Instead of checking after each binding, batch all bindings from a single match and check for cycles in the final substitution graph. This could amortize the overhead.
- **Profile-guided partial removal**: Instrument which specific call sites actually encounter cycles (rather than proving they can't). If a specific call site never encounters cycles in practice, the occurs check could be removed with a debug assertion.
