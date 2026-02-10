# Investigation: Skip Redundant match_head in apply_rule_by_id_reuse

## Summary

Removed redundant `env.reset()` and `match_head` re-matching loop from `apply_rule_by_id_reuse`, since the RVarEnv already contains correct bindings from the preceding `find_match_by_ids_reuse` call. ~10.4% improvement on treecalc_synth_flip.

**Baseline:** 2532057us (median, all values: 2549293, 2508470, 3142301, 2538182, 2566560, 2512859, 2525933, 2479424, 2516828, 3163436)
**After:** 2267824us (median, all values: 2260720, 2376902, 2229451, 2281585, 2263135, 2226881, 2251609, 2312554, 2272514, 2652749)
**Improvement:** ~10.4% (same-session comparison)
**Mann-Whitney U:** 92/100 (p < 0.001)
**Regression:** None observed on recursive_even_backward_first64 (U=56/100, neutral)

## Problem

In the CHR solver, `solve_to_fixpoint` processes each matching rule via two steps:

1. `find_match_by_ids_reuse` — resets RVarEnv, matches all heads via `match_head`, runs `search_steps_inner` for partner matching. On success, the env contains variable bindings for all heads.

2. `apply_rule_by_id_reuse` — **redundantly** resets the env again, re-matches all heads via `match_head`, then executes the rule body.

The second step was re-doing all the matching work of the first step. For the synth_flip workload, `match_head` was 17.8% of total runtime. Roughly half of those calls were the redundant re-matching in `apply_rule_by_id_reuse`.

## Solution

Removed the `env.ensure_capacity()`, `env.reset()`, and the `match_head` loop from `apply_rule_by_id_reuse`. The function now directly proceeds to body execution using the bindings already in the env from `find_match_by_ids_reuse`.

This is correct because:
1. `find_match_by_ids_reuse` and `apply_rule_by_id_reuse` share the same `&mut RVarEnv`
2. Nothing between the two calls modifies the env
3. `search_steps_inner` properly unwinds failed partner matches via `env.unwind(trail)`, leaving only successful bindings
4. For single-headed rules (all rules in synth_flip), find_match produces exactly the bindings needed for body execution

### Key design decisions

1. **Pure deletion, no new code**: The change is a net deletion of 10 lines, replaced by a 2-line comment. No new logic, no new branches, no new data structures. This makes it a risk-free simplification.

2. **Relies on RVarEnv unwind correctness**: The optimization depends on `search_steps_inner` correctly unwinding its trail on failed partner matches. This invariant was already established and tested.

## Files changed

- `src/chr/mod.rs` — Removed redundant `env.ensure_capacity()`, `env.reset()`, and `match_head` re-matching loop from `apply_rule_by_id_reuse`.

## Why 10.4% instead of 17.8%

The theoretical maximum was ~17.8% (the full cost of match_head in profiles). The actual improvement is lower because:

1. **Not all match_head calls are in apply_rule**: Some match_head calls are in `find_match_by_ids_reuse` and `search_steps_inner`, which still need to run. The redundant calls were roughly half the total.

2. **Body execution cost is unchanged**: Rule body execution (applying substitutions, interning terms, adding to constraint store) still takes the same time.

3. **The improvement exceeds the initial estimate of 1.5-3.5%** because match_head calls on the anchor head (the first head matched) are particularly expensive in synth_flip — the patterns involve deep tree calculus term structures that require walking multiple levels per match.

## Remaining opportunities

- For multi-headed rules, the matching work in `search_steps_inner` (partner matching with backtracking) is still done. Caching successful partner tuples could avoid re-searching when the same anchor constraint is revisited.
- The remaining match_head calls in `find_match_by_ids_reuse` could potentially be accelerated by pre-filtering on term structure signatures (similar to the root functor precheck in compose_nf).
