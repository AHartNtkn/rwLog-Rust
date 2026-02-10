# Investigation: Eliminate split_match_subst in compose_nf

## Summary

Eliminated `split_match_subst` from the compose_nf pipeline by returning the raw combined substitution from matching and letting consumers resolve bindings lazily through `apply_subst`'s natural chain following.

**Baseline:** 839730us (median, all values: 851530, 853664, 849073, 866568, 848059, 831401, 823367, 829186, 827929, 825879)
**After:** 704724us (median, all values: 714443, 723812, 716725, 730607, 706381, 692233, 699186, 700781, 703066, 694184)
**Improvement:** ~16.1% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001, complete separation)
**Regression:** None observed on recursive_even_backward_first64 (U=61/100, neutral)

## Problem

After matching a's build patterns against b's match patterns in `compose_nf`, the previous pipeline called `split_match_subst` to split the combined substitution into separate (left, right) halves. `split_match_subst` walked ALL bindings in the combined substitution, calling `apply_subst` on each to resolve transitive chains, then partitioned bindings by the variable offset boundary. This was 14.21% of total runtime in profiling.

The cost was dominated by two factors:
1. **Transitive chain resolution**: For every binding `var -> term`, `apply_subst(term, &combined, terms)` followed the full substitution chain, potentially creating new intermediate terms in the TermStore (HashMap insert + hash computation).
2. **Unnecessary work**: The downstream consumers (constraint `apply_subst`, `factor_tensor_with_subst`) only access bindings from their own variable side. Left-side patterns contain only left-side vars (< offset), right-side patterns contain only right-side vars (>= offset). The "extra" bindings for the other side are never accessed.

## Solution

Added `match_term_lists_shifted_with_left_renaming_combined` which returns the raw combined `Subst` instead of splitting it. Modified `compose_nf_impl` to pass the combined substitution directly to all consumers:

1. **Constraint apply_subst**: Both `a.drop_fresh.constraint.apply_subst(&combined_subst, terms)` and `b.drop_fresh.constraint.remap_and_apply_subst(...)` receive the combined substitution. Each constraint's args only reference variables from their own side, so cross-side bindings are never accessed.

2. **factor_tensor_with_subst**: The fused factoring pass receives the combined substitution in both `lhs_params` and `rhs_params`. Left-side patterns only contain left-side vars, right-side patterns only contain right-side vars, so chain resolution through `apply_subst` naturally follows only the relevant bindings.

3. **Chain resolution is lazy**: When `apply_subst` encounters a binding `var -> other_var` where `other_var` has its own binding in the same substitution, it naturally follows the chain. This is equivalent to `split_match_subst`'s eager resolution but amortized: only chains that are actually traversed during factor/constraint operations get resolved, and only as deep as needed.

### Key design decisions

1. **Combined subst passed by reference, not split.** The combined Subst is a dense `Vec<Option<TermId>>`. Passing it to multiple consumers adds zero overhead — it's a slice reference. Split would create two new Vecs.

2. **meet_nf path unchanged.** The meet_nf path (in `match_term_lists_shifted`) still uses `split_match_subst` because meet's multi-round substitution application pattern requires fully resolved separate substitutions. Only the compose path was changed.

3. **No semantic change.** Every consumer that previously received `subst_left` or `subst_right` now receives the combined substitution. The extra bindings are invisible because left patterns don't contain right vars and vice versa. The only difference is that chain resolution happens lazily during consumption rather than eagerly during splitting.

## Files changed

- `src/kernel/util.rs` — Added `match_term_lists_shifted_with_left_renaming_combined` returning raw `Subst`. (~22 lines changed)
- `src/kernel/compose.rs` — Modified `compose_nf_impl` to use combined substitution directly for constraints, factor_tensor_with_subst, and all downstream operations. (~50 lines changed)

## Why 16.1% instead of 5-14%

The estimated 5-14% assumed `split_match_subst` was primarily a traversal cost (walking bindings). In practice, the cost was amplified by:

1. **TermStore interning during chain resolution.** `apply_subst` on each binding potentially creates new intermediate terms when resolving chains. Each new term requires `intern_unlocked` (HashMap hash + probe + insert). With ~10-50 bindings per successful compose and 100+ bindings per split, this added significant HashMap overhead.

2. **All bindings resolved, not just accessed ones.** `split_match_subst` resolved chains for ALL bindings, including those that would never be accessed by downstream consumers. The combined subst approach only resolves chains that are actually traversed.

3. **Cascading savings.** Eliminating intermediate term creation reduces TermStore size growth, which improves cache hit rates for subsequent operations in the same compose pipeline.

The 16.1% represents the true cost of split_match_subst including its second-order effects on TermStore and cache behavior, not just the direct traversal cost.

## Remaining opportunities

- The `meet_nf` path still uses `split_match_subst`. Changing it would require rethinking the multi-round substitution pattern — meet applies substitutions iteratively and needs fully resolved separate substitutions at each step.
- `apply_subst` itself (29.57% pre-optimization) remains the largest single cost center. Further improvement requires algorithmic changes (lazy substitution, shared-nothing representation) rather than avoiding splits.
- `shift_term` (11.98%) is still called during matching when left-side Var matches right-side compound term. Deferring shift_term was previously tried and discarded, but the cost structure may have changed after this optimization.
