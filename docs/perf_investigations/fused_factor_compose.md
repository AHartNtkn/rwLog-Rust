# Investigation: Fused Factor-Tensor with Substitution in compose_nf

## Summary

Eliminated intermediate term creation in compose_nf by fusing apply_subst into factor_tensor, yielding ~27.8% improvement on treecalc_synth_flip.

**Baseline:** 2049837us (median, all values: 2019307, 2047066, 2111547, 2071795, 2036363, 2031724, 2065594, 2080786, 2051266, 2048409)
**After:** 1479001us (median, all values: 1474451, 1476751, 1474124, 1506226, 1481931, 1478352, 1471809, 1479650, 1526269, 1504462)
**Improvement:** ~27.8% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001, complete separation)
**Regression:** None — secondary workload recursive_even_backward_first64 also improved ~4.5% (U=76/100)

## Problem

In compose_nf, after matching succeeds at the interface, the pipeline performed multiple separate tree walks that each created intermediate terms:

1. `apply_subst_list(&rw1.lhs, &subst_left)` — walk patterns, create substituted terms (interned in HashMap)
2. `apply_subst_shifted_list(&rw2.rhs, &subst_right, ...)` — walk patterns with shifting, create substituted terms
3. If constraint normalization produces `subst_opt`: `apply_subst_list` again on both sides — another walk creating MORE intermediate terms
4. `factor_tensor(new_match, new_build, ...)` — walk the intermediate terms to collect vars, then walk AGAIN to renumber vars

Total: 4-6 tree walks per successful compose, with 2-4 rounds of intermediate term creation. Each term creation involves a hashcons lookup (HashMap get + potential insert). With 324,674 compose calls on treecalc_synth_flip (even with 99.14% failure rate, ~2,787 successes), the intermediate term creation dominated runtime.

Profile showed:
- apply_subst: 20.96% of runtime
- HashMap::get_inner: 13.29% of runtime (from term interning)

## Solution

Created `factor_tensor_with_subst` — a fused version that takes the ORIGINAL patterns along with their substitutions, and resolves variables through the substitutions during its own traversal passes. This eliminates all intermediate term creation.

### Key design decisions

1. **SubstParams struct**: Encapsulates substitution parameters (primary subst, optional secondary subst, shifted flag, shifted_vars) to keep function signatures clean. The secondary substitution handles the constraint-derived `subst_opt` case.

2. **Two-phase fused traversal**: Phase 1 (`collect_vars_through_subst_list`) walks patterns resolving through substitutions to discover variables WITHOUT creating terms. Phase 2 (`renumber_vars_through_subst_list` or `apply_subst_and_renumber_list`) walks again with the renaming map to produce final terms directly.

3. **Variable chain resolution**: Uses `resolve_var_chain_unlocked` (made pub(crate) in subst.rs) to chase variable bindings through substitution chains. When two substitutions are provided, chains are resolved through both sequentially.

4. **VarResolution enum**: Inside the traversal loop, a scoped borrow of `terms.nodes.get_mut()` extracts all needed information into a `VarResolution` enum, then the mutable borrow is released before creating new terms. This avoids borrow conflicts between reading existing terms and interning new ones.

5. **Shifted variable handling**: When `shifted=true`, raw variables are mapped through `shifted_vars` before substitution lookup, matching the semantics of `apply_subst_shifted`.

### Reordering in compose_nf

The compose pipeline was restructured to:
1. Match at interface → get subst_left, subst_right
2. Apply subst to CONSTRAINTS only (still needed for normalization)
3. Normalize constraints → get subst_opt
4. Pass ORIGINAL patterns + composed substitutions to `factor_tensor_with_subst`

The pattern substitution is now fully deferred — intermediate substituted patterns are never created.

## Files changed

- `src/kernel/compose.rs` — Restructured compose_nf_impl to use `factor_tensor_with_subst` instead of apply_subst_list + factor_tensor. Removed imports of apply_subst_list and apply_subst_shifted_list.
- `src/nf.rs` — Added `SubstParams` struct, `factor_tensor_with_subst` function, and three fused helper functions: `renumber_vars_through_subst_list`, `collect_vars_through_subst_list`, `apply_subst_and_renumber_list`.
- `src/subst.rs` — Made `resolve_var_chain_unlocked` pub(crate) for cross-module use.

## Why 27.8% instead of the estimated 3-5%

The original estimate of 3-5% was based on counting only the apply_subst_list calls in compose_nf. The actual improvement was dramatically larger because:

1. **Cascading term creation**: When a variable resolves through a substitution to a compound term, the ENTIRE subtree must be re-created with new variable indices. For deep tree calculus terms, this means creating dozens of intermediate terms per compose success, each requiring a full hashcons probe.

2. **HashMap pressure**: The intermediate terms pollute the hashcons HashMap with entries that are never accessed again. This increases hash table load factor, slows probe sequences for all subsequent lookups, and wastes memory.

3. **Cache pollution**: Intermediate terms occupy CPU cache lines that are immediately evicted, displacing useful data and increasing cache miss rates for subsequent operations.

4. **Double-walk elimination**: When constraint normalization produces subst_opt (common in CHR-constrained workloads like treecalc_synth_flip), the old pipeline re-walked already-substituted patterns. The fused approach handles both substitutions in a single traversal.

The 27.8% improvement reflects the compound effect of eliminating all these costs simultaneously.

## Remaining opportunities

- Apply the same fused approach to `meet_nf`, which has even more apply_subst_list calls (9+ per success). However, meet_nf is called much less frequently (~241 times vs 324K for compose).
- The `collect_vars_through_subst_list` phase still does a separate traversal from the renumber phase. A single-pass approach that discovers and renumbers simultaneously would be possible if variables were assigned indices in order of discovery (which they already are), but would require careful handling of the constraint renaming step.
- The original `factor_tensor` + `apply_subst_list` path is still used by meet_nf and dual.rs. If those become hot paths in other workloads, they could benefit from the same fusion.
