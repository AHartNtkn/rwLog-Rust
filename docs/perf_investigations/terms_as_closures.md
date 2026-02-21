# Investigation: Terms as Closures / Explicit-Substitution (Major Proposal 4)

## Summary

Attempted to defer tree walks in compose_nf via explicit-substitution terms or lazy NF construction. DISCARDED: the O(depth^2) cost is inherent to the hash-consing architecture — NF hashes require materialized TermIds, and building those TermIds requires O(tree_size) intern calls per compose step.

**Baseline:** 52,690 us (median, all values: 52589, 53033, 52690, 53356, 52441)
**After:** N/A (no successful optimization implemented)
**Verdict:** DISCARD — fundamental architectural blocker

## Problem

deep_rewrite_depth256 applies `wide_inc` (8-branch recursive rewrite) to a depth-256 term. Each of the 256 compose steps adds one tree layer per branch, making the tree O(k) at step k. Building that tree requires O(k) hash-cons operations. Over 256 steps: O(sum(k=1..256)) = O(depth^2) ~= 263K intern calls.

Profiling breakdown (~53ms):
- `factor_tensor_with_subst` (LHS/RHS tree walks): ~30ms (57%)
- `match_term_lists_shifted` (matching): ~4.5ms (8.5%)
- Everything else: ~18ms (34.5%)

## Approaches Attempted

### 1. Lazy NF match_pats
Defer computing match_pats TermIds until they're needed. **Blocked**: `DiagonalJoin::push_pending()` uses `nf.hash_value()` for dedup. The NF hash depends on match_pats TermIds, so deferred match_pats breaks the Hash/Eq contract.

### 2. Term::Subst variant (full closure representation)
Add `Term::Subst { base: TermId, subst: SubstId }` to defer substitution. **Rejected**: too invasive — 72+ match sites across 7 files would need to handle the new variant. And at hash-cons time, the closure must still be materialized to compute the correct hash.

### 3. Substitution composition
Instead of apply_subst(apply_subst(t, σ1), σ2), compute σ_composed = σ1 ∘ σ2 and apply once. **Rejected**: still O(depth^2) because the composed bindings grow with each step — binding for variable i at step k contains a term of size O(k).

### 4. all_same optimization in renumber_vars_through_subst_list
Reuse original TermId when all children are unchanged after substitution (skip interning). **Rejected**: added overhead without benefit — extra store read per node, never fires for wide_inc because the substitution changes every leaf variable. Result: 54.2ms vs 52.6ms baseline (3% slower).

### 5. Pre-resolving variables
Resolve variable lookups before tree walk. Doesn't help since the tree walk itself (traversing and interning nodes) is the bottleneck, not variable resolution.

## Why O(depth^2) is Inherent

The hash-consing architecture requires that every NF has fully materialized TermIds for its patterns. Building f^k(Var(i)) requires k intern calls. With 8 branches and 256 levels, total intern calls = 8 × sum(k=1..256) ≈ 263K. No closure or lazy approach can avoid this materialization because:

1. NF dedup depends on hash equality of materialized patterns
2. Each of 8 branches has different leaf variables, so no subtree sharing across branches
3. The `all_same` optimization never fires because substitution always changes leaves

## What Would Actually Help

To break the O(depth^2) barrier would require changing the NF hash/equality contract:
- Hash based on closure parameters (base pattern + substitution) rather than materialized tree
- Accept that different closures producing the same logical NF would not be deduped (false negatives)
- Or prove that closure equality implies materialized equality for all reachable NFs

This is a deep architectural change affecting all NF consumers (DiagonalJoin, tabling, answer dedup). It may be worth investigating as a standalone proposal but is beyond the scope of a single worker.

## Files Changed

None — all experimental changes were reverted.

## Remaining Opportunities

- **Change NF hash contract**: Hash based on (pattern_shape, substitution_fingerprint) rather than materialized TermIds. Would allow truly lazy NFs but requires careful correctness analysis.
- **Structural sharing in term store**: If the term store could represent f^k(x) as a single node with a "repeat depth" annotation, materialization cost drops to O(depth) instead of O(depth^2). This is a term store architecture change.
- **Bounded depth optimization**: For shallow rewrites (depth < 16), the current approach is already fast. The O(depth^2) only matters for stress-test-scale depths. Consider whether the benchmark is representative of real workloads.
