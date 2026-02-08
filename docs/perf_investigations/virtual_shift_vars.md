# Investigation: Virtual shift_vars Elimination

## Summary

Eliminated physical term tree rewriting for variable renaming-apart in `compose_nf` and `meet_nf` by combining the shift operation with subsequent substitution application into a single pass. ~8.5% improvement on `program_synth_flip` (same-session comparison).

**Baseline:** 4.58s (median, same-session: 4.35, 4.38, 4.44, 4.50, 4.56, 4.60, 4.61, 4.62, 4.64, 4.67)
**After:** 4.19s (median, same-session: 4.04, 4.16, 4.17, 4.19, 4.19, 4.19, 4.22, 4.28, 4.34, 4.36)
**Improvement:** ~8.5% (same-session comparison)
**Regression:** None observed on tabling (`recursive_even_backward_first64` ~21.9ms) or treecalc (~1.57ms) workloads.

## Problem

Both `compose_nf` and `meet_nf` rename-apart the second operand's variables before matching. The old approach physically walked both lhs and rhs term trees, rewriting every `Var(j)` to `Var(j + offset)` and interning all intermediate App nodes. These shifted terms were then immediately consumed by `match_term_lists` (which applies a substitution and matches) and `apply_subst_list`.

From DWARF-based profiling of `program_synth_flip`:
- `compose_nf` = 71.52% of total time
- Within compose_nf: `shift_vars_list` = 9.95%

The shifted intermediate terms served no purpose beyond being immediately fed to substitution/matching operations. Every App node in the shifted tree was:
1. Created by `shift_vars` (tree walk + intern)
2. Traversed by `apply_subst`/`match_terms_combined` (tree walk + read lock)
3. Discarded

## Solution

A single `apply_subst_core<const SHIFTED: bool>` function that handles both standard substitution and shifted substitution via const generic specialization. Work items carry a `Visit(TermId, bool)` tag where the bool indicates "raw" (unshifted) terms:

- **raw=true**: Variables use a pre-created `shifted_vars` lookup table (`shifted_vars[j] = Var(j + offset)`) before resolving through the substitution. App children inherit raw-ness.
- **raw=false**: Standard `apply_subst` behavior, no shifting. Terms from substitution bindings are always non-raw.

Public API:
- `apply_subst(term, subst, terms)` → calls `apply_subst_core::<false>` (no shifting overhead)
- `apply_subst_shifted(term, subst, var_offset, shifted_vars, terms)` → calls `apply_subst_core::<true>`

### Key design decisions

1. **Pre-created shifted vars**: `terms.var(j + offset)` calls `intern()` which acquires a write lock. This would deadlock with the read lock held during term traversal. Solution: pre-create all shifted var TermIds before any traversal begins, stored in a `SmallVec<[TermId; 8]>`.

2. **Const generic specialization**: The `SHIFTED` const generic ensures the compiler generates two separate monomorphizations. Branches guarded by `SHIFTED && raw` fold to `false` in the non-shifted version, eliminating all shifting overhead on the hot path (`apply_subst`). Without this, a runtime-only `raw` flag caused ~5% regression because the compiler couldn't prove through the SmallVec work stack that `raw` was always false.

3. **BuildApp optimization preserved**: The "all children unchanged" fast path still works. For raw terms with variable children, it correctly fails (shifted children differ from originals), causing a new term to be interned. For resolved terms, it works as before.

4. **Unified match_term_lists**: `match_term_lists` delegates to `match_term_lists_shifted` with empty `shifted_vars`, and `apply_subst_shifted` with empty shifted_vars delegates to `apply_subst`. This eliminates the near-duplicate `match_term_lists` implementation.

## Files changed

- `src/subst.rs`: Unified `apply_subst` and `apply_subst_shifted` into `apply_subst_core<const SHIFTED: bool>`. Both public functions are thin wrappers with fast-path checks.
- `src/kernel/util.rs`: Added `pre_create_shifted_vars`, `apply_subst_shifted_list`, `match_term_lists_shifted`. `match_term_lists` now delegates to `match_term_lists_shifted`. Deleted `shift_vars` and `shift_vars_list` (dead code).
- `src/kernel/compose.rs`: Replaced `shift_vars_list` + `match_term_lists` + `apply_subst_list` with virtual-shift equivalents.
- `src/kernel/meet.rs`: Same pattern. First `match_term_lists` uses virtual shift; second operates in the shared namespace (no shift needed).

## Why 4% instead of 10%

The profiling showed `shift_vars_list` at ~10% of compose_nf time (~6% of total). However:

1. **Pre-creating shifted vars has overhead**: Each `terms.var(j + offset)` call does a hash + lock operation. For b_max_var of ~5, this is 6 intern operations per compose_nf call.

2. **BuildApp comparison always fails for raw terms**: The "all children unchanged" optimization never triggers for raw App nodes with variable children, since shifted results differ from unshifted originals. This means we always intern new terms for these nodes — the same interning that shift_vars would have done, just deferred.

3. **The real saving is avoiding double traversal**: We no longer walk the term tree once to shift and again to substitute. The single-pass traversal saves ~half the read_lock acquisitions and cache misses, but the interning cost is comparable.

## Remaining opportunities

The dominant cost in compose_nf is now `apply_subst` and `match_terms_combined`, each doing per-node read_lock acquisition. Potential next investigations:
- Batch read_lock across entire match_term_lists operation (hold lock for the whole element-wise loop)
- Avoid interning intermediate substituted terms that are immediately matched
- Structural hashing to skip matching on identical subtrees
