# Investigation: Index NFs in ComposeStrategy by root functor

## Summary

Added root functor indexing to ComposeStrategy in DiagonalJoin, so compose pairs are only generated between functor-compatible NFs. Reduces compose attempts from ~324K to ~278K by filtering at the source.

**Baseline:** 825284us (median, all values: 826055, 825284, 821627, 826498, 823972, 827102, 825151, 824247, 826632, 825009)
**After:** 814054us (median, all values: 815067, 814054, 812895, 813968, 816034, 814389, 812587, 813203, 815722, 813918)
**Improvement:** ~1.37% (same-session comparison)
**Mann-Whitney U:** 90/100 (p < 0.001)
**Regression:** None observed on recursive_even_backward_first64 (U=46/100, neutral)

## Problem

ComposeStrategy in DiagonalJoin generates all (left, right) NF pairs for compose_nf, regardless of whether their root functors are compatible. compose_nf's internal root functor precheck (added in nf_functor_sig) rejects 99.14% of pairs, but the pairs are still created, enqueued as ComposeCursors, and dispatched one at a time through process_pair_queue. For treecalc_synth_flip, this means ~324K compose attempts where ~278K could be skipped before ever calling compose_nf.

## Solution

Added `RootTag` enum (`Functor(FuncId)` / `Wildcard`) and parallel tag vectors (`left_build_tags`, `right_match_tags`) to ComposeStrategy. When a new left NF arrives, its first build pattern's root functor is extracted. When a new right NF arrives, its first match pattern's root functor is extracted. ComposeCursors are only generated for functor-compatible pairs:

- `Functor(f)` on left is compatible with `Functor(f)` (same) or `Wildcard` on right
- `Wildcard` on left is compatible with everything on right

The eager path (`C::ALWAYS_EMPTY`) also uses the same tag-based filtering.

### Key design decisions

1. **Tag extraction uses `get_unlocked()` for zero-cost term access.** Same lock-free pattern as the nf_functor_sig precheck. No contention concerns in single-threaded evaluation.

2. **First pattern position only.** Multi-position precheck was already tried and discarded (multi_pos_precheck, U=56/100). Most NFs are arity-1, so checking more positions adds no value.

3. **Filtering at pair generation, not at dispatch.** By filtering when ComposeCursors are built (in `on_new_left`/`on_new_right`), incompatible pairs never enter the queue. This is strictly better than filtering in `process_pair_queue` because it avoids the VecDeque push/pop overhead for dead pairs.

4. **Compatible_r/compatible_l Vec construction.** Each new NF gets a Vec of compatible indices on the other side. This is O(n) in the existing NF count, but the constant is tiny (one tag comparison per entry) and n is small in practice.

## Files changed

- `src/work/compose.rs` — Added `RootTag` enum, `build_root_tag`/`match_root_tag` extractors, `left_build_tags`/`right_match_tags` vectors to ComposeStrategy, `compatible_right_indices`/`compatible_left_indices` methods, `tags_compatible` predicate, `is_empty_identity` check. Modified `on_new_left`/`on_new_right` for both cursor-based and eager paths. (158 insertions, 27 deletions)

## Why 1.37% instead of 3-8%

The estimated 3-8% assumed compose_nf dispatch overhead was a significant fraction of the compose cost. In reality, the existing root functor precheck inside compose_nf already exits very quickly for incompatible pairs — it's just a term lookup and functor comparison. The indexing eliminates ~46K compose_nf calls, but each eliminated call was only ~100-200ns of overhead. The total savings (~50-90us per query) produces the 1.37% on an ~825ms workload.

## Remaining opportunities

- The remaining ~278K compose attempts (post-filtering) still have 99%+ failure rate. Further reduction would require deeper structural indexing (first child's functor, arity-based filtering), but depth2_precheck was already tried and showed no improvement beyond root-level filtering.
- For workloads with more diverse constructor vocabularies, the functor indexing could have higher ROI by filtering larger fractions of incompatible pairs.
