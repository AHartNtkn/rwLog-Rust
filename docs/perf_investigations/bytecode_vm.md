# Investigation: Bytecode VM Backend

## Summary

Profiled the engine to quantify dispatch overhead before implementing a bytecode VM. DISCARD: dispatch overhead is only 2-4% of total time. CHR constraint processing (35%), substitution/matching (22%), and compose_nf (6%) dominate. A bytecode VM would add enormous complexity for zero measurable benefit. Confirms all 4 prior dispatch investigations (step_dispatch U=67, engine_loop_inlining U=39, streamline_fixwork U=50, compile_rel_plan U=61).

## Profiling Data (treecalc_synth_flip, perf record, ~1760 samples)

| Category | % of total | Key functions |
|----------|-----------|---------------|
| CHR constraint processing | ~35% | exec_body_inline (18.3%), normalize_owned (9.9%), collect_args (3.9%), apply_subst (2.8%) |
| Substitution/matching | ~22% | apply_subst (15.0%), shift_term (5.1%), occurs_unlocked (1.3%) |
| compose_nf kernel | ~6% | compose_nf (4.7%), factor_tensor (0.9%), build_remap_map (0.6%) |
| Term store (hash-consing) | ~5% | HashMap::get_inner (3.9%), intern_unlocked (1.0%) |
| Memory allocation | ~10% | mi_free (3.7%), mi_malloc variants (3.5%), Vec reserve/grow (1.1%) |
| Arc refcounting | ~2% | Arc::make_mut (0.7%), Arc::drop_slow (0.7%), drop_in_place (0.4%) |
| **Dispatch overhead** | **~2-4%** | step_node (~1.8%), ComposeWork::step_in_place (0.4%), AndGroup::step (1.9%) |

## Why It Failed

1. **Dispatch overhead is only 2-4%.** Even a perfect bytecode VM eliminating ALL dispatch would yield at most 2-4% improvement — well below significance threshold.

2. **Actual computation dominates at ~74%.** CHR + substitution/matching + compose_nf account for three-quarters of execution. This is genuinely useful work.

3. **Branch predictor already handles dispatch efficiently.** The 4-variant Node enum and Work enum dispatch is well-predicted by modern CPUs.

4. **Fifth confirmation of dispatch ceiling.** Consistent with step_dispatch (U=67), engine_loop_inlining (U=39), streamline_fixwork (U=50), compile_rel_plan (U=61).

## Files changed

None — profiling only.

## Remaining opportunities

Based on the profile breakdown, the highest-ROI targets are:
- **CHR constraint processing (35%)**: exec_body_inline alone is 18.3%. Any improvement to inline body execution would have outsized impact.
- **apply_subst (15%)**: Still the single largest non-CHR function. Despite prior optimizations (var_range skip, ground bit, fused factor), 15% remains.
- **Memory allocation (10%)**: mi_free 3.7% + mi_malloc 3.5%. Reducing allocation count (not just switching allocators) could help.
- **normalize_owned (9.9%)**: Despite the commutative hash cache (76.1% improvement), this is still ~10% of total time. Further cache hit rate improvements could help.
- **shift_term (5.1%)**: Despite the HashMap cache, still 5%. The cache itself may be the overhead (HashMap operations).
- **Term store hash-consing (5%)**: Irreducible hash table probing and equality comparison cost.
