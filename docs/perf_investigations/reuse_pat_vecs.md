# Investigation: SmallVec Reuse in instantiate_pat

## Summary

Replacing heap-allocated `Vec` with stack-allocated `SmallVec` in `instantiate_pat` showed a consistent ~2-4% median improvement but did not reach statistical significance on treecalc_synth_flip (U=72/100 first run, U=66/100 second run).

**Baseline (run 1):** ~72.9 ms median
**After (run 1):** ~71.4 ms median
**Improvement (run 1):** ~2.1%
**Mann-Whitney U (run 1):** 72/100 (not significant, p > 0.05)

**Baseline (run 2):** ~73.1 ms median
**After (run 2):** ~71.5 ms median
**Improvement (run 2):** ~2.2%
**Mann-Whitney U (run 2):** 66/100 (not significant)

## Problem

In the CHR body execution path, `instantiate_pat` (called from `collect_args` via `eval_arg_expr`) allocates fresh `Vec<(PatId, usize)>` and `Vec<TermId>` on every call. Since `exec_body_inline` is recursive (rules fire other rules in a DFS chain), `instantiate_pat` can be called many times per normalize_owned invocation. Each call allocates and deallocates two Vecs. collect_args is 2.01% of runtime, exec_body_inline is 9.35%.

## Solution (attempted)

Replaced the two `Vec` allocations in `instantiate_pat` with `SmallVec`:

```rust
// Before:
let mut stack: Vec<(PatId, usize)> = vec![(root, 0)];
let mut out: Vec<TermId> = Vec::new();

// After:
let mut stack: SmallVec<[(PatId, usize); 8]> = smallvec![(root, 0)];
let mut out: SmallVec<[TermId; 8]> = SmallVec::new();
```

This eliminates heap allocation for patterns with ≤8 nodes, which covers the vast majority of CHR patterns in the treecalc workload.

### Key design decisions

1. Used SmallVec instead of thread-local pool — simpler, no recursion concerns (instantiate_pat can be called recursively through exec_body_inline).
2. Capacity of 8 chosen to cover typical pattern depths (tree calculus patterns are shallow).
3. SmallVec is already widely used throughout the codebase.

## Files changed

- `src/chr/mod.rs` — Changed `instantiate_pat` to use `SmallVec<[(PatId, usize); 8]>` and `SmallVec<[TermId; 8]>` instead of `Vec`

## Why not significant

The improvement is real but small (~2-3%), and the treecalc_synth_flip benchmark has ~5-8% coefficient of variation (run-to-run timing variance), which masks the signal. The U statistic of 72/100 is tantalizingly close to the 73 threshold — with lower variance or a larger sample size, this might reach significance.

The fundamental issue is that `instantiate_pat` is only called for `ArgExpr::Pat` variants. Most body instruction args are `ArgExpr::RVar` (direct variable lookup, O(1)) or `ArgExpr::Const` (constant, O(1)). The Pat path — which creates compound terms from matched variables — is less common. Additionally, mimalloc makes Vec allocation very fast (~15ns), so eliminating it saves only a few nanoseconds per call.

## Remaining opportunities

- The borderline result (U=72) suggests this optimization has a small but real effect. It could be combined with other small improvements for a cumulative benefit.
- Thread-local RVarEnv pooling in exec_body_inline was considered but mimalloc makes RVarEnv::new O(1) (see iterative_body_dfs investigation).
- The exec_body_inline + collect_args hotspot (~11.36% combined) is dominated by actual matching and term construction work, not allocation overhead.
