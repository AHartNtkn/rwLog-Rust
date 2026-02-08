# DropFresh Identity Fast-Path Investigation

## Summary

Investigated whether adding fast-paths for identity DropFresh in `collect_tensor`, `factor_tensor`, and `direct_rule_terms` could improve performance. Found that **DropFresh is 100% identity for the critical benchmark workload** (`recursive_even_backward_first64`), but the optimization produces **no measurable improvement** because the kernel (compose_nf, meet_nf, matching) is only ~3-5% of total runtime at the current ~32ms baseline.

**Result: Low ROI.** The fast-paths are correct and principled but the target is too small. The investigation confirms that further kernel-level optimizations cannot meaningfully improve performance for tabling-heavy workloads — the bottleneck is entirely in evaluation infrastructure.

## Hypothesis

DropFresh identity is the common case for typical programs. When DropFresh is identity, `collect_tensor` and `factor_tensor` do unnecessary work: Vec allocations, HashSet/HashMap construction, and var renaming traversals that are all no-ops. Fast-pathing these could reduce kernel overhead.

## Methodology

### Step 1: Instrument identity frequency

Added perf counters to measure:
- How often `a.drop_fresh` and `b.drop_fresh` are identity in compose_nf/meet_nf
- How often `collect_tensor` receives identity DropFresh
- How often `factor_tensor` produces identity DropFresh results
- Arity distribution (avg and max)

### Step 2: Measure across workloads

Ran instrumented engine on four workload types:
1. **even64** — critical tabling benchmark (mutual recursion, 64 answers)
2. **compose chain** — simple sequential composition (a→b→c→d)
3. **meet workload** — conjunction with non-trivial variable dropping
4. **non-identity workload** — explicit variable dropping and fresh introduction

### Step 3: Implement and benchmark

Added identity fast-paths to `collect_tensor`, `factor_tensor`, and `direct_rule_terms`. Benchmarked against baseline.

## Data: Identity Frequency

### even64 (critical workload)

```
compose_nf calls: 378  (success: 315, fail: 63)
  a.df identity: 378 (100.0%)
  b.df identity: 378 (100.0%)
  both identity: 378 (100.0%)

meet_nf calls: 0

collect_tensor: 756 calls, 756 identity (100.0%)
  avg arity: 0.50, max arity: 1

factor_tensor: 315 calls, 315 identity results (100.0%)
engine steps: 4793, emits: 64
```

**100% identity across the board.** The even/odd program has rules where every LHS variable appears in the RHS and vice versa: `z -> yes` (0 vars), `(s $n) -> $n` (1 var, shared). Tabling preserves this property.

### compose chain (a→b→c→d)

```
compose_nf: 2 calls, both identity: 2 (100%)
collect_tensor: 4 calls, 4 identity (100%)
factor_tensor: 2 calls, 2 identity (100%)
```

100% identity — ground terms have no variables to route.

### meet workload: `(f $x $y) -> $x & (f $a $b) -> $b`

```
meet_nf: 1 call, a identity: 0%, b identity: 0%, both: 0%
collect_tensor: 2 calls, 0 identity (0%)
factor_tensor: 1 call, 1 identity result (100%)
```

**0% identity for inputs** because `(f $x $y) -> $x` drops `$y` and `(f $a $b) -> $b` drops `$a`. But the **result** is identity because the meet constrains them to produce the same output.

### non-identity workload: `(f $x $y) -> $x ; $a -> (g $a $b)`

```
compose_nf: 1 call, a identity: 0%, b identity: 0%, both: 0%
collect_tensor: 2 calls, 0 identity (0%)
factor_tensor: 1 call, 0 identity (0%)
```

Correctly non-identity — variable dropping and fresh introduction.

## Why This Doesn't Help

The identity rate is 100% but the absolute cost is negligible:

| Operation | Calls (even64) | Per-call cost at arity 0-1 | Total |
|---|---|---|---|
| collect_tensor | 756 | ~30-50ns (Vec alloc + identity check bail-out) | ~30µs |
| factor_tensor | 315 | ~100-200ns (HashSet/HashMap for 0-1 entries) | ~50µs |
| **Total kernel overhead** | | | **~80µs** |

~80µs out of ~32ms = **0.25% of total runtime.**

The existing `apply_var_renaming` function already has an identity fast-path (line 443 of nf.rs) that catches identity mappings and returns the original TermId. So the per-call waste in `collect_tensor` was already small — just the Vec allocation for rhs_map and the loop setup before hitting the existing bail-out.

For `factor_tensor`, the HashSet/HashMap construction for 0-1 entries is essentially free — the allocator returns immediately for these sizes.

## Benchmark Results

| Benchmark | Baseline | With fast-paths | Change |
|---|---|---|---|
| recursive_even_backward_first64 | ~32.5ms | ~33.0ms | +1.5% (noise) |

Criterion: "Change within noise threshold" (p = 0.03, within default threshold).

Multiple runs confirmed: no measurable difference in either direction.

## What Was Implemented (kept)

Despite no measurable improvement, the fast-paths are correct and principled:

1. **`collect_tensor` identity fast-path** (`src/nf.rs`): When `nf.drop_fresh.is_identity()`, returns `RwT { lhs: clone, rhs: clone, constraint: clone }` directly, skipping Vec allocation and var renaming traversal.

2. **`factor_tensor` identity fast-path** (`src/nf.rs`): When `lhs_vars == rhs_vars`, builds identity DropFresh directly, skipping 2 HashSet + 1 HashMap + 1 Vec construction.

3. **`direct_rule_terms` identity fast-path** (`src/nf.rs`): When `nf.drop_fresh.is_identity()`, returns `(lhs, rhs)` directly, skipping rhs_map construction.

4. **`is_identity()` marked `#[inline]`** (`src/drop_fresh.rs`): Ensures the check is inlined on hot paths.

## Key Insight

After the cumulative 3.28× speedup (105ms → 32ms), the kernel operations (compose_nf, meet_nf, matching) account for only ~3-5% of runtime. **No kernel-level optimization can produce meaningful improvement for tabling-heavy workloads.** The remaining bottlenecks are all evaluation infrastructure:

| Category | Estimated % of 32ms |
|---|---|
| step_node dispatch | ~15-17% |
| DiagonalJoin/ComposeWork stepping | ~10-14% |
| Drop overhead | ~8-10% |
| Table::answer_at NF cloning | ~6-8% |
| malloc/cfree | ~5-7% |
| Kernel (compose/meet/matching) | ~3-5% |

Future optimization efforts should target the infrastructure categories, not the kernel.

## Also Investigated: Perf Counter Infrastructure

Added DropFresh-specific counters to the perf_counters module for ongoing measurement capability:
- `compose_df_a_identity`, `compose_df_b_identity`, `compose_df_both_identity`
- `meet_df_a_identity`, `meet_df_b_identity`, `meet_df_both_identity`
- `collect_tensor_calls`, `collect_tensor_identity_skips`
- `factor_tensor_calls`, `factor_tensor_identity_results`
- `collect_tensor_max_arity`, `collect_tensor_total_arity`

These are gated behind the existing `enabled()` check and add zero overhead when disabled.

## Decision

**Keep fast-paths, mark investigation complete.** The optimization is correct but below the noise floor for current workloads. The perf counters and measurement tests provide ongoing instrumentation for future workloads where higher-arity or non-identity DropFresh might become relevant.
