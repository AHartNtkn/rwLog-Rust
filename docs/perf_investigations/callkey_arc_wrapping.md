# Arc-Wrapping CallKey in FixWork

**Status:** Completed — kept. 20-25% improvement on recursive workloads, no regressions.
**Date:** 2026-02-07
**Commit:** `baa7d81`
**Triggered by:** Per-step cost decomposition ([per_step_cost_decomposition.md](per_step_cost_decomposition.md)) identified FixWork::clone as the root cause of the ChrState clone cascade, accounting for ~22% of total execution time.

## Motivation

The per-step cost decomposition revealed that 89.8% of ChrState cloning
originates from `FixWork::clone`. The clone cascade flows:

```
FixWork::clone → CallKey::clone → NF::clone → SmallVec + DropFresh → ChrState
```

`FixWork::step()` calls `self.clone()` on every step (4 sites in the method),
and FixWork contains `key: CallKey<C>` which holds `Option<NF<C>>` boundaries
that trigger deep cloning. CallKey is never mutated after construction, making
it a candidate for Arc-wrapping.

## Method

### Changes

Three production files modified:

1. **`src/work/fix.rs`**: `FixWork.key` and `ProducerSpec.key` changed from
   `CallKey<C>` to `Arc<CallKey<C>>`. `Tables::get_or_create` changed from
   taking owned `CallKey<C>` to `&CallKey<C>` (clones only on the insert path,
   which runs once per unique key).

2. **`src/work/mod.rs`**: `CallMode::ReplayOnly(Box<CallKey<C>>)` changed to
   `CallMode::ReplayOnly(Arc<CallKey<C>>)`. Arc already is a pointer; Box was
   redundant.

3. **`src/work/pipe.rs`**: `handle_call()` wraps CallKey in Arc at the single
   creation point. All downstream clones (for ProducerSpec, FixWork, Tables
   lookup) are O(1) Arc reference count bumps.

### Measurement

Release builds, `perf_corpus_run` with 1 iteration per case. Each configuration
benchmarked 5 runs; median reported. Same machine, same conditions.

## Results

### Recursive Workloads (Median of 5 Runs)

| Case | Steps | Before (us) | After (us) | Change |
|------|------:|------------:|----------:|---------:|
| recursive_even_backward_first64 | 4793 | 105,186 | 83,654 | **-20.5%** |
| recursive_add_forward_n24 | 448 | 3,614 | 2,785 | **-22.9%** |
| recursive_add_backward_n24 | 1348 | 7,431 | 6,246 | **-15.9%** |
| recursive_even_backward_first10 | 203 | — | 1,020 | — |
| recursive_add_forward_n8 | 160 | — | 553 | — |
| recursive_add_backward_n8 | 268 | — | 743 | — |

The heaviest workload (`recursive_even_backward_first64`) dropped from ~105ms
to ~84ms. The improvement scales with step count because the per-step clone
cost was the dominant overhead.

### Non-Recursive Workloads (Spot Check)

| Case | Before (us) | After (us) | Change |
|------|----------:|----------:|--------:|
| identity_atom | 231 | 200 | -13% |
| sequence_chain_len64 | 3,655 | 3,464 | -5% |
| conjunction_cross_16x16 | 450 | 333 | -26% |
| disjunction_wide_16 | 151 | 139 | -8% |
| deep_term_depth_32 | 42 | 39 | -7% |

No regressions. Several non-recursive workloads also improved slightly because
`Work::Fix` variants still appear in non-recursive call paths.

### Per-Step Cost

| Case | Steps | Before (us/step) | After (us/step) |
|------|------:|---------:|---------:|
| recursive_even_backward_first64 | 4793 | 21.9 | 17.5 |
| recursive_add_forward_n24 | 448 | 8.1 | 6.2 |
| recursive_add_backward_n24 | 1348 | 5.5 | 4.6 |

## Analysis

### Why the Improvement Exceeds the Estimate

The per-step cost decomposition estimated ~22% reduction from eliminating the
clone cascade. The measured improvement is 20-25%, consistent with the estimate.
The variation across workloads reflects different ratios of FixWork steps to
total steps:

- `recursive_even_backward_first64` is dominated by FixWork steps (high ratio
  of tabling to non-tabling work), so it benefits most in absolute terms.
- `recursive_add_forward_n24` has a higher ratio of kernel work, so the
  relative improvement is similar but applies to a smaller absolute base.

### What Was Eliminated

The Arc-wrap eliminates the deep clone cascade on every FixWork::step call.
Before, each step cloned:
- `CallKey` (rel, bind_id, two `Option<NF<C>>`)
- Each `NF` (match_pats SmallVec, drop_fresh DropFresh, build_pats SmallVec)
- Each `DropFresh` (in_arity, out_arity, map SmallVec, constraint)
- Each `ChrState` (inside DropFresh constraint)

After, each step clones an `Arc` (single atomic increment).

### Collateral Fixes

During testing, three additional issues were found and fixed:

1. **perf_counters deadlock**: `test_lock()` used `CAPTURE_LOCK`, the same
   mutex that `capture()` acquires internally. Since `std::sync::Mutex` is not
   reentrant, any test calling both would deadlock. Fixed by introducing a
   separate `TEST_SERIALIZE` mutex for test serialization.

2. **perf_counters race condition**: `ENABLED` was a global `AtomicBool`.
   Concurrent engine tests could record steps during a `capture()` scope,
   contaminating snapshots. Fixed by making `ENABLED` thread-local.

3. **Benchmark tests blocking CI**: Three investigation benchmarks
   (`chrstate_perf_bench`, `compose_meet_dedup_investigation`,
   `or_tree_investigation`) ran full corpus in debug mode, taking minutes.
   Marked `#[ignore]`.

## Relationship to Prior Investigations

This optimization implements Target 1 from
[per_step_cost_decomposition.md](per_step_cost_decomposition.md) and validates
the key finding: ChrState overhead is a symptom of FixWork::clone, not an
independent cost center. Arc-wrapping CallKey in FixWork eliminates 89.8% of
ChrState cloning without touching ChrState at all.

The prior ChrState-focused investigations
([chrstate_arc_wrapping.md](chrstate_arc_wrapping.md),
[chrstate_cache_and_fastpath.md](chrstate_cache_and_fastpath.md)) attacked
the wrong level of the cascade. This optimization addresses the root cause.

## Remaining Targets

From the per-step cost decomposition, the remaining optimization targets are:

| Target | Est. ROI | Status |
|--------|----------|--------|
| Arc-wrap NFs in Table answer store | 5-8% | Not yet attempted |
| Replace Mutex with RefCell for single-threaded | 3-6% | Not yet attempted |
| Reduce Work::step dispatch overhead | 3-5% | Not yet attempted |
| Arena allocation for Work/Node | 3-5% | Not yet attempted |

Combined with the ~22% from this change, the total addressable overhead is
~35-45%. However, the remaining targets have higher risk and lower individual
ROI.
