# Investigation: ChrState Option<Arc> to Eliminate Empty-Program Clone

## Summary

Changed `ChrState.program` from `Arc<ChrProgram<T>>` to `Option<Arc<ChrProgram<T>>>` to skip the atomic `Arc::clone` (fetch_add) when the program is empty (NoTheory case). The secondary benchmark improved ~4%, but the primary benchmark regressed ~3.3%.

**Verdict:** DISCARD
**Regression:** ~3.3% slower on primary (U=12/100)

## Problem

Post-Round-6 profiling showed `ChrState::clone` at 2.10% of total runtime. ChrState contains `program: Arc<ChrProgram<T>>`, and cloning it does `Arc::clone` which performs an atomic `fetch_add`. For `NoTheory` workloads (like `recursive_even_backward_first64`), the ChrProgram is always empty, but the atomic increment still happens on every clone.

The hypothesis was that making `program` an `Option<Arc<ChrProgram<T>>>` where `None` represents an empty program would make clone for the empty case a simple `None` copy — no atomic operation needed.

## Approach

Changed `ChrState.program` from `Arc<ChrProgram<T>>` to `Option<Arc<ChrProgram<T>>>`. Added helper methods `program_ref()` and `program_id()` to unwrap the Option at access sites. Updated Clone impl to only Arc::clone when `Some`. Updated all test sites to use `.as_ref().unwrap()` for program field access.

## Results

### Primary Workload: recursive_even_backward_first64
- Baseline timings: [13.30, 13.30, 12.99, 12.99, 12.71, 12.89, 12.85, 13.23, 13.40, 12.89]
- Optimized timings: [13.77, 13.22, 13.78, 13.38, 13.41, 13.24, 13.66, 13.43, 13.75, 13.16]
- Baseline median: 12.99ms
- Optimized median: 13.42ms
- U statistic: 12/100
- Change: -3.3% (regression)

### Secondary Workload: treecalc_first16
- Baseline median: 0.75ms
- Optimized median: 0.72ms
- U statistic: 90/100
- Change: +4.0% (improvement)

## Why It Failed

The optimization successfully eliminated the Arc atomic clone for empty ChrState (evidenced by the 4% secondary benchmark improvement). However, it regressed the primary benchmark because:

1. **Option indirection on every program access.** Wrapping `program` in `Option` means every access in `solve_to_fixpoint`, `program_ref()`, and other hot code paths now goes through `Option::as_ref().expect()` — an extra branch that didn't exist before. These accesses happen far more frequently than clones.

2. **Struct layout changes.** `Option<Arc<...>>` changes the niche optimization characteristics of ChrState, potentially altering field offsets and cache alignment in ways that pessimize the hot path.

3. **Compiler optimization interference.** The compiler could previously prove that `self.program` was always valid and optimize accordingly. With `Option`, it must emit conditional code even when the None path is unreachable in practice.

The fundamental lesson: profiler-reported 2.1% cost in `Arc::clone` was real, but eliminating it by adding Option indirection to ALL program accesses (not just clone) was a net negative. The clone savings on the cold path were outweighed by Option unwrapping overhead on the hot evaluation loop.

## What Would Be Needed

A better approach would avoid adding indirection to program accesses:
- Use a `static` empty `ChrProgram` singleton (avoiding Arc::clone without Option overhead)
- Restructure code so ChrState is not cloned as frequently
- Use a no-op Arc-like wrapper that skips the atomic for known-singleton cases

## Files changed (in worktree, not merged)

- `src/chr/mod.rs` — Changed ChrState.program to Option<Arc<ChrProgram<T>>>, updated access sites
- `src/chr/tests.rs` — Updated tests for Option program field
- `src/parser.rs` — Updated tests for Option program field
- `src/kernel/compose.rs` — Updated tests for Option program field
