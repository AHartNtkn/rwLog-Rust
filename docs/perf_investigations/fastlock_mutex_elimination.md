# FastLock: Mutex Elimination for Single-Threaded Tabling

## Summary

Replaced `parking_lot::Mutex` in `Table<C>` (the tabling answer/producer store) with a zero-cost `FastLock<T>` wrapper that performs no atomic operations. The evaluator is single-threaded, so the Mutex was pure overhead.

**Result: ~20% improvement on the critical recursive workload.**

- `recursive_even_backward_first64`: ~85ms → ~65-71ms
- No regressions on non-tabling workloads
- All 716 tests pass

## Hypothesis

The per_step_cost_decomposition investigation identified Mutex overhead as ~3-6% of execution. However, that estimate was based on profile percentages, not actual call counts. The hypothesis was that the true Mutex overhead is much higher because:

1. The tabling API uses per-field locking (each Table method locks, does one thing, unlocks)
2. FixWork::step makes multiple Table method calls per step
3. There are far more FixWork steps than engine steps (many FixWork handles per tabled call)

## Methodology

### Step 1: Fresh profiling (post-CallKey-fix)

Profiled `recursive_even_backward_first64` at ~85ms baseline. Top functions:

| Function | Self % | Category |
|---|---|---|
| PipeWork::step | 10.7% | Dispatch |
| Table::answer_at | 9.4% | Lock + optional NF clone |
| step_table_producer | 6.3% | Multiple lock calls |
| Table::set_producer_node | 5.1% | Lock + node store/drop |
| drop_in_place\<Work\> | 5.1% | Destruction |
| FixWork::clone | 4.5% | Clone per step |
| Table::set_producer_task_active | 2.0% | Lock + bool set |

### Step 2: Instrumented call counting

Added atomic counters to all Table lock sites and FixWork::step. Results for the critical workload:

| Metric | Value |
|---|---|
| Engine steps | 4,793 |
| FixWork::step calls | 216,806 |
| answer_at calls | 433,612 |
| answer_at hits (clone path) | 4,096 (0.9%) |
| Total Mutex lock operations | 1,738,671 |
| Mutex locks per FixWork step | 8.0 |

**Key finding: 99.1% of `answer_at` calls return None** — the Mutex lock is pure waste on those paths. The prior assumption that `answer_at`'s 9.4% cost was mostly NF cloning was wrong. It was mostly Mutex overhead.

**1.74M Mutex operations** for producing 64 answers. At ~15-20ns per uncontended parking_lot lock/unlock, that's ~26-35ms of pure overhead, or **30-40% of total execution time**. The prior estimate of 3-6% was off by 5-10×.

### Step 3: FastLock implementation

Created `src/fast_lock.rs` — a zero-cost wrapper around `UnsafeCell<T>` with the same `.lock()` API as `parking_lot::Mutex<T>`:

- `FastLock::lock()` returns a `FastLockGuard` that derefs to `&mut T`
- No atomic operations, no memory barriers
- `unsafe impl Sync` is sound because the evaluator is single-threaded
- All methods are `#[inline(always)]`

Replaced both `Mutex<TableAnswers<C>>` and `Mutex<TableProducer<C>>` in the `Table` struct.

### Step 4: Measurement

**Critical workload** (`recursive_even_backward_first64`):
- Before: ~85ms (median across multiple runs)
- After: ~65-71ms (range across multiple runs, system noise)
- Improvement: **~17-23%**

**Non-tabling workloads** (no change expected or observed):
- identity_atom: ~9µs (no tabling)
- conjunction_selective: ~37µs (no tabling)
- treecalc_first_answer: ~34µs (uses tabling but tiny workload)

### Step 5: Post-change profiling

The cost landscape shifted dramatically:

| Function | Before | After | Change |
|---|---|---|---|
| Table::answer_at | 9.4% | 0.7% | -8.7% |
| Table::set_producer_node | 5.1% | <0.3% | -5.1% |
| step_table_producer | 6.3% | 2.9% | -3.5% |
| Table::set_producer_task_active | 2.0% | <0.3% | -2.0% |
| **Total Table overhead** | **22.8%** | **~4%** | **-19%** |

## Why the prior estimate was so wrong

The per_step_cost_decomposition estimated Mutex-to-RefCell at 3-6% based on the `set_producer_task_active` profile entry (2.0%). The reasoning was: "if a trivial bool-set with Mutex is 2%, then Mutex overhead is roughly 2% of the total."

This was wrong because:

1. **Spread across many functions**: The Mutex cost wasn't concentrated in one function — it was spread across `answer_at`, `set_producer_node`, `step_table_producer`, `is_done`, `try_mark_producer_active`, `answers_len`, etc. Each individually looked small, but they added up to ~23%.

2. **Call frequency was unknown**: Without counting actual calls, there was no way to know that `answer_at` was called 433K times (2× per FixWork step) with a 0.9% hit rate. The profile showed 9.4% for `answer_at` but attributed most of it to "NF cloning" rather than "Mutex locking on the miss path."

3. **FixWork step count was unknown**: 216K FixWork steps vs 4.8K engine steps means 45× more Table method calls than naively expected. Each FixWork step makes ~8 Mutex calls.

## Safety considerations

`FastLock` uses `unsafe impl Sync` and `UnsafeCell`. This is correct only when:
- The evaluator is single-threaded (current design)
- No other threads access Table contents

If parallel evaluation is ever added, `FastLock` must be replaced with a real Mutex or the parallelism must avoid sharing Tables across threads.

## Remaining optimization targets

After this change, the profile is now dominated by:

1. **PipeWork::step** (8.4%) — dispatch overhead
2. **FixWork::clone** (4.1%) — still cloning per step
3. **malloc/cfree** (6.3% combined) — allocation pressure
4. **drop_in_place\<Work\> + drop_in_place\<Node\>** (5.5% combined) — destruction
5. **DiagonalJoin::new/pull_side** (4.3% combined) — join overhead

The allocator (malloc/cfree/drop) combined is now ~12% — arena allocation could address this. FixWork::clone at 4.1% could benefit from further Arc-wrapping of remaining cloned fields.

## Files changed

- `src/fast_lock.rs` — New: zero-cost lock wrapper
- `src/lib.rs` — Added `pub mod fast_lock`
- `src/work/fix.rs` — Replaced `parking_lot::Mutex` with `FastLock` in Table struct
