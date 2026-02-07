# Investigation: Fixpoint Verification Overhead

**Status:** Completed — low ROI for current workloads. Real bottleneck identified elsewhere.
**Backlog item:** Tabling/Recursion Strategy #4, #5
**Branch:** `fast-flip`
**Triggered by:** compose/meet memoization investigation revealed exact-2x duplication caused by fixpoint verification.

## Hypothesis

The tabling fixpoint iteration re-runs the entire producer from scratch to verify fixpoint (no new answers). This verification pass duplicates all compose_nf calls and engine steps. Eliminating or reducing this verification pass could cut tabled-recursive evaluation time by ~50%.

## Architecture

### How fixpoint iteration works (src/work/fix.rs)

When a table's producer exhausts:
1. Check `has_new = answers_len() > iteration_start_len`
2. If `has_new`: call `make_replay_producer` to rebuild the ENTIRE producer from scratch, re-run
3. If `!has_new`: fixpoint confirmed, mark table as Done

`make_replay_producer` creates a brand-new `PipeWork` from the `ProducerSpec`, which includes the full relation body. The self-recursive call uses `CallMode::ReplayOnly` to replay answers from the table rather than re-entering the producer.

### No dependency tracking between tables

`Tables<C>` is a flat `DashMap<CallKey, Arc<Table>>`. There is:
- No dependency graph between tables
- No global epoch counter for answer changes
- No tracking of which tables a producer consulted
- No way to determine "did any other table change?" without re-running

### Why exactly 2x duplication for deterministic relations

For a deterministic relation producing 1 answer per table:
1. **Pass 1**: Producer discovers the answer. `has_new = true`.
2. **Pass 2**: Producer re-runs from scratch. Same compose_nf calls. No new answers. `has_new = false`. Fixpoint.

Every compose_nf call happens twice. For relations with N answers per table, you'd get 2 full passes minimum (Pass 1 finds all N answers; Pass 2 confirms no more).

## Wall-Clock Impact Assessment

| Case | Median µs | Steps | Compose Dup% | Est. µs wasted |
|------|----------:|------:|-------------:|---------------:|
| recursive_add_forward_n8 | 508 | 160 | 50% | ~254 |
| recursive_add_backward_n8 | 830 | 268 | 50% | ~415 |
| recursive_add_forward_n24 | 3,224 | 448 | 50% | ~1,612 |
| recursive_add_backward_n24 | 6,313 | 1,348 | 50% | ~3,157 |
| **recursive_even_backward_first64** | **92,684** | **4,793** | **0%** | **0** |
| treecalc_first16 | 1,787 | 331 | 0% | 0 |

### Key finding: the heaviest workload is unaffected

`recursive_even_backward_first64` at **93ms** dominates the corpus runtime but has **zero verification overhead**. It uses mutual recursion (even/odd) in a backward streaming mode where every compose_nf pair is unique. The `add` cases that ARE affected top out at 6.3ms with ~3.2ms wasted.

## Per-Step Cost Analysis

| Case | µs/step | Pattern |
|------|--------:|---------|
| identity_atom | 1.4 | trivial |
| recursive_add_forward_n24 | 7.2 | self-recursive, deterministic |
| recursive_even_backward_first64 | **19.3** | mutual recursion, streaming |

The 2.7x higher per-step cost for `recursive_even` is likely caused by:

1. **Or tree growth**: Each answer adds a branch to the search tree. After 64 answers, ~64 Or branches accumulate. Each `step_or` walks the left spine, steps the leaf, and rebuilds — cost grows linearly with tree depth, making total Or-management cost O(n²) in answers.

2. **Mutual recursion tabling**: Two tables (even/odd) with lock acquisition, producer state checks, DashMap lookups on every FixWork::step() call.

3. **No compose reuse**: All 378 compose calls are unique (different Peano depths at each level).

## Potential Optimizations Evaluated

### 1. Global answer epoch on Tables
Add an `AtomicU64` that increments on every new answer insertion. Check it at fixpoint verification time.

**Verdict:** Does not help. The verification pass is triggered by `has_new = true` (this table's OWN new answers), not by external tables. The epoch check would only help if `has_new` is false but another table changed — which is already handled correctly.

### 2. Semi-naive fixpoint (delta replay)
Instead of replaying ALL answers through the self-recursive call, replay only the delta (`answers[iteration_start_len..]`).

**Verdict:** Correct approach for multi-iteration fixpoints, but offers **zero savings** for the current workloads. Each table produces all its answers in a single pass, so the delta IS the entire answer set. Semi-naive helps when you need 3+ iterations, which doesn't occur in the current corpus.

### 3. Skip verification for self-contained tables
If a table's producer only consulted itself (no other table), fixpoint might be provable without re-running.

**Verdict:** Requires dependency tracking that doesn't exist. Implementation cost exceeds benefit for current workloads.

### 4. Incremental producer suspension
Suspend the producer tree rather than discarding it. Resume only when dependent tables update.

**Verdict:** Most architecturally sound but highest implementation complexity. Not justified by current workload data.

## Conclusion

**Fixpoint verification optimization has low ROI for current workloads.** The maximum savings is ~3ms on a 6ms case. The heaviest workload (93ms) is completely unaffected.

The investigation reveals two more promising optimization targets:

1. **Or tree management** (Backlog: Disjunction/Or Execution #1, #5): The O(n²) cost of Or rotation as the search tree grows with streaming answers. This is the dominant cost in the heaviest workload. Flattening nested Or structures into a branch pool and batching branch stepping would address this.

2. **Per-step overhead for mutual recursion tabling**: Lock contention, DashMap lookups, and FixWork state machine transitions on every step. Reducing this overhead would directly improve the 19.3µs/step cost.

## Artifacts

- Timing data from `perf_corpus_run` with labeled cases
- Hooks (not yet wired): `record_fixpoint_producer_start`, `record_fixpoint_verification_start`, `record_fixpoint_verification_step` exist in `perf_counters.rs` but are not called from `fix.rs`
- Instrumentation: pair hash tracking in `perf_counters.rs` (active for meet via `meet.rs`)
- Investigation test: `tests/compose_meet_dedup_investigation.rs`
