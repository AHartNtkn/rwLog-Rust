# Investigation: ChrState Arc-Wrapping (Clone/Hash/Eq Optimization)

**Status:** Completed — not worth keeping; ~21% improvement attributable to hash caching, not Arc clone
**Backlog item:** ChrState Clone/Hash/Eq (Optimization Targets #1 and #2 from Or Tree investigation)
**Branch:** `fast-flip`
**Triggered by:** Or tree investigation identified ChrState clone/hash as consuming ~45% of execution time.

## Hypothesis

Wrapping ChrState internals in `Arc` should:
- Make Clone O(1) (two atomic ref bumps instead of deep copy) — targets the 21.8% clone overhead
- Cache frozen bytes via `OnceLock` — targets the 12.7% hash overhead
- Add `Arc::ptr_eq` fast path for Eq — targets the freeze_chr-in-eq overhead

Predicted speedup: ~2x on `recursive_even_backward_first64` (eliminating ~45% overhead).

## Method

### Implementation

Introduced `ChrStateInner<T>` containing all original fields, wrapped in `ChrState<T>` with:
```rust
pub struct ChrState<T: Theory> {
    inner: Arc<ChrStateInner<T>>,
    frozen: Arc<OnceLock<Vec<u8>>>,
}
```

Key design choices:
- `frozen` lives *outside* `inner` so `Arc::make_mut` on inner doesn't deep-clone the cache
- `inner_mut()` invalidates cache (`self.frozen = Arc::new(OnceLock::new())`) then returns `Arc::make_mut(&mut self.inner)`
- Clone = two `Arc::clone` calls
- Hash = `frozen_bytes()` via `OnceLock::get_or_init`, cached across all clones sharing the same Arc
- Eq = `Arc::ptr_eq` fast path, then program_id check, then frozen bytes comparison

### Measurement

Used `tests/chrstate_perf_bench.rs` running all 21 corpus cases in release mode, with 5 focused runs on the critical case for stable median timing.

## Results

### Full corpus comparison

| Case | Steps | Before (µs/step) | After (µs/step) | Change |
|------|------:|------------------:|-----------------:|-------:|
| identity_atom | 12 | 10.2 | 9.2 | -10% |
| sequence_chain_len12 | 111 | 3.0 | 2.5 | -17% |
| sequence_chain_len64 | 579 | 8.5 | 7.8 | -8% |
| disjunction_wide_16 | 117 | 1.5 | 1.3 | -13% |
| disjunction_wide_64_first16 | 67 | 1.5 | 1.3 | -13% |
| disjunction_wide_256_first64 | 259 | 1.4 | 1.2 | -14% |
| conjunction_selective | 32 | 2.4 | 2.1 | -13% |
| conjunction_cross_16x16 | 154 | 2.1 | 2.3 | +10% |
| deep_term_depth_32 | 12 | 2.6 | 2.6 | 0% |
| deep_term_depth_128 | 12 | 4.1 | 5.7 | +39% |
| recursive_add_forward_n8 | 160 | 4.2 | 3.8 | -10% |
| recursive_add_backward_n8 | 268 | 3.9 | 3.4 | -13% |
| recursive_add_forward_n24 | 448 | 8.0 | 8.3 | +4% |
| **recursive_add_backward_n24** | **1348** | **10.0** | **6.2** | **-38%** |
| recursive_even_backward_first10 | 203 | 5.3 | 5.2 | -2% |
| **recursive_even_backward_first64** | **4793** | **24.2** | **22.9** | **-5%** |
| constraints_nonzero_success | 12 | 3.2 | 3.2 | 0% |
| constraints_nonzero_deep_success | 12 | 2.7 | 2.8 | +4% |
| constraints_range_between | 12 | 2.2 | 2.2 | 0% |
| treecalc_first_answer | 18 | 3.5 | 2.3 | -34% |
| treecalc_first16 | 331 | 6.0 | 5.2 | -13% |

### Focused measurement: recursive_even_backward_first64

| Metric | Before | After | Change |
|--------|-------:|------:|-------:|
| Median µs/step | 25.2 | 19.9 | **-21%** |
| Median total ms | 120.90 | 95.22 | **-21%** |
| Min µs/step | 24.9 | 19.6 | -21% |
| Max µs/step | 27.1 | 20.3 | -25% |
| Variance (max-min) | 2.2 µs | 0.7 µs | **-68%** (tighter) |

## Analysis

### What improved

1. **Clone cost eliminated for shared states.** When multiple FixWork steps share the same ChrState (common in the tabling call-chain), clone is now O(1) instead of deep-copying ChrStore + TokenStore + VecDeque.

2. **Hash caching works.** When the same ChrState is hashed multiple times (DashMap lookups), the frozen bytes are computed once and reused via `OnceLock`.

3. **Eq pointer fast-path.** When comparing a ChrState against itself (e.g., table lookup hits for same state), `Arc::ptr_eq` returns immediately.

4. **Variance reduced.** The optimized version has much tighter timing (0.7µs spread vs 2.2µs) because it avoids allocation-heavy operations that are sensitive to allocator state.

### Why only ~21% instead of ~2x

The original profiling attributed ~45% of execution to ChrState clone/hash/allocation. The optimization addresses these, but the actual speedup is smaller because:

1. **Arc::make_mut deep-copies on divergence.** Every `inner_mut()` call when refcount > 1 still deep-clones. In the ConstraintOps methods (`combine`, `normalize`, `apply_subst`, `remap_vars`), the pattern is `self.clone()` then immediately mutate — so Arc refcount is 2, and `Arc::make_mut` triggers a full deep clone. The clone cost is only eliminated when the clone is *not* subsequently mutated (which happens in the FixWork step chain but not in constraint operations).

2. **freeze_chr still allocates on first computation.** The cache helps on *repeat* hash/eq calls for the same state, but the first computation for each unique state still allocates Vec<AliveRec>, Vec<u32>, ByteWriter, etc. Since the even/odd workload uses NoTheory with empty ChrState, every state is "unique" (empty) but still pays the first-computation cost.

3. **The 23.3% allocation overhead is only partially addressed.** Arc reduces clone allocations but doesn't eliminate FixWork Box allocation, or the allocations within compose_nf itself.

### Remaining bottlenecks

Given that ~21% was reclaimed, roughly ~24% of the original overhead remains unaddressed:

- **FixWork::step Box allocation** (Target #3 from the original investigation): Every step allocates `Box::new(Work::Fix(self.clone()))`. Now the clone is cheaper, but the Box alloc itself remains.
- **freeze_chr first-call allocation for empty states**: A fast-path returning a static empty `Vec<u8>` for empty ChrState would eliminate this entirely for the NoTheory workload.
- **Compose/meet kernel overhead** (15.4% per original profiling): This is actual work and not addressable by ChrState optimization.

### Where the optimization helps most

The biggest wins are in workloads with high step counts and tabling:

- `recursive_add_backward_n24`: **-38%** (1348 steps, heavy tabling)
- `treecalc_first_answer`: **-34%** (18 steps but deep call chains)
- `recursive_even_backward_first64`: **-21%** (4793 steps, the critical workload)

Low-step-count cases show noise-level variation (±10%) as expected.

## Verdict

**Not worth keeping as-is.** The Arc wrapper adds indirection (`.inner()` at every external access site) and complexity for a benefit that comes almost entirely from hash/eq caching — not from O(1) clone.

The core problem: ConstraintOps methods (`combine`, `normalize`, `apply_subst`, `remap_vars`) all follow a clone-then-mutate pattern. With Arc, the clone is O(1) but the immediate `inner_mut()` call triggers `Arc::make_mut` deep-copy (refcount is 2), so these paths pay the *same* deep-copy cost as before, plus additional overhead for Arc atomics and OnceLock allocation. The O(1) clone benefit only materializes for clones that are never mutated (FixWork step chain passing state through), which is a minority of the clone traffic.

The ~21% improvement is real, but it's attributable to the **hash/eq caching** (frozen bytes computed once per unique state via OnceLock), not the Arc clone optimization. A simpler approach — caching frozen bytes directly on ChrState as an `Option<Vec<u8>>` field, invalidated on mutation — would capture most of the same win without Arc indirection.

### Recommended next steps (in order of expected impact)

1. ~~**Cache frozen bytes directly on ChrState**~~ — Investigated in [chrstate_cache_and_fastpath.md](chrstate_cache_and_fastpath.md). `OnceLock<Vec<u8>>` cache caused a 15-23% regression due to struct size increase and OnceLock overhead. Instances are hashed/compared once each, so caching adds cost without benefit.
2. ~~**Empty ChrState fast-path**~~ — Implemented in `freeze_chr`. Benchmarks showed neutral impact (existing code was already near-zero cost for empty state). See [chrstate_cache_and_fastpath.md](chrstate_cache_and_fastpath.md).
3. **Restructure ConstraintOps to avoid clone-then-mutate** — this is a prerequisite for Arc-wrapping to deliver its full potential. Only after this is done would Arc-wrapping make sense.
4. **FixWork Box allocation** — avoid per-step `Box::new(Work::Fix(self.clone()))` by reusing allocations.

The Arc approach should be revisited *after* #3, when the mutation patterns actually allow clones to remain shared.

## Artifacts

- Implementation: reverted (not merged)
- Benchmark: `tests/chrstate_perf_bench.rs`
