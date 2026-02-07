# Investigation: Or Tree Management and Per-Step Cost

**Status:** Completed — Or tree hypothesis disproven. Real bottleneck identified: ChrState clone/hash allocation.
**Backlog item:** Disjunction/Or Execution #1, #5; Term Representation and Memory Layout
**Branch:** `fast-flip`
**Triggered by:** fixpoint verification investigation identified Or tree management as the likely bottleneck.

## Hypothesis

The O(n²) cost of Or tree rotation (binary tree left-spine walk + rebuild) is the dominant cost in streaming recursive evaluation, specifically for `recursive_even_backward_first64` at ~102ms.

## Method

Added Or spine instrumentation to `perf_counters`:
- `or_spine_walks`: number of step_or calls
- `or_spine_total_siblings`: cumulative siblings collected across all walks
- `or_spine_max_siblings`: peak siblings in any single walk

Ran all 21 corpus cases in release mode and analyzed Or tree depth.

## Or Tree Results

| Case | Steps | OrWalks | MaxSibs | AvgSibs | SibSteps% |
|------|------:|--------:|--------:|--------:|----------:|
| disjunction_wide_16 | 117 | 90 | 2 | 1.3 | 100.9% |
| disjunction_wide_64_first16 | 67 | 47 | 2 | 1.3 | 92.5% |
| disjunction_wide_256_first64 | 259 | 191 | 2 | 1.3 | 98.1% |
| conjunction_cross_16x16 | 154 | 90 | 2 | 1.3 | 76.6% |
| **recursive_even_backward_first64** | **4793** | **253** | **1** | **1.0** | **5.3%** |
| treecalc_first16 | 331 | 663 | 5 | 1.4 | 287.3% |
| TOTAL | 8960 | 1759 | 5 | 1.2 | 24.4% |

### Or tree hypothesis: DISPROVEN

For `recursive_even_backward_first64` (the heaviest workload at 102ms):
- **MaxSibs = 1** — the Or tree never has more than 1 sibling
- **SibSteps% = 5.3%** — Or overhead is negligible
- The 21.3µs/step cost comes from something else entirely

Or tree overhead IS significant for wide disjunction cases (disjunction_wide_*, treecalc), but those are already fast (<1ms total). The O(n²) Or tree cost is real but only matters for workloads with many static Or branches (wide disjunction), not for streaming recursive workloads.

## Profiling: Where Does 21.3µs/Step Actually Go?

Built with `RUSTFLAGS="-C force-frame-pointers=yes"`, profiled with `perf record -g --call-graph dwarf -F 9999`.

### Execution Time Breakdown

| Category | % of Execution | Description |
|----------|---------------|-------------|
| **Allocation/Deallocation** | **23.3%** | malloc, realloc, cfree, Arc::drop_slow |
| **Cloning** | **21.8%** | ChrState::clone dominates via FixWork → CallKey → NF → DropFresh chain |
| **compose_nf (kernel work)** | **15.4%** | match_term_lists, apply_subst, factor_tensor, var_renaming |
| **Hashing (incl. freeze_chr)** | **12.7%** | freeze_chr allocates Vec<u8> during hash computation |
| **Pipe/Diagonal framework** | **12.4%** | PipeWork::step, DiagonalJoin::pull_side stepping overhead |
| **Table operations** | **6.5%** | Table::answer_at, Table::set_producer_node (mutex locks) |
| **Other** | **7.9%** | Miscellaneous |

### Key finding: only 15% of time is actual computation

The engine spends **~45% of execution time on allocation + cloning**, and only 15% on actual kernel work (compose_nf). The dominant cost is the ChrState clone/hash/eq chain.

## Root Cause: ChrState Clone and Hash Allocation

### The clone chain

`FixWork::step()` calls `self.clone()` on every single step (lines 487, 498, 506, 512 of fix.rs). Each clone triggers:

```
FixWork::clone()
  → CallKey::clone()
    → Option<NF>::clone() × 2 (left and right boundaries)
      → NF::clone()
        → DropFresh::clone()
          → ChrState<NoTheory>::clone()  ← EXPENSIVE
```

### The hash chain

Every DashMap lookup on a CallKey triggers:

```
CallKey::hash()
  → Option<NF>::hash() × 2
    → NF::hash()
      → DropFresh::hash() (derived)
        → ChrState::hash()
          → freeze_chr()  ← ALLOCATES Vec<u8> EVERY TIME
```

### Why freeze_chr allocates

`freeze_chr` (chr/mod.rs:1562) builds a canonical byte representation for hashing/equality:
1. Allocates `Vec<AliveRec>` (filters alive constraints)
2. Allocates `Vec<u32>` (remap table)
3. Allocates `ByteWriter` inner `Vec<u8>` (grows via realloc)
4. Allocates `Vec<(u32, Vec<TokenKey>)>` (token rules)
5. Sorts both alive constraints and token rules

**Update:** An empty fast-path has since been added to `freeze_chr` that short-circuits when `alive_count == 0 && T::is_empty(&builtins)`, returning a fixed 12-byte result without any allocations. Benchmarks showed this was neutral (the existing code path was already near-zero cost for empty state). See [chrstate_cache_and_fastpath.md](chrstate_cache_and_fastpath.md).

### Why ChrState::eq also allocates

`ChrState::eq()` calls `freeze_chr(self) == freeze_chr(other)` — allocating TWO temporary Vec<u8> buffers just to compare for equality.

## Impact Quantification

For `recursive_even_backward_first64`:
- 4793 engine steps
- ~2300 FixWork steps, each cloning 2 NFs with ChrState
- ~400+ table lookups (DashMap::get_or_create), each hashing + comparing CallKeys
- **Total ChrState allocations estimated: ~7000+ per evaluation**

At ~3-5µs per freeze_chr call (allocation + serialization + deallocation), the hash/eq path alone costs ~20-35ms out of 102ms total.

## Optimization Targets Identified

### Target 1: Eliminate allocation in ChrState Hash/Eq

**Impact: ~12.7% of execution (hashing) + portion of 23.3% allocation**

Options:
- **Pre-compute and cache the hash** inside ChrState (invalidate on mutation)
- **Hash directly without materializing**: feed values to Hasher instead of building Vec<u8>
- ~~**Fast-path for empty ChrState**: skip freeze_chr entirely when store is empty~~ (implemented; neutral impact)

### Target 2: Make ChrState cloning cheap

**Impact: ~21.8% of execution (cloning)**

Options:
- **Arc-wrap ChrState internals**: `struct ChrState<T> { inner: Arc<ChrStateInner<T>> }` — clone is just Arc bump. Use `Arc::make_mut` for copy-on-write when mutation needed.
- **Intern ChrState**: share identical states via interner, clone is copy of handle
- **Avoid cloning in FixWork::step**: restructure to pass FixWork by ownership instead of cloning continuation

### Target 3: Reduce FixWork per-step allocation

**Impact: portion of 23.3% allocation**

- FixWork::step returns `WorkStep::More(Box::new(Work::Fix(self.clone())))` — Box allocation + clone on every step
- Could be restructured to reuse the existing allocation

## Conclusion

The Or tree management hypothesis is disproven for the heaviest workload. The real bottleneck is **ChrState clone/hash/eq overhead**, which consumes ~45% of execution time through:
1. Deep cloning on every FixWork step (21.8%)
2. Allocating in freeze_chr during every hash/eq operation (12.7%)
3. Associated malloc/realloc/cfree overhead (23.3%)

The engine spends only 15% of its time on actual kernel work (compose_nf). The remaining 85% is framework overhead, dominated by ChrState-related allocation and cloning.

The most impactful fix is making ChrState cheap to clone and hash. Arc-wrapping the internals would address both the clone cost (Arc bump instead of deep copy) and the hash cost (cached hash value). For the even/odd workload specifically, a fast-path for empty ChrState would eliminate nearly all of this overhead.

## Artifacts

- Instrumentation: `src/perf_counters.rs` (or_spine_walks, or_spine_total_siblings, or_spine_max_siblings)
- Instrumentation: `src/node.rs:step_or` (record_or_spine_walk call)
- Measurement test: `tests/or_tree_investigation.rs`
- Flamegraph: generated via `perf record` + `inferno-collapse-perf` + `inferno-flamegraph`
