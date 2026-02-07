# Allocation Overhead Analysis

## Summary

Profiled allocation patterns in the `recursive_even_backward_first64` workload (the heaviest benchmark). Found that **968K heap allocations totaling 390MB** are dominated by two types: `Box<Work<C>>` (624 bytes, 440K allocs) and `Box<Node<C>>` (232 bytes, 443K allocs). Together these account for 91% of all allocations and 97% of all bytes.

The root cause is the `Work<C>` enum being 624 bytes (sized to its largest variant, `PipeWork<C>`), meaning every `Box<Work>` allocates 624 bytes even for tiny variants like `FixWork` (40 bytes). In the critical workload, ~216K FixWork steps each create a short-lived `Box<Work>` that wastes 584 bytes per allocation (94% waste).

**Estimated opportunity: 5-12% wall-time improvement** through a combination of enum layout optimization and allocation avoidance.

## Methodology

### Step 1: Allocation counting

Used the existing `perf_corpus_alloc` binary with a `CountingAlloc` global allocator to measure allocation counts and bytes across all corpus workloads.

**Key finding:** The recursive workload is a dramatic outlier.

| Workload | Alloc Calls | Alloc Bytes | Engine Steps | Allocs/Step |
|---|---|---|---|---|
| recursive_even_backward_first64 | 929K | 390 MB | 4,793 | 194 |
| recursive_add_backward_n24 | 69K | 26 MB | 1,348 | 51 |
| sequence_chain_len64 | 59K | 22 MB | 579 | 102 |
| treecalc_first16 | 20K | 4.6 MB | 331 | 59 |
| identity_atom | 112 | 41 KB | 12 | 9 |

### Step 2: Size-bucketed allocation profiling

Built a custom allocator that tracks allocation counts per size bucket.

| Size Range | Alloc Count | Alloc Bytes | % of Total Allocs |
|---|---|---|---|
| 0-16 B | 77,284 | 0.9 MB | 8.0% |
| 17-32 B | 1,770 | 54 KB | 0.2% |
| 33-64 B | 2,263 | 86 KB | 0.2% |
| 129-256 B | **443,716** | **103 MB** | **45.8%** |
| 513-1024 B | **440,361** | **275 MB** | **45.5%** |
| Others | 3,502 | 11 MB | 0.4% |
| **TOTAL** | **967,896** | **390 MB** | |

Two buckets dominate: 129-256 bytes (45.8%) and 513-1024 bytes (45.5%). Together: **91.3% of allocations, 96.9% of bytes.**

### Step 3: Data structure size mapping

Built a `size_report` binary to measure all key types with the concrete constraint type `ChrState<NoTheory>`:

**The size chain (why Work<C> is 624 bytes):**

```
ChrState<NoTheory>:    128 B
  Contains: ChrStore (56B), TokenStore (24B), VecDeque<u32> (32B),
            Arc<ChrProgram> (8B), next_cid (4B), failed (1B)

DropFresh<C>:          176 B
  Contains: ChrState (128B) + SmallVec<[(u32,u32);4]> (40B) + 2×u32 (8B)

NF<C>:                 224 B
  Contains: 2× SmallVec<[TermId;1]> (48B) + DropFresh<C> (176B)

PipeWork<C>:           624 B
  Contains: 2× Option<NF<C>> (448B) + Factors<C> (136B) + Env (8B)
            + Tables (16B) + CallMode (16B)

Work<C> enum:          624 B  (sized to PipeWork, the largest variant)
```

**Variant size mismatch in the Work enum:**

| Variant | Payload Size | Wasted in Box<Work> |
|---|---|---|
| PipeWork | 624 B | 0 B (defines the size) |
| ComposeWork | 280 B | 344 B (55%) |
| MeetWork | 248 B | 376 B (60%) |
| NF (Atom) | 224 B | 400 B (64%) |
| FixWork | 40 B | **584 B (94%)** |
| Done | 0 B | 624 B (100%) |

### Step 4: Allocation site analysis

All 440K `Box<Work>` allocations come from `WorkStep` construction:

**FixWork::step()** — 4 return sites, called ~216K times:
```rust
// Each creates Box::new(Work::Fix(self.clone())) = 624 bytes for 40 bytes of payload
WorkStep::Emit(nf, Box::new(Work::Fix(self.clone())))   // lines 491, 510
WorkStep::More(Box::new(Work::Fix(self.clone())))        // lines 502, 516
```

**PipeWork::step()** — ~15 return sites, creates Box<Work::Pipe>, Box<Work::Compose>, Box<Work::Done>

**Key pattern:** These allocations are extremely short-lived. Each FixWork step:
1. Allocates `Box<Work>` (624 bytes) containing the updated FixWork
2. Caller wraps it in `Node::Work(box)`
3. Next `step_node()` call consumes this Node, extracts the Work, calls `.step()` again
4. The old Box is dropped

This is a classic alloc-use-free cycle happening ~216K times.

### Step 5: perf profiling

Profile of the critical workload (with counting allocator, so percentages are shifted):

| Function | Self % | Category |
|---|---|---|
| PipeWork::step | 11.8% | Dispatch |
| FixWork::clone | 8.7% | Clone per step |
| drop_in_place\<Work\> | 4.5% | Destruction |
| step_table_producer | 4.4% | Producer stepping |
| step_node | 3.0% | Node dispatch |
| DiagonalJoin::pull_side | 3.0% | Join |
| sip::Hasher::write | 2.9% | Hashing |
| DiagonalJoin::new | 2.9% | Join creation |
| malloc | 1.5% | Allocation |
| cfree | 1.5% | Deallocation |
| drop_in_place\<Vec\<NF\>\> | 1.5% | NF vec destruction |

Combined allocation/deallocation overhead: malloc (1.5%) + cfree (1.5%) + drop_in_place\<Work\> (4.5%) + drop_in_place\<Vec\<NF\>\> (1.5%) = **~9%**.

## Root Causes

1. **Work<C> enum sized to largest variant**: PipeWork at 624B forces every Box<Work> to allocate 624B, even for FixWork (40B). This wastes 584B per FixWork boxing.

2. **ChrState inline in DropFresh**: ChrState at 128B appears inside DropFresh (176B), inside NF (224B), inside PipeWork (2× via Option<NF>). This is the fundamental reason NF and PipeWork are so large.

3. **Alloc-use-free cycles**: FixWork::step() allocates a Box<Work>, step_node consumes it, and the next step drops it — 216K cycles of allocate/use/free for identical-size objects.

## Potential Optimizations

### A: Box PipeWork internally in the Work enum

```rust
// Current: Work<C> = 624 bytes (sized to PipeWork)
enum Work<C> {
    Pipe(PipeWork<C>),     // 624 B
    Fix(FixWork<C>),       // 40 B
    ...
}

// Proposed: Work<C> = ~288 bytes (sized to ComposeWork)
enum Work<C> {
    Pipe(Box<PipeWork<C>>), // 8 B (pointer)
    Fix(FixWork<C>),        // 40 B
    ...
}
```

**Impact:** Every `Box<Work>` shrinks from 624B to ~288B. For the critical workload:
- 440K allocations × 336B savings = ~148MB less allocation traffic
- PipeWork allocations add one extra indirection (Box inside Box when used as Box<Work::Pipe>)
- Net savings depends on PipeWork:FixWork ratio but is substantial since FixWork dominates (216K steps)

**Estimated improvement:** 3-5% wall time (less memory pressure, better cache utilization, faster memcpy).

### B: Object pool / free list for Box<Work> and Box<Node>

Since allocations are extremely regular (same sizes, short-lived, alloc-use-free pattern), a typed free list would eliminate malloc/free calls entirely:

```rust
struct WorkPool<C> {
    free: Vec<Box<MaybeUninit<Work<C>>>>,
}
```

**Impact:** Eliminates ~880K malloc+free calls. At ~10-15ns per uncontended malloc/free, that's ~9-13ms saved directly, plus reduced cache pollution.

**Estimated improvement:** 3-6% wall time.

### C: Reduce ChrState inline size

ChrState at 128B is the root of the size inflation chain. If ChrState internals were Arc-wrapped:

```rust
// Current: 128 bytes inline
pub struct ChrState<T: Theory> {
    pub store: ChrStore,        // 56B
    pub builtins: T::Store,     // 0B for NoTheory
    pub tokens: TokenStore,     // 24B
    pub next_cid: u32,          // 4B
    pub agenda: VecDeque<Cid>,  // 32B
    pub program: Arc<...>,      // 8B
    failed: bool,               // 1B
}

// Proposed: ~16 bytes (Arc + bool)
pub struct ChrState<T: Theory> {
    inner: Arc<ChrStateInner<T>>,
    failed: bool,
}
```

**Impact:** NF shrinks from 224B to ~104B, PipeWork from 624B to ~344B, Work enum from 624B to ~352B.

**Risk:** Changes ChrState clone semantics from deep-copy to shared reference. Would need copy-on-write discipline for mutations. Significantly more invasive than options A or B.

### D: Return Work by value instead of Box

WorkStep could contain `Work<C>` inline instead of `Box<Work<C>>`:

```rust
// Current
enum WorkStep<C> {
    Emit(NF<C>, Box<Work<C>>),  // 232 bytes
    More(Box<Work<C>>),
    ...
}

// Proposed (only viable after option A reduces Work size)
enum WorkStep<C> {
    Emit(NF<C>, Work<C>),      // ~512 bytes (with option A: ~288+224)
    More(Work<C>),
    ...
}
```

**Impact:** Eliminates Box<Work> allocations entirely for Emit/More cases. WorkStep becomes large (~512B) but is always a stack temporary. Only viable after option A reduces Work size.

## Results

### Option A: Box PipeWork internally (IMPLEMENTED)

Changed `Work::Pipe(PipeWork<C>)` to `Work::Pipe(Box<PipeWork<C>>)` — a purely mechanical refactor.

**Size measurements:**

| Type | Before | After | Change |
|---|---|---|---|
| Work<C> | 624 B | 280 B | -55% |
| Box<Work<C>> heap | 624 B | 280 B | -55% |

**Allocation measurements (recursive_even_backward_first64):**

| Metric | Before | After | Change |
|---|---|---|---|
| 513-1024 B bucket | 440,361 allocs / 275 MB | 1,955 allocs / 1.6 MB | -99.6% / -99.4% |
| 257-512 B bucket | 479 allocs / 238 KB | 439,394 allocs / 123 MB | absorbed from 513-1024 |
| Total alloc bytes | 390 MB | 239 MB | -39% |
| Avg alloc size | 403 B | 247 B | -39% |

**Benchmark results:**

| Workload | Before | After | Change |
|---|---|---|---|
| recursive_even_backward_first10 | 785 µs | 706 µs | **-11.2%** |
| recursive_even_backward_first64 | 65.9 ms | 58.7 ms | **-11.0%** |

The improvement exceeded the predicted 3-5% — the 11% gain likely reflects reduced cache pressure from the smaller allocations in addition to raw allocation traffic savings.

### Remaining Experiment Order

1. **Option B** (object pool) — eliminates remaining malloc/free overhead
2. **Option C** (ChrState Arc-wrapping) — invasive but addresses root cause; defer unless B insufficient

## Files Involved

- `src/work/mod.rs` — Work enum definition
- `src/work/pipe.rs` — PipeWork struct, all Box<Work::Pipe> construction sites
- `src/work/fix.rs` — FixWork::step Box<Work::Fix> construction sites
- `src/node.rs` — Node enum, Box<Node> construction in step_node and or_node
- `src/nf.rs` — NF struct (size contributor)
- `src/drop_fresh.rs` — DropFresh struct (size contributor via ChrState)
- `src/chr/mod.rs` — ChrState struct (root size contributor)

## Benchmark History

| Workload | Pre-investigation | Post Option A |
|---|---|---|
| recursive_even_backward_first64 | ~75-78ms | ~58-59ms |
| recursive_even_backward_first10 | ~840µs | ~706µs |

## Files Created for This Investigation

- `src/bin/alloc_profile.rs` — Size-bucketed allocation profiler with perf mode
- `src/bin/size_report.rs` — Data structure size reporter
