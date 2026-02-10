# Box PipeWork Inside Work Enum

## Change

Single structural change: `Work::Pipe(PipeWork<C>)` → `Work::Pipe(Box<PipeWork<C>>)`.

PipeWork (624B) was the largest variant in the `Work<C>` enum, forcing every `Box<Work>` to allocate 624 bytes regardless of which variant it held. In the critical `recursive_even_backward_first64` workload, ~216K FixWork steps each created a `Box<Work>` that wasted 584 bytes per allocation (FixWork is only 40 bytes — 94% waste).

Boxing PipeWork internally shrinks `Work<C>` from 624 to 280 bytes (now sized by ComposeWork at 280B). This is free for PipeWork itself — it was already behind a `Box<Work<C>>`, so it was already heap-allocated. The savings come from every *other* variant now allocating 280 bytes instead of 624 bytes.

## Measurements

### Size

| Type | Before | After | Change |
|---|---|---|---|
| `Work<C>` | 624 B | 280 B | -55% |
| `Box<Work<C>>` heap | 624 B | 280 B | -55% |

### Allocation profile (recursive_even_backward_first64)

| Metric | Before | After | Change |
|---|---|---|---|
| 513-1024 B bucket | 440,361 allocs / 275 MB | 1,955 allocs / 1.6 MB | -99.6% |
| 257-512 B bucket | 479 allocs / 238 KB | 439,394 allocs / 123 MB | absorbed from above |
| Total alloc bytes | 390 MB | 239 MB | -39% |
| Avg alloc size | 403 B | 247 B | -39% |

### Wall time

| Benchmark | Before | After | Change |
|---|---|---|---|
| recursive_even_backward_first10 | 785 µs | 706 µs | **-11.2%** |
| recursive_even_backward_first64 | 65.9 ms | 58.7 ms | **-11.0%** |

## Why 11% instead of the predicted 3-5%

The prediction accounted for reduced allocation traffic but underestimated the cache pressure effect. With 440K allocations shrinking by 344 bytes each, the working set shrinks substantially. Smaller allocations mean more of them fit in cache lines, reducing TLB misses and cache evictions during the tight alloc-step-free loops.

## Files changed

- `src/work/mod.rs` — enum definition + 2 construction sites
- `src/work/pipe.rs` — 15 construction sites
- `src/work/fix.rs` — 1 construction site
- `src/work/tests.rs` — 2 construction sites + 6 unboxing sites
- `src/bin/size_report.rs` — removed stale hypothetical section
- `docs/perf_investigations/allocation_overhead_analysis.md` — updated with results

## Risk

None. The compiler catches any missed site (type mismatch). All tests pass. No semantic changes.
