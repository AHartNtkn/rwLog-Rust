# Investigation: mimalloc Global Allocator

## Summary

Replaced the default system allocator (glibc malloc) with mimalloc as the global allocator across all binaries. ~1.3% improvement on `recursive_even_backward_first64`, ~21.5% improvement on `treecalc_first16`.

**Primary baseline:** 20.52ms (median)
**Primary after:** 20.25ms (median)
**Primary improvement:** ~1.3%
**Mann-Whitney U (primary):** 100/100 (p < 0.01)

**Secondary baseline:** 1.16ms (median)
**Secondary after:** 0.91ms (median)
**Secondary improvement:** ~21.5%
**Mann-Whitney U (secondary):** 100/100 (p < 0.01)

## Problem

From profiling of `recursive_even_backward_first64`:
- `_int_malloc` = 1.70% of total time (direct)
- Additional allocation overhead hidden in clone, Vec resize, Box operations

glibc's malloc is general-purpose but not optimized for the allocation patterns typical of rwlog (many small, short-lived allocations from NF cloning, Work boxing, Vec operations).

## Solution

Added `mimalloc = "0.1"` dependency and set `#[global_allocator]` in each binary crate:

```rust
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
```

The allocator is set per-binary rather than in `lib.rs` because two profiling binaries (`alloc_profile`, `perf_corpus_alloc`) define their own custom counting allocators as global allocators. These were updated to wrap mimalloc instead of `std::alloc::System`.

## Files changed

- `Cargo.toml` — Added `mimalloc = "0.1"` dependency
- `Cargo.lock` — Lockfile update
- 11 binary crates — Added `#[global_allocator]` using mimalloc
- 2 profiling binaries — Updated counting allocator to wrap mimalloc

## Why 21.5% on secondary but only 1.3% on primary

The `treecalc_first16` workload is much shorter (~1ms vs ~20ms) and more allocation-intensive relative to its total runtime. mimalloc's faster small-allocation path and reduced fragmentation have a proportionally larger effect. The primary workload spends more time in computation (compose, match, step) relative to allocation.

## Notes

mimalloc adds ~200KB to the binary size (the C library is statically linked). It has no unsafe Rust code beyond the FFI boundary. Thread-safety is guaranteed by mimalloc's internal design (thread-local heaps with delayed free).
