# Investigation: dropfresh_arc_map

**Status:** KEEP
**Round:** 14
**Date:** 2025-02-09

## Hypothesis

`DropFresh::clone` is 2.9% of runtime. DropFresh contains `map: SmallVec<[(u32, u32); 4]>` which is 32 bytes inline. Even though the constraint (ChrState) is now Arc-wrapped (O(1) clone from Round 12), cloning the SmallVec map is still a 32-byte memcpy on every NF clone. Arc-wrapping the map makes clone an atomic refcount bump instead.

## Changes Made

- `src/drop_fresh.rs`: Changed `map: SmallVec<[(u32, u32); 4]>` to `map: Arc<SmallVec<[(u32, u32); 4]>>`. Updated all construction sites to wrap with `Arc::new()`. Fixed `validate()` iteration.
- `src/nf.rs`: Updated DropFresh construction in `factor()` and `factor_tensor()`.
- `src/kernel/dual.rs`: Updated `dual_drop_fresh()` and test construction sites.
- `src/kernel/compose.rs`: Updated test construction site.

## Measurement

### Primary: recursive_even_backward_first64
| Round | Baseline (us) | Optimized (us) |
|-------|--------------|----------------|
| 1 | 4830.2 | 5266.1 |
| 2 | 4571.4 | 4440.4 |
| 3 | 4762.9 | 4558.5 |
| 4 | 4765.5 | 4763.1 |
| 5 | 4610.4 | 4313.0 |
| 6 | 4768.8 | 4542.0 |
| 7 | 4774.2 | 4471.0 |
| 8 | 4697.7 | 4300.7 |
| 9 | 4669.3 | 5139.9 |
| 10 | 4812.4 | 4485.4 |

**U = 75/100 — KEEP (~5.3% improvement)**

### Secondary: treecalc_first16
**U = 60/100 — PASS (neutral, no regression)**

## Analysis

Arc-wrapping the map field replaces a 32-byte memcpy with an 8-byte atomic increment on every DropFresh clone. Since DropFresh values are created once during NF construction and cloned many times through DiagonalJoin's NF flow (pending, seen_l, seen_r sets), the clone-heavy pattern favors Arc's O(1) clone.

The `derive(Clone, PartialEq, Eq, Hash)` all work correctly through Arc's implementations — Arc<T> delegates PartialEq and Hash to T, and Clone performs an atomic refcount increment. Most map accesses are reads (iteration, len, binary_search) which work transparently through Arc's Deref.

## Remaining Opportunities

- **Arc the entire NF:** If NF itself were Arc-wrapped (like ChrState), all NF cloning would be O(1). But this requires COW semantics at every NF mutation point, which is more invasive.
- **Persistent data structures:** SmallVec could be replaced with a persistent/functional array that shares structure across modifications.
