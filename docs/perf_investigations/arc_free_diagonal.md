# Investigation: arc_free_diagonal

**Status:** DISCARD
**Round:** 11
**Date:** 2025-02-09

## Hypothesis

DiagonalJoin wraps every NF in `Arc<NF<C>>` for storage in `seen_l`/`seen_r` Vecs and `seen_l_set`/`seen_r_set`/`pending_set` FxHashSets. This incurs:
- `Arc::new` allocation for every NF entering the join
- `Arc::clone` for every HashSet operation
- `Arc::try_unwrap` + potential clone on every `pop_pending`
- Pointer indirection through Arc on every `seen_l_at`/`seen_r_at` access
- Full NF comparison in HashSet operations

Replacing Arc with direct NF storage and u64 cached_hash for dedup should eliminate this overhead.

## Changes Made

- `src/work/diagonal.rs`: Replaced `Vec<Arc<NF<C>>>` with `Vec<NF<C>>`, `FxHashSet<Arc<NF<C>>>` with `FxHashSet<u64>`, `VecDeque<Arc<NF<C>>>` with `VecDeque<NF<C>>`
- `src/work/meet.rs`: Updated test helper return types

## Measurement

### Primary: recursive_even_backward_first64
| Round | Baseline (us) | Optimized (us) |
|-------|--------------|----------------|
| 1 | 6068.8 | 6138.2 |
| 2 | 6016.4 | 5786.7 |
| 3 | 8501.5 | 6666.4 |
| 4 | 5855.4 | 5721.9 |
| 5 | 8466.6 | 5621.0 |
| 6 | 6008.4 | 6249.6 |
| 7 | 6857.3 | 5690.3 |
| 8 | 7539.6 | 5828.5 |
| 9 | 6029.7 | 5824.5 |
| 10 | 6526.3 | 5783.4 |

**U = 84/100 — KEEP on primary (~4.6% improvement)**

### Secondary: treecalc_first16
| Round | Baseline (us) | Optimized (us) |
|-------|--------------|----------------|
| 1 | 1111.9 | 1344.3 |
| 2 | 912.1 | 1351.4 |
| 3 | 915.0 | 1250.3 |
| 4 | 917.7 | 910.3 |
| 5 | 908.3 | 1211.4 |
| 6 | 914.3 | 1365.6 |
| 7 | 906.6 | 913.8 |
| 8 | 907.9 | 1345.4 |
| 9 | 1402.9 | 915.1 |
| 10 | 914.5 | 1332.2 |

**U = 23/100 — FAIL (significant regression on secondary)**

Step counts identical (269 steps, 78 compose, 5 meet) — correctness preserved, regression is pure overhead.

## Analysis

The optimization helps the primary workload (~4.6%) where NFs are small (C=() or thin ChrState) and compose-heavy (378 compose calls). But it *hurts* the secondary workload (~45% regression) where NFs flow through both compose and meet work.

**Root cause of regression:** Moving NF<ChrState> structs inline instead of behind Arc pointers increases memcpy costs for VecDeque push/pop operations and Vec growth. Arc provides pointer stability — the NF stays in one place and only the 8-byte Arc pointer moves. With direct storage, NF structs (~96+ bytes) are copied on every VecDeque operation. The `take_self()` path in the non-in-place `step()` method moves entire DiagonalJoin contents including all inline NFs.

## Remaining Opportunities

- **Hybrid approach:** Keep Arc for seen_l/seen_r (which grow monotonically and benefit from pointer stability) but use u64 hash for the dedup sets. This gets the HashSet speedup without the Vec/VecDeque regression.
- **Shrink NF:** If NF<ChrState> were smaller, inline storage would be viable. The ChrState constraint carries significant per-NF overhead.
- **Pool-based Arc:** Use a custom allocator for Arc<NF> to reduce allocation overhead without losing pointer stability.
