# Investigation: chrstate_cow

**Status:** KEEP
**Round:** 12
**Date:** 2025-02-09

## Hypothesis

`ChrState::clone` is 3.7% of runtime and `DropFresh::clone` (which contains the ChrState constraint) is 1.3%. ChrState contains `Option<Box<ChrStateData<T>>>` where ChrStateData has ChrStore (with HashMaps), TokenStore (with Vec<HashSet>), VecDeque<Cid>, etc. Every clone deep-copies all of this. Since most ChrState clones are never mutated (they flow through NF cloning in DiagonalJoin), replacing `Box` with `Arc` makes clone O(1) with copy-on-write on mutation via `Arc::make_mut()`.

## Changes Made

- `src/chr/mod.rs`: Changed `data: Option<Box<ChrStateData<T>>>` to `data: Option<Arc<ChrStateData<T>>>`. Updated Clone impl to use O(1) `Arc::clone`. Updated `data_mut()` to use `Arc::make_mut()` for copy-on-write semantics. All 12 mutation sites updated.

## Measurement

### Primary: recursive_even_backward_first64
| Round | Baseline (us) | Optimized (us) |
|-------|--------------|----------------|
| 1 | 5852.4 | 5004.8 |
| 2 | 5494.2 | 4969.8 |
| 3 | 5466.2 | 4826.0 |
| 4 | 5528.4 | 4801.3 |
| 5 | 5506.8 | 4815.8 |
| 6 | 5530.3 | 5153.5 |
| 7 | 5471.5 | 5083.4 |
| 8 | 5741.5 | 4771.4 |
| 9 | 5627.2 | 4912.4 |
| 10 | 5460.7 | 4975.3 |

**U = 100/100 — KEEP (~10.4% improvement)**

### Secondary: treecalc_first16
| Round | Baseline (us) | Optimized (us) |
|-------|--------------|----------------|
| 1 | 708.6 | 627.6 |
| 2 | 710.6 | 629.4 |
| 3 | 658.5 | 647.1 |
| 4 | 701.1 | 622.7 |
| 5 | 679.2 | 621.9 |
| 6 | 1030.7 | 598.7 |
| 7 | 688.0 | 628.2 |
| 8 | 1024.1 | 641.0 |
| 9 | 1074.4 | 633.4 |
| 10 | 710.3 | 935.3 |

**U = 93/100 — PASS (~11.4% improvement on secondary, no regression)**

## Analysis

The optimization exceeded the hypothesized ~5% target, achieving ~10% primary and ~11% secondary improvement. This suggests ChrState clone costs were underestimated in profiling — cloned NFs containing ChrState flow through DiagonalJoin's pending/seen_l/seen_r sets, causing cascading deep copies of ChrStore (HashMaps), TokenStore (Vec<HashSet>), VecDeque<Cid>, etc.

U=100/100 on primary means every optimized sample was faster than every baseline sample — zero overlap between distributions. The change was minimal (19 insertions, 17 deletions) and purely mechanical: `Box` → `Arc` + `Arc::make_mut()` at mutation points.

Both workloads benefit because ChrState cloning is on the hot path for all workloads using CHR constraints. The copy-on-write semantics mean clones are free until mutation, and most NF clones in the join pipeline are never mutated.

## Remaining Opportunities

- **Lazy ChrState initialization:** Many NFs carry empty ChrState (data=None). Could avoid even the Arc overhead for these with a static sentinel.
- **ChrStore structural sharing:** Even with Arc COW, mutation still deep-copies the entire ChrStateData. A persistent/functional ChrStore could share structure across mutations.
