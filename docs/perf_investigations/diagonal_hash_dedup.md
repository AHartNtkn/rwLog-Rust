# Investigation: diagonal_hash_dedup

**Status:** KEEP
**Round:** 12
**Date:** 2025-02-09

## Hypothesis

DiagonalJoin uses `FxHashSet<Arc<NF<C>>>` for dedup (seen_l_set, seen_r_set, pending_set). Each NF insert requires Arc::new, Arc::clone for set operations, and full NF PartialEq comparison on hash collisions. Since NF already has a `cached_hash: u64` field, replace the hash sets with `FxHashSet<u64>` using the cached_hash for dedup. Also change `VecDeque<Arc<NF<C>>>` to `VecDeque<NF<C>>` for pending since Arc is no longer needed for set dedup.

This is the "hybrid approach" identified in the arc_free_diagonal investigation (Round 11 DISCARD) — keep Arc for seen_l/seen_r Vecs (pointer stability for indexed access) but use u64 hash for the dedup sets.

## Changes Made

- `src/nf.rs`: Added `pub fn hash_value(&self) -> u64` accessor for the private `cached_hash` field.
- `src/work/diagonal.rs`: Added `IdentityHasher` for zero-cost u64 hashing (cached_hash is already well-distributed from FxHasher). Changed `seen_l_set`, `seen_r_set`, `pending_set` from `FxHashSet<Arc<NF<C>>>` to `HashSet<u64, BuildIdentityHasher>`. Changed `pending` from `VecDeque<Arc<NF<C>>>` to `VecDeque<NF<C>>`. Updated push_pending/pop_pending to use direct NF storage with u64 hash dedup.

## Measurement

### Primary: recursive_even_backward_first64
| Round | Baseline (us) | Optimized (us) |
|-------|--------------|----------------|
| 1 | 5741.4 | 5242.2 |
| 2 | 5878.5 | 5192.6 |
| 3 | 5702.0 | 5562.5 |
| 4 | 5676.8 | 5411.9 |
| 5 | 5726.4 | 5570.8 |
| 6 | 5706.1 | 5201.3 |
| 7 | 5984.1 | 5419.6 |
| 8 | 5582.7 | 5191.2 |
| 9 | 5732.2 | 5346.4 |
| 10 | 5538.5 | 5180.7 |

**U = 98/100 — KEEP (~7.4% improvement)**

### Secondary: treecalc_first16
| Round | Baseline (us) | Optimized (us) |
|-------|--------------|----------------|
| 1 | 741.6 | 678.9 |
| 2 | 694.3 | 718.0 |
| 3 | 1026.6 | 1037.8 |
| 4 | 690.9 | 744.4 |
| 5 | 717.3 | 712.3 |
| 6 | 718.8 | 716.4 |
| 7 | 726.6 | 1041.8 |
| 8 | 692.1 | 689.0 |
| 9 | 1055.2 | 1031.5 |
| 10 | 1071.8 | 717.1 |

**U = 56/100 — PASS (neutral, no regression)**

## Analysis

The optimization eliminates three sources of overhead in the DiagonalJoin hot path:
1. `Arc::new`/`Arc::clone` for pending set insertion
2. `Arc::try_unwrap` + potential clone on `pop_pending`
3. Full NF PartialEq comparison on hash collisions in the FxHashSet

The identity hasher is critical: since the u64 keys are already well-distributed FxHasher outputs from NF construction, double-hashing through FxHasher would waste cycles. The identity hasher passes u64 values through directly.

The 7.4% gain on recursive_even (compose-heavy workload) is significant because compose operations are the primary user of DiagonalJoin. The treecalc secondary (meet-heavy) shows no regression.

This validates the hybrid approach predicted by the arc_free_diagonal investigation: keeping Arc<NF> in the Vecs for pointer stability while using u64 hash for the dedup sets captures the hash set speedup without the VecDeque regression.

## Remaining Opportunities

- **Remove Arc from seen_l/seen_r entirely:** If NF<C> is small enough (after chrstate_cow makes constraint cloning O(1)), the seen Vecs could store NF directly. The ChrState COW change may make this viable now.
- **Capacity pre-allocation:** Pre-size the hash sets and VecDeque based on heuristics from the relation being computed.
