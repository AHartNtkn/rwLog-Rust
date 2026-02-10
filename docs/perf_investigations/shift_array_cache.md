# Investigation: Direct-mapped array cache for shift_term

## Summary

Attempted to replace the HashMap in ShiftCache with a fixed-size direct-mapped array for faster cache lookups.

**Baseline:** 301202us (median, all values: 302770, 300507, 300270, 299424, 301896, 306571, 299927, 303099, 300407, 302081)
**After:** 403391us (median, all values: 409552, 403010, 408754, 403701, 398971, 402841, 411204, 406955, 402847, 403080)
**Improvement:** -33.9% (catastrophic regression)
**Mann-Whitney U:** 0/100 (complete separation, wrong direction)
**Regression:** N/A (primary failed)

## Problem

shift_term is 4.33% of runtime (10.41% inclusive), using a thread-local HashMap<u64, TermId> cache. HashMap operations (hash computation, bucket probing) have per-lookup overhead. A direct-mapped array cache indexed by `packed_key % SIZE` should theoretically be faster: just one array index + key compare.

## Solution

Replaced `HashMap<u64, TermId>` with `Vec<(u64, TermId)>` of fixed size (4096 entries). Lookup: `entries[packed_key as usize & (SIZE - 1)]`, compare stored key, return value on match. Store: overwrite the slot. Used sentinel key u64::MAX for empty slots. Also tried combining the two `SHIFT_CACHE.with()` calls into a single `borrow_mut()`.

## Files changed

- `src/matching.rs` — Replaced ShiftCache entries HashMap with fixed-size Vec, direct-mapped lookup/store

## Why -33.9% instead of 2-5% improvement

1. **Hashbrown's HashMap uses SIMD-accelerated probing.** SSE2 control bytes allow parallel comparison of 16 slots simultaneously, achieving effective O(1) lookups in 1-2 cache line reads for well-distributed keys. A direct-mapped array cannot compete with this.

2. **Poor bit distribution in packed keys.** The key `(TermId.raw() << 32 | offset)` concentrates useful entropy in the high bits (TermId) while the low bits (offset) have low cardinality. Modulo indexing (`key & (SIZE-1)`) uses only the low bits, causing massive collisions as many different TermIds with the same offset map to the same slot.

3. **Collisions cause uncached fallback.** Each collision evicts the previous entry, forcing the evicted term to re-run `shift_term_uncached` (full tree walk + term interning) on next access. With high collision rates, the effective hit rate dropped dramatically.

4. **Cache size doesn't help.** Both 4096 entries (64KB) and 256 entries (4KB) showed the same ~33% regression, confirming the collision problem is structural (bad key distribution), not capacity-related.

5. **Array fill for invalidation pollutes cache lines.** Writing sentinel values to 4096 entries (64KB) on generation change pollutes L1/L2 cache, though this only runs once per engine run.

## Remaining opportunities

- A better hash function that mixes high bits into low bits before indexing (e.g., Fibonacci hashing: `key.wrapping_mul(0x9E3779B97F4A7C15) >> (64 - log2(SIZE))`) might fix the collision problem. But this adds hash computation overhead that may negate savings.
- Hashbrown's HashMap is already near-optimal for this use case. The 4.33% self-time of shift_term likely includes the uncached tree walk for cache misses, not just HashMap overhead.
- The shift_term cache design space appears exhausted unless a fundamentally different approach is taken (e.g., caching at a higher level).
