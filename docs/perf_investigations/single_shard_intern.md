# Investigation: Eliminate double hashing in TermStore intern

## Summary

Attempted to eliminate double FxHash computation in `TermStore::intern_unlocked` by pre-computing the hash once and using hashbrown's `raw_entry` API for both shard selection and HashMap bucket lookup.

**Baseline:** 833544us (median, all values: 824822, 821923, 823200, 842266, 823177, 824551, 868125, 863285, 850625, 875605)
**After:** 846104us (median, all values: 828419, 826942, 826072, 826060, 837880, 854328, 869239, 870062, 866760, 863030)
**Improvement:** -1.51% (slight regression)
**Mann-Whitney U:** 35/100 (not significant)
**Regression:** N/A (primary failed to show improvement)

## Problem

`TermStore::intern_unlocked` uses 16 shards with FxHash. When interning a term, the hash is computed twice: once by `shard_index()` to select the shard (FxHash of the Term), and once internally by the shard's `HashMap::get`/`HashMap::insert`. Profiling showed `HashMap::get_inner` at 7.43% and `intern_unlocked` at 1.87% of total runtime, suggesting interning overhead was significant.

## Solution

Replaced the two-step lookup with hashbrown's `raw_entry` API:

1. Renamed `shard_index()` to `hash_term()` returning the full `u64` hash
2. Used `raw_entry().from_hash(hash, |k| k == &term)` for lookups, passing the pre-computed hash
3. Used `raw_entry_mut().from_hash(hash, |k| k == &term).insert_hashed_nocheck(hash, term, id)` for inserts
4. Also used `AtomicU32::get_mut()` directly in `intern_unlocked` to avoid atomic overhead on the counter

## Files changed

- `src/term.rs` — Replaced `HashMap::get`/`insert` with `raw_entry()`/`raw_entry_mut()` using pre-computed FxHash. (~40 lines changed)

## Why -1.51% (regression) instead of 2-4% improvement

1. **FxHash is extremely fast.** FxHash is a simple multiply-xor-shift cascade with no state setup, no finalization, and no SIMD. For typical `Term` values (enum with FuncId + SmallVec of u32s), the total hash computation is ~5-15ns. Computing it twice costs ~10-30ns total — eliminating one saves ~5-15ns per intern call.

2. **raw_entry adds overhead.** The `raw_entry_mut().from_hash(hash, |k| k == &term)` path requires a closure for equality checking and goes through an additional layer of dispatch (Occupied/Vacant enum match) compared to the direct `HashMap::get` which is fully inlined by the compiler. This indirection overhead appears to cancel out or exceed the double-hash savings.

3. **The hypothesis was wrong.** The 9.3% profiling cost attributed to interning (7.43% HashMap::get_inner + 1.87% intern_unlocked) is dominated by hash table probing and Term equality comparisons (comparing FuncIds and SmallVecs of TermIds), not by hash computation. The hash computation is a tiny fraction of the per-lookup cost.

4. **Compiler optimization loss.** HashMap's standard `get`/`insert` path is extremely well-optimized by the compiler with full inlining. The raw_entry path prevents some of these optimizations due to the closure boundary and generic dispatch.

## Remaining opportunities

- If term interning is truly a bottleneck, more impactful approaches would be:
  - Reducing the number of intern calls (e.g., memoization at a higher level, avoiding creation of intermediate terms) — this is partially addressed by the `skip_split_subst` optimization which eliminates intermediate term creation during chain resolution
  - Encoding more term types inline in TermId (avoiding the hash table entirely for common patterns) — partially addressed by `inline_var_termid`
  - A more cache-friendly data structure (open addressing with linear probing, or a flat arena with hash index)
- The equality comparison cost could potentially be reduced by hashing term structure more aggressively and using hash equality as a prefilter, but FxHash collisions are already rare
