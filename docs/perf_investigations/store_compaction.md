# Investigation: Compact ChrStore after solve_to_fixpoint to reduce clone and iteration costs

## Summary

Investigated compacting the ChrStore (removing dead CInstance entries) after solve_to_fixpoint in normalize_owned. Early discard based on instrumentation: 82% of normalize_owned calls operate on completely empty stores, and the remaining 18% have at most 1 dead entry.

**Baseline:** N/A (early discard)
**After:** N/A
**Improvement:** N/A
**Mann-Whitney U:** N/A
**Regression:** N/A

## Problem

The hypothesis was that after `match_before_store` (Round 33), the ChrStore accumulates many dead CInstance entries alongside a few alive ones. When `compose_nf` succeeds (2787 times), `ChrState::apply_subst` clones the entire ChrStateData including the bloated store. `apply_subst_to_data` iterates ALL instances checking `inst.alive`, including dead ones. Compacting the store after solve_to_fixpoint would reduce clone and iteration costs.

## Solution Attempted

Before implementing compaction, added instrumentation to normalize_owned to measure the dead/alive ratio:

```rust
eprintln!("COMPACT_STATS: alive={} dead={} total={}",
    sd.store.alive_count, sd.store.dead_count, sd.store.inst.len());
```

## Why it was discarded

The instrumentation revealed the hypothesis was completely wrong:

1. **82% of normalize_owned calls (2467/3011) operate on completely empty stores** (alive=0, dead=0, total=0). There is nothing to clone, iterate, or compact.

2. **For the remaining 18% of calls, the dead count is always exactly 1.** The total store size ranges from 2 to ~19 entries. Compacting would save removing 1 element from vectors of size 2-19 — negligible.

3. **The secondary benchmark has 100% empty stores.** Zero compaction opportunity.

4. **ChrStateData::clone at 1.95% is not from store bloat.** The cost comes from aggregate clone frequency (2787 composes × clone), not per-instance size. The store portion of each clone is tiny.

5. **CId-as-index invariant makes compaction expensive.** CIds are used as direct indices into `inst` throughout the codebase, and TokenStore contains CIds in HashSets. Any compaction would require a full CId remapping pass, which for stores with just 1 dead entry exceeds the savings.

## Key insight

The `match_before_store` optimization (Round 33) has already eliminated the dead-entry accumulation pattern. Constraints that would have been stored and then killed are now never stored in the first place — they're consumed inline during body execution. Only unmatched constraints enter the store, and they remain alive.

## Files changed

None (instrumentation was added and removed).

## Remaining opportunities

- The 1.95% ChrStateData::clone cost is from frequency, not size. Reducing clone frequency (e.g., lazy cloning, COW for constraint state) would be more effective than reducing per-clone cost.
- The 15.77% apply_subst from ChrState::apply_subst operates on the few alive constraints' args. Reducing the number of alive constraints or making their args ground would eliminate this cost.
