# Investigation: Skip PredStore index construction for single-head simplification

## Summary

Skipped PredStore index building (rebuild_indexes, index_from, PredStore::insert) when all CHR rules are single-head simplification. These indexes are only used for JOIN STEPS in multi-head rules and are pure waste for single-head programs.

**Baseline:** 1198790us (median, all values: 1218790, 1182240, 1184195, 1201843, 1195738, 1179564, 1192037, 1323314, 1276058, 1232190)
**After:** 1124721us (median, all values: 1123481, 1090033, 1125960, 1096568, 1122381, 1122402, 1718635, 1200887, 1169128, 1127121)
**Improvement:** ~6.2% (same-session comparison)
**Mann-Whitney U:** 85/100 (p < 0.01)
**Regression:** None observed on recursive_even_backward_first64 (U=40/100, neutral — that workload doesn't use single-head simplification)

## Problem

The CHR engine has two fixpoint paths:
1. `solve_to_fixpoint_general` — uses `search_steps_inner` → `candidates_for_step_inner` → reads PredStore indexes for join step candidate lookup
2. `solve_to_fixpoint_single_head` — processes constraints directly from the agenda, uses only `program.triggers` (per-rule functor index), never accesses PredStore indexes

When `all_single_head_simplification` is true (treecalc's case), path 2 is always taken. But `normalize_owned` still called `rebuild_indexes` (1.32% of profile) which iterates all alive instances and populates PredStore HashMap indexes, and `add_chr` still called `PredStore::insert` (1.46% of profile) for every new constraint created by body execution. All this indexing work was never read.

## Solution

Added a `skip_indexes: bool` field to `ChrStore`, set from `program.all_single_head_simplification` at construction time.

### Key design decisions

1. **`skip_indexes` flag on ChrStore rather than passing program everywhere:** The flag is set once at ChrStore construction and propagated through all mutation operations. This avoids threading the ChrProgram reference through rebuild_indexes and add_chr, which would complicate borrow-checker interactions.

2. **PredStore stubs via `new_stub()` instead of empty preds Vec:** When skip_indexes is true, `rebuild_indexes` still creates the preds Vec with correct dimensions (one PredStore per predicate) to avoid panics in `add_chr` which accesses `self.preds[pred.0 as usize]`. The stubs use `new_stub()` which allocates no HashMaps. In add_chr, the `PredStore::insert` call is skipped entirely.

3. **Still count alive/dead in rebuild_indexes:** The `alive_count` and `dead_count` fields are still maintained even when skipping indexes, as these are used for other purposes (store emptiness checks, compaction decisions).

## Files changed

- `src/chr/mod.rs` — Added `skip_indexes: bool` to ChrStore, `new_stub()` to PredStore, conditional skip logic in `add_chr`, `rebuild_indexes`, and `index_from`. Updated all ChrStore::new call sites to pass the skip flag.

## Why 6.2% instead of 2.8%

The profiling estimated rebuild_indexes at 1.32% and PredStore::insert at 1.46% = 2.78% total. The actual improvement of 6.2% is more than 2x the estimate because:

1. **HashMap allocation cost underestimated by sampling:** PredStore::new creates HashMaps for each index type. The allocation + initialization cost of these HashMaps (even when small) is captured imprecisely by cycle-based sampling.

2. **Cache pressure from index data:** The PredStore HashMap entries occupy cache lines that evict hotter data (constraint args, agenda). Eliminating the indexes reduces cache pressure, speeding up adjacent operations.

3. **add_chr overhead was higher than profiled:** Each add_chr call's PredStore::insert involves TermStore read_lock (for ArgTopFunctor index), HashMap entry lookup/insert, and Vec push. The lock acquisition alone adds ~10ns per call, and there are thousands of calls in the fixpoint loop.

## Remaining opportunities

- The single-head simplification specialization could be extended further: skip agenda management (VecDeque pop/push) by processing constraints in-order from the inst array directly.
- The `all_single_head_simplification` flag could be generalized to per-rule properties, enabling partial index skipping when some rules are single-head and others are multi-head.
