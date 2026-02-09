# Investigation: Pre-flatten CHR head patterns for linear matching

## Summary

Pre-flattened CHR head argument patterns into contiguous `FlatMatchOp` arrays at program construction time, replacing the generic PatArena-based tree walk in the hot matching loop. ~7.0% improvement with complete statistical separation.

**Baseline:** 1473773us (median, all values: 1479661, 1456807, 1457986, 1516167, 1474595, 1481144, 1450866, 1472951, 1480399, 1452989)
**After:** 1369952us (median, all values: 1401559, 1383969, 1359853, 1369070, 1320280, 1386217, 1353312, 1370833, 1399699, 1346797)
**Improvement:** ~7.0% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001, complete separation)
**Regression:** None observed on recursive_even_backward_first64 (U=61/100, neutral)

## Problem

`match_head` called `match_pat_bind_locked` for each CHR head pattern match, which used a generic stack-based tree walk through `PatArena` indirection. This was 17.61% of total runtime per profiling data. Three forms of overhead compounded:

1. **PatArena indirection**: Each `pats.get(p)` is an indexed lookup into a `Vec<PatNode>`, requiring bounds checking and pointer chasing through enum variants with `SmallVec` children.
2. **Stack pair overhead**: The work stack held `(PatId, TermId)` pairs (16 bytes per entry), requiring both to be pushed/popped together.
3. **Dispatch overhead**: Each iteration dispatched on `PatNode` (RVar vs App), then for App, looked up children from a SmallVec and zipped them.

## Solution

Added a `FlatMatchOp` enum with three variants:
- `PushRoot` — push the next root term from the head argument list
- `CheckApp(FuncId, u8)` — pop a term, verify it's `App(f, n_children)`, push children in reverse
- `BindVar(RVar)` — pop a term, bind it to an RVar

At program construction time (`ChrProgramBuilder::build`), each head's argument patterns are flattened into a contiguous `Box<[FlatMatchOp]>` via pre-order traversal. At match time, `match_flat_ops` executes the linear op sequence with a `SmallVec<[TermId; 8]>` stack (4 bytes per entry).

### Key design decisions

1. **Pre-order traversal with reverse child push**: Children are pushed in reverse order so they're popped in forward order, maintaining correct left-to-right matching semantics.
2. **PushRoot separators**: Instead of separate per-arg matching calls, all args are fused into one op sequence with PushRoot ops marking boundaries. This eliminates per-arg function call overhead.
3. **Box<[FlatMatchOp]> storage**: Stored as `head_flat_ops: Box<[Box<[FlatMatchOp]>]>` on `Rule`, indexed by head position. The Box<[]> (boxed slice) avoids Vec capacity overhead and provides contiguous cache-friendly layout.
4. **Dead code removal**: After the flat path proved successful, removed the now-unused `match_pat_bind` and `match_pat_bind_locked` functions, and the unused `pats` parameter from `match_head`.

## Files changed

- `src/chr/mod.rs` — Added `FlatMatchOp` enum, `flatten_head_pat`/`flatten_pat_preorder` functions, `match_flat_ops` function, `head_flat_ops` field on `Rule`. Replaced `match_head` calls to use flat path. Removed dead `match_pat_bind`/`match_pat_bind_locked`.

## Why 7% instead of 17%

The profiling showed `match_head` at 17.61% of total runtime. Capturing ~7% of total runtime from an 18% hotspot means we eliminated roughly 40% of the overhead in that specific function. The remaining 60% is:

1. **TermStore lock acquisition**: `match_head` still calls `terms.read_lock()` once per match attempt. This RwLock read-lock overhead is unchanged.
2. **HashMap lookups in TermReadGuard::get**: Each `CheckApp` op still does a hashmap lookup via `guard.get(t)` to access the term's functor and children. This is the actual term data access cost.
3. **RVar binding**: `env.bind()` does generation-checked binding with potential equality checking for already-bound vars.

The flat matching eliminated the structural traversal overhead (PatArena lookups, large stack entries, PatNode dispatch) but the data access costs remain.

## Remaining opportunities

- The `TermReadGuard::get` hashmap lookup in `match_flat_ops` is now the dominant cost per match step. If terms could be accessed via direct indexing (e.g., arena-based storage) instead of HashMap, the per-step cost would drop further.
- The `CheckApp` variant stores arity as `u8`, which handles up to 255 children. For the common case of 1-2 children, a specialized `CheckApp1`/`CheckApp2` variant could avoid the length comparison.
- The `read_lock()` acquisition per match attempt could potentially be hoisted to a broader scope if the search loop could guarantee no concurrent writes.
