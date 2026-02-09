# Investigation: Contiguous CInstance args buffer in ChrStore

## Summary

Replaced per-CInstance `SmallVec<[TermId; 4]>` with a contiguous `Vec<TermId>` args buffer in ChrStore. CInstance shrinks from ~48 bytes to ~16 bytes, reducing ChrStateData clone cost and improving cache locality.

**Baseline:** 1210792us (median, all values: 1205334, 1216250, 1229404, 1200830, 1222577, 1219890, 1193876, 1199966, 1194935, 1218917)
**After:** 1166631us (median, all values: 1176014, 1171539, 1165620, 1163320, 1168643, 1161119, 1161239, 1159675, 1167642, 1172553)
**Improvement:** ~3.65% (same-session comparison)
**Mann-Whitney U:** 100/100 (complete separation, p < 0.0001)
**Regression:** None observed on recursive_even_backward_first64 (U=66/100, neutral)

## Problem

CInstance contained `args: SmallVec<[TermId; 4]>`, which occupies ~32 bytes (union of inline [TermId; 4] and heap pointer+len+cap, plus discriminant). Total CInstance was ~48 bytes with alignment. For the treecalc_synth_flip workload using `no_c/1` (1-arg constraints), each SmallVec stored a single TermId (4 bytes) but occupied 32 bytes — 8x waste.

ChrStateData::clone was 3.61% of runtime, dominated by cloning Vec<CInstance> which deep-clones each CInstance including its SmallVec. Additionally, apply_subst_to_data iterated instances with scattered args (each SmallVec has its own inline buffer), hurting cache prefetch.

## Solution

1. Added `all_args: Vec<TermId>` to ChrStore — a single contiguous buffer for all constraint args.
2. Replaced `args: SmallVec<[TermId; 4]>` in CInstance with `arg_start: u32, arg_count: u16` — indices into the contiguous buffer.
3. Added `ChrStore::args(&self, inst: &CInstance) -> &[TermId]` and `args_mut` accessor methods.
4. Updated all code that accessed `inst.args` to use the new accessor or direct slicing (where borrow checker requires it).

### Key design decisions

1. **Contiguous buffer over per-instance SmallVec:** SmallVec<[TermId; 4]> was designed for general-case variable-arity constraints. But the dominant workload uses 1-arg constraints, making the inline storage wasteful. A contiguous buffer provides O(1) clone via Vec::clone (memcpy) instead of N individual SmallVec clones.

2. **`arg_count: u16` instead of u32:** Constraint arity is always small (1-4 in practice). u16 saves 2 bytes per CInstance, with a max arity of 65535 which is more than sufficient.

3. **Dead instance holes in all_args are tolerated:** When constraints are mark_dead'd, their args remain in all_args as dead space. This is acceptable because constraint stores are typically small and short-lived — the entire ChrStateData is rebuilt during compose pipeline operations.

4. **Separate `inst_args` parameter for match_head:** Rather than passing ChrStore to match_head, we pass the args slice separately. This keeps the function signature clean and avoids lifetime complications.

## Files changed

- `src/chr/mod.rs` — Core restructuring: CInstance layout, ChrStore with all_args buffer, args/args_mut accessors, updated apply_subst_to_data, remap_vars, remap_and_apply_subst, match_head, combine_owned, rebuild_indexes, collect_vars, display
- `src/chr/tests.rs` — Updated test helper to use new ChrStore::args() accessor
- `src/kernel/compose.rs` — Updated test to use new ChrStore::args() accessor

## Why 3.65% instead of more

The 3.61% ChrStateData::clone hotspot includes cloning ALL fields of ChrStateData (inst Vec, all_args Vec, preds Vec with HashMaps, agenda VecDeque, tokens). The optimization primarily improves the Vec<CInstance> clone cost (smaller instances) and adds the efficient Vec<TermId> clone (contiguous memcpy). The PredStore HashMap clones and token FxHashSet clones remain unchanged.

## Remaining opportunities

- The PredStore HashMap clones within ChrStateData::clone are still O(n) per HashMap. Arc-wrapping PredStore data could make this O(1).
- The PropTokens `fired: Vec<FxHashSet<TokenKey>>` clone is also O(n) per set. For propagation-free workloads (all simplification rules), these sets are empty but still allocated.
- The `all_args` buffer could be compacted during clone to remove dead instance holes, but the stores are small enough that this is unlikely to matter.
