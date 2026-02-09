# Investigation: Specialize solve_to_fixpoint for single-head simplification rules

## Summary

Specialized the CHR `solve_to_fixpoint` loop for programs where all rules are single-head simplification rules. Eliminates Vec allocations, SearchCtx construction, recursive search_steps_inner, and propagation token handling. ~7.1% improvement on treecalc_synth_flip.

**Baseline:** 1325042us (median, all values: 1339583, 1343855, 1323851, 1344830, 1296084, 1294389, 1324312, 1323598, 1346946, 1325772)
**After:** 1231211us (median, all values: 1232222, 1245456, 1269758, 1259322, 1195696, 1198940, 1199522, 1219144, 1230201, 1269783)
**Improvement:** ~7.1% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001, complete separation)
**Regression:** None observed on recursive_even_backward_first64 (U=67/100, neutral)

## Problem

`solve_to_fixpoint` is inside the 50.93% inclusive `normalize_owned` hotspot. For treecalc_synth_flip, ALL CHR rules are single-head simplification rules, yet the code used the general multi-head join framework:

1. `find_match_by_ids_reuse` allocated `Vec<Option<Cid>>` of length 1 (heap alloc for single-element Vec)
2. Created `SearchCtx` struct on every match attempt
3. Called `search_steps_inner` recursively (for single-head rules with no join steps, this just evaluates the guard and returns)
4. Allocated `Vec<Cid>` of length 1 for the tuple result (another heap alloc)
5. Checked `rule.is_propagation` and created `TokenKey` (unnecessary for simplification rules)

## Solution

Added `all_single_head_simplification: bool` flag to `ChrProgram`, computed at build time (true iff all rules have `heads.len() == 1` and `!is_propagation`).

When set, `solve_to_fixpoint` dispatches to `solve_to_fixpoint_single_head` which:
- Directly calls `match_head` on the anchor head (no Vec<Option<Cid>> chosen array)
- Evaluates the guard directly using the env (no SearchCtx, no search_steps_inner recursion)
- Calls `mark_dead` directly on the matched CID (no Vec<Cid> tuple, no removed_mask iteration)
- Calls `exec_with_data` directly (no propagation token creation/checking)

The general path was refactored into `solve_to_fixpoint_general` with no behavioral changes.

### Key design decisions

1. **Compile-time flag on ChrProgram rather than per-rule dispatch**: Checking the flag once at the start of solve_to_fixpoint is cheaper than per-occurrence checks. The flag is computed at program build time, adding zero runtime cost.
2. **Unconditional mark_dead for single-head simplification**: CHR semantics guarantee that simplification rules remove all matched constraints. For single-head rules, this means the one matched constraint is always removed.
3. **Preserved the general path unchanged**: The `solve_to_fixpoint_general` method is identical to the old code (just refactored to take `program` and `d` as parameters). No risk of regression for programs with multi-head or propagation rules.

## Files changed

- `src/chr/mod.rs` — Added `all_single_head_simplification` flag to `ChrProgram`, computed at build time; split `solve_to_fixpoint` into general and specialized paths (+106 lines, -9 lines)

## Why 7.1% instead of more

The specialization eliminates per-match-attempt overhead but not the actual matching work (match_head/match_flat_ops) or body execution, which dominate the solve_to_fixpoint loop. The 7.1% improvement represents the Vec allocations + function call overhead + cache effects from the extra code paths. The actual matching and body execution remain unchanged.

## Remaining opportunities

- The solve_to_fixpoint loop still acquires a read_lock per match_head call. Passing `&mut TermStore` and using `get_unlocked` for the entire loop could eliminate lock overhead (though chr_lock_hoist showed this is ~10ns per call).
- Body execution (`exec_with_data`) could be similarly specialized for common body patterns (all-RVar args, single AddChr instruction).
- The `instantiate_pat` function in body execution allocates two Vecs per call — SmallVec-ifying these could help for workloads with pattern-constructing rule bodies.
