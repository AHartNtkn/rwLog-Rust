# Investigation: Pre-flatten CHR rule body instructions

## Summary

Attempted to pre-flatten CHR rule body instructions into contiguous `FlatBodyOp` arrays (paralleling the flat_chr_match approach for head matching). No significant improvement on the primary workload.

**Baseline:** 1375469us (median, all values: 1299921, 1926463, 2320242, 1493501, 1387322, 1296639, 1293747, 1365750, 1368998, 1381940)
**After:** 1374155us (median, all values: 1376516, 2336197, 2291112, 1482634, 1334594, 1308406, 1372762, 1375548, 1337483, 1363691)
**Improvement:** 0.10% (not significant)
**Mann-Whitney U:** 47/100 (not significant)
**Regression:** N/A

## Problem

The CHR body execution path `exec_with_data` is called for every successful rule firing inside `solve_to_fixpoint`. The code interprets `BodyInstr` enum variants, allocating a new `SmallVec<[TermId; 8]>` via `collect_args` for each instruction, and dispatching through `eval_arg_expr` for each argument. The hypothesis was that pre-flattening body instructions (like flat_chr_match did for head matching) could eliminate this per-instruction overhead.

## Solution Attempted

Created `FlatBodyOp` enum with variants: `BeginAddChr`, `ArgRVar`, `ArgConst`, `ArgPat`, `CommitAddChr`, `BeginAddBuiltin`, `CommitAddBuiltin`, `Fail`. Pre-flattened each rule's `BodyProg` into `Box<[FlatBodyOp]>` at program construction time. Added `exec_flat_body` function that interprets flat ops with a single reusable `SmallVec<[TermId; 8]>` args buffer.

## Why it failed

1. **SmallVec<[TermId; 8]> is already stack-allocated for common cases.** With 8 inline slots (32 bytes), the original `collect_args` never heap-allocates for typical constraint args (1-4 args). The "saving" of reusing one SmallVec across instructions is negligible — each per-instruction SmallVec is already free.

2. **ArgExpr enum dispatch is trivially predicted.** The CPU branch predictor handles the 3-way ArgExpr match (RVar/Const/Pat) perfectly since most args are RVar or Const. The flat ops eliminate this match but the match was essentially free.

3. **Body execution is not the bottleneck.** Despite being called on every rule firing, body execution is a small fraction of solve_to_fixpoint time. The dominant costs are: index lookup for candidates, match_head pattern matching, and constraint store management (add_chr, mark_dead).

4. **The flat_chr_match analogy doesn't transfer.** Head matching eliminated PatArena indirection (pointer chasing through a tree) and reduced stack entry size from 16 to 4 bytes. Body execution has no analogous tree indirection — it's already a flat loop over instructions. The overhead being eliminated (SmallVec reuse, enum dispatch) is categorically smaller than what flat_chr_match eliminated.

## Files changed

- `src/chr/mod.rs` — Added `FlatBodyOp` enum, `flatten_body_prog` function, `exec_flat_body` function, `body_flat_ops` field on Rule (reverted, DISCARD)

## Remaining opportunities

- Body execution overhead is negligible for this workload. Further body optimization would only help workloads with very complex rule bodies (many pattern-constructing args).
- The `instantiate_pat` function (used for `ArgExpr::Pat`) does allocate two Vecs per call, but this is only triggered for complex pattern arguments which are rare.
