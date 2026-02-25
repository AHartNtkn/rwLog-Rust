# Investigation: try_split_call_atom_call (REMOVED — fundamentally unsound)

## Summary

`try_split_call_atom_call` detected `[Call1, Atom, Call2]` patterns in PipeWork mid and split them into `Compose(Pipe[Call1, right=domain_filter(Atom)], Pipe[Atom ; Call2])` to parallelize both Calls via DiagonalJoin. Removed because the split is fundamentally unsound: the Atom transforms data, and any placement of the Atom on one side loses the transformation at the compose interface for the other direction.

**Origin:** Commit a4992f4 ("fix duality"), not a numbered PERF investigation.

**Symptom:** `k ; $p -> (pair $p nil) ; eval` runs forever. k produces `(lam ...)`, the right pipe produces NFs matching `(pair ... nil)` — root functor mismatch at the compose interface. Zero successful compositions despite 113+ right-side NFs.

## The Problem

The original split placed the Atom on the right side:
- Left pipe: `[Call1]` with `right = nf_domain_filter(Atom)`
- Right pipe: `[Atom, Call2]` with `left = None`

This loses the Atom's transformation at the compose interface. Call1 produces raw output (e.g., `(lam ...)`), but the right pipe's NFs expect Atom-transformed input (e.g., `(pair ... nil)`). The root functor mismatch causes all compose attempts to fail, and the right pipe explores Call2's full (potentially infinite) search space without constraint from Call1's output.

## Why No Compromise Exists

The Atom transforms data — it is not a filter. Consider `$p -> (pair $p nil)`:

1. **Atom on the right** (`[Call1] | [Atom, Call2]`): Left produces `(lam ...)`, right expects `(pair ...)` — forward direction broken.

2. **Atom on the left** (`[Call1, Atom] | [Call2]`): Fixes forward, but the dual relation hits the same problem — Call2's output doesn't match the Atom's input domain at the compose interface.

3. **Atom on both sides**: Applies the transformation twice — semantically wrong.

Any split that separates Call1 and Call2 into parallel Compose halves must place the Atom somewhere, and that placement breaks one direction. The system must be symmetric (work correctly for dual relations), so no valid placement exists.

## What Works Instead

The normal sequential advance path handles `[Call, Atom, Call]` correctly:
1. Flip selects one end to advance
2. The Call is advanced, creating `Compose(fix_results, remaining_pipe)`
3. The remaining pipe contains the Atom and the other Call
4. The Atom composes into the boundary before the other Call advances
5. The other Call gets properly constrained boundaries

The existing "peek at adjacent mid element" logic (handle_call, line ~1189) already provides the front Call with the Atom's domain as a boundary hint, further optimizing the sequential path.

## Files Changed

- `src/work/pipe.rs` — Removed `try_split_call_atom_call` method and call site
- `src/engine.rs` — Added regression test `simplelam_k_eval_full_must_not_starve`
- `docs/perf_investigations/pipe_lazy_mid_normalize.md` — Updated remaining opportunities (to_vec reference removed)
