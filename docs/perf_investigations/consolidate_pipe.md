# Investigation: Consolidation — Simplify Front/Back Duplication in pipe.rs

## Summary

Consolidation round eliminating duplicated front/back logic in PipeWork and unifying root functor utilities between pipe.rs and compose.rs. -70 lines (233 insertions, 303 deletions). Performance neutral as expected.

**Baseline (full corpus):** 643,018 us (median, all values: 1136660, 821168, 862492, 700649, 644082, 635567, 645708, 625550, 643018, 636515)
**After:** 640,969 us (median, all values: 828438, 841005, 868359, 629754, 641609, 640969, 627150, 625420, 639063, 637701)
**Mann-Whitney U:** 61/100 (not significant — expected for consolidation)
**treecalc_synth_flip spot-check U:** 30/100 (not significant — no regression)
**Regression:** None

## Changes

### 1. Unified root functor utilities (MEDIUM priority)

Moved `RootTag` enum, `build_root_tag()`, `match_root_tag()`, `tags_compatible()` from `compose.rs` to `work/mod.rs` as shared utilities. Removed the parallel `term_root_functor()`, `build_root_functor()`, `match_root_functor()` functions from `pipe.rs` that used `Option<FuncId>` instead of `RootTag`. Both `pipe.rs` and `compose.rs` now use the same `RootTag`-based approach.

### 2. Unified absorb_front/absorb_back (MEDIUM priority)

Replaced two near-identical methods with a single `absorb_at(end: PipeEnd, nf, terms) -> bool` that parameterizes direction. Boundary selection (`self.left` vs `self.right`) and composition order (`compose_nf(left, nf)` vs `compose_nf(nf, right)`) are determined by the `PipeEnd` enum.

### 3. Unified try_normalize_step front/back (HIGH priority)

Extracted `try_normalize_end(end, terms)` that handles Zero, Atom, and Seq normalization for either direction. `try_normalize_step()` now iterates over `[PipeEnd::Front, PipeEnd::Back]` instead of duplicating the match arms.

### 4. Unified try_batch_advance_calls front/back (HIGH priority)

Extracted `try_advance_call_at_end(end, terms)` that handles Call lookup, Atom composition, and Or dispatch filtering for either direction. The outer loop iterates over ends instead of duplicating ~75 lines.

### 5. Refactored handle_call and try_dispatch_or_atoms

Changed `absorb_front: bool` parameter to `end: PipeEnd` for type-safe direction handling throughout the dispatch and call resolution paths.

### 6. Added order_by_end helper

Common pattern for constructing `(left_node, right_node)` from a produced node and remaining pipe, parameterized by direction. Used in `handle_call` and `advance_fix`.

## Files changed

- `src/work/mod.rs` — Added shared `RootTag`, `build_root_tag`, `match_root_tag`, `tags_compatible` (+62 lines)
- `src/work/compose.rs` — Removed local `RootTag` and functor extraction functions, imports from mod.rs (-49 lines)
- `src/work/pipe.rs` — Replaced duplicated front/back logic with parameterized helpers, removed local root functor functions (-233 net lines in pipe.rs)

## Why this matters

Four optimization workers incrementally added features to pipe.rs in the same round:
- `mid_normalized` flag (pipe_lazy_mid)
- `try_batch_advance_calls()` (pipe_batch_advance)
- Root functor dispatch (compiled_dispatch)
- Semi-naive watermark support

Each worker independently duplicated front/back logic because they worked in isolation. This consolidation unifies those patterns, reducing the maintenance surface and making future changes to the pipe evaluation path require changes in one place instead of two.
