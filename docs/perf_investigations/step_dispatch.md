# Investigation: Function-Pointer Dispatch Table for step_node

## Summary

Refactored step_node Work dispatch from sequential if-let checks to a single match statement for potential jump-table optimization. DISCARD: U=67/100, not statistically significant. Branch prediction and LLVM already handle the 4-variant dispatch well.

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 208545 us (mean, all values: 204954, 207825, 210697, 205566, 203412, 206697, 211921, 211441, 212160, 210785)
**After:** 205750 us (mean, all values: 207289, 212197, 201260, 205028, 206777, 199341, 207927, 208484, 203646, 205549)
**Improvement:** ~1.3% (not significant)
**Mann-Whitney U:** 67/100 (not significant)

## Problem

step_node dispatches on Work variants using sequential if-let checks (Fix, Compose, Meet) followed by a fallback work.step() call. The hypothesis was that replacing this with a single match statement would allow the compiler to generate a jump table, reducing branch misprediction overhead.

## Solution Attempted

- Replaced sequential if-let chain with single `match *work` statement giving compiler full variant set
- Extracted `step_work` as `#[inline(never)]` function
- Added `handle_diagonal_step` helper to deduplicate identical Compose/Meet handling

## Why It Failed

1. **Branch prediction handles the 4-variant dispatch well.** The CPU predicts the Node match arm correctly often enough that restructuring provides no material benefit.

2. **LLVM already optimizes the sequential if-let pattern effectively.** In release mode, LLVM likely converts sequential discriminant checks into something equivalent to a jump table. The restructuring doesn't change generated code meaningfully.

3. **The existing fast-paths for Fix/Compose/Meet already cover the main variants.** The remaining variants (Pipe, AndGroup) that fall through to work.step() are cold enough that extra discriminant tests don't matter.

4. **Consistent with prior investigations.** engine_loop_inlining (U=39), split_work_node_variants (12% regression), streamline_fixwork (U=50) — the dispatch structure around Node/Work is well-optimized and resistant to micro-optimization at this level.

## Files changed

- `src/kernel/node.rs` — Refactored step_node Work dispatch to single match

## Remaining opportunities

- Node/Work dispatch structure is at its optimization ceiling for this level of abstraction
- Any structural change to Node enum carries high regression risk (see split_work_node_variants 12% regression)
- Algorithmic changes that reduce the NUMBER of steps are the remaining lever, not making each step's dispatch cheaper
