# Investigation: Engine Tight Loop — Manual step_node Inlining

## Summary

Manually inlined `step_node` into `Engine::next()` to keep the current `Node` on the stack instead of round-tripping through `self.root` per step. No measurable improvement — the compiler already performs this optimization.

**Verdict:** DISCARD
**Result:** No improvement (U=39/100)

## Problem

In `Engine::next()`, each iteration calls `self.step()` which does:
1. `mem::replace(&mut self.root, Node::Fail)` — takes the node out
2. `step_node(node, &mut self.terms)` — steps it
3. Writes the continuation node back to `self.root`
4. Returns a `StepResult`

The hypothesis was that this mem::replace + write-back pattern forces the Node through memory (self.root lives on the heap as part of Engine), when the hot loop could keep the Node on the stack and only write it back when returning from next().

## Approach

Rewrote `Iterator::next()` to inline the step_node call directly:
1. Take the Node out of self.root once at the start
2. Loop calling step_node directly, keeping the continuation Node on the stack
3. Only write back to self.root when returning (Emit or Exhausted)
4. Made `step()` and `StepResult` `#[cfg(test)]` since they'd only be used in tests

## Results

### Primary Workload: recursive_even_backward_first64
- Baseline timings: [13.03, 12.79, 12.78, 12.78, 14.97, 13.03, 13.32, 13.21, 13.12, 13.27]
- Optimized timings: [12.83, 12.99, 12.88, 13.80, 16.01, 14.34, 12.91, 13.39, 13.00, 13.44]
- Baseline median: 13.07ms
- Optimized median: 13.20ms
- U statistic: 39/100
- Change: -0.92% (noise)

### Secondary Workload: treecalc_first16
- Baseline median: 0.77ms
- Optimized median: 0.77ms
- U statistic: 50/100 (58.5 with ties)
- Change: -0.65% (noise)

## Why It Failed

The compiler (LLVM) is already optimizing the `step()`/`next()` boundary effectively:

1. **Inlining.** At release optimization levels (`-O2`/`-O3`), `step()` is almost certainly inlined into `next()`. The function boundary we tried to eliminate didn't actually exist in the generated code.

2. **Register promotion.** The `mem::replace` + write-back pattern is a well-known idiom that LLVM optimizes effectively. The Node (now only ~24B) likely stays in registers across the loop without actually touching `self.root` memory on each iteration.

3. **No actual overhead to eliminate.** The per-step overhead is not at the Engine::next() dispatch level — the bottleneck is deeper inside `step_node` itself (pattern matching, term operations, node tree restructuring).

## Key Insight

This confirms that the engine loop wrapper contributes negligible overhead. Future optimization efforts should focus on the inner workings of `step_node` and the node stepping logic (work dispatch, compose/meet operations, substitution) rather than the engine loop wrapper.

## Files changed (in worktree, not merged)

- `src/engine.rs` — Inlined step_node into Iterator::next(), made step()/StepResult cfg(test)
