# Investigation: Iterative Drop for Node<C>

## Summary

Attempted to implement a custom iterative `Drop` for `Node<C>` to avoid stack overflow on deep Or/Emit chains and reduce the ~5.65% drop overhead. The implementation compiled and passed tests but **regressed performance** — DISCARDED.

**Baseline:** 19.56ms (median)
**After:** 19.82ms (median)
**Regression:** ~1.3%
**Mann-Whitney U:** 22/100 (significant regression)

## Problem

From profiling of `recursive_even_backward_first64`:
- `drop_in_place Node<C>` = 5.65% of total time

The default recursive destructor walks Or/Emit chains via the call stack, and on deep trees could potentially overflow.

## Approach

1. **`NodeParts<C>` mirror enum**: Created a second enum with identical variants but no `Drop` impl, allowing free destructuring via pattern matching.
2. **`Node::into_parts()`**: Used `ManuallyDrop` + `ptr::read` to convert a `Node<C>` into `NodeParts<C>` without running Drop.
3. **Custom `Drop` impl**: Replaced self with `Node::Fail` via `mem::replace`, then iteratively processed Or/Emit children using a `SmallVec<[Node<C>; 8]>` explicit stack.
4. **All match sites converted**: `step_node`, `step_or`, and other match sites were changed to use `node.into_parts()` + `NodeParts::*` patterns.

## Why it regressed

The overhead comes from several sources:
1. **`mem::replace` in Drop**: Every single Node drop (even Fail nodes on the fast path) had to check the variant and potentially replace self.
2. **SmallVec allocation**: The explicit stack requires allocation when >8 nodes deep.
3. **`into_parts()` indirection**: Every match site now pays for `ManuallyDrop` + pointer cast + `ptr::read` instead of direct pattern matching.
4. **Layout assumption risk**: The `NodeParts` transmute relies on identical layout between two `#[derive(Clone, Debug)]` enums — not guaranteed by Rust without `#[repr(C)]`.

The 5.65% "drop" overhead in the profile likely includes both actual deallocation (which this doesn't help) and the overhead of recursively visiting children (which the iterative approach trades for its own overhead). For the typical tree depths in `recursive_even_backward_first64`, the default recursive drop is faster.

## Files changed (not merged)

- `src/node.rs` — Added `NodeParts<C>`, `into_parts()`, custom `Drop`, converted all match sites.

## Lessons

- Custom Drop on a frequently-destructured enum is extremely invasive in Rust (prevents `match` moves).
- The `NodeParts` workaround adds per-match overhead that dominates the drop savings.
- This optimization would only help workloads with very deep Or/Emit chains (>1000 levels) where stack overflow is a real risk. For normal depths, the default recursive drop wins.
- A better approach might be to limit Or-chain depth structurally (balanced trees) rather than working around it in Drop.
