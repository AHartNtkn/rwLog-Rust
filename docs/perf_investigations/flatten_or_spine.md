# Investigation: Flatten Or Spine to Eliminate Recursive Drop

## Summary

Attempted to replace `Node::Or(Box<Node>, Box<Node>)` binary tree with a flat `Vec<Node>` or `VecDeque<Node>` representation to eliminate recursive drop overhead (6.16% of runtime). Both approaches regressed performance.

**Verdict:** DISCARD
**Vec attempt:** ~1.6% regression (U=17/100)
**VecDeque attempt:** ~0.8% regression (U=13/100)

## Problem

Post-Round-6 profiling showed `core::ptr::drop_in_place<Node>` at 6.16% of total runtime. The Node drop is recursive: dropping an Or chain of depth N requires N recursive calls, each loading the Node discriminant (17.63% of drop time on that single instruction — a cache miss).

The hypothesis was that a flat Vec/VecDeque representation would make drop iterative (Vec::drop iterates its elements), eliminating recursive stack frames and cache-missing discriminant loads.

## Approaches Tried

### Attempt 1: Vec-based `Node::Or(Box<Vec<Node<C>>>)`

Changed Or from binary tree to flat Vec. step_or uses `Vec::remove(0)` to pop the first branch.

**Result:** ~1.6% regression. `Vec::remove(0)` is O(n) because it shifts all remaining elements left. This shift happens on every Or step, adding more overhead than the recursive drop savings.

### Attempt 2: VecDeque-based `Node::Or(Box<VecDeque<Node<C>>>)`

Switched to VecDeque for O(1) `pop_front`/`push_back` rotation.

**Result:** ~0.8% regression. VecDeque's ring buffer indexing overhead and different allocation patterns offset the iterative drop savings. The ring buffer metadata and wrap-around logic add per-access overhead that doesn't exist with the simple binary tree.

### Attempt 3: Custom Drop impl (abandoned)

Implementing `Drop` for `Node` to iteratively walk Or chains was abandoned because implementing Drop prevents moving out of enum fields in `match` statements. This would require restructuring step_node, step_or, and every pattern match site — a pervasive change.

## Why It Failed

1. **The recursive drop cost is overstated.** The 6.16% in the profile is partially a sampling artifact — the per-drop cost is small, and the nodes being dropped were recently accessed (good temporal locality). The compiler-generated recursive drop has surprisingly good cache behavior.

2. **Flat containers add overhead.** Both Vec and VecDeque have per-access overhead (bounds checks, pointer arithmetic, ring buffer indexing) that doesn't exist with the simple two-pointer Or node. The binary tree representation is cache-efficient because each Or node is only 24B (two 8B Box pointers + discriminant).

3. **Or trees are shallow in practice.** For the critical workload (recursive_even_backward_first64), Or chains are typically short. The step_or spine walk already handles this efficiently with a temporary Vec that's built and consumed in one step.

4. **Allocation patterns change.** Vec/VecDeque allocate a contiguous buffer that must grow/shrink, while the binary tree uses individual Box allocations that mimalloc handles efficiently with thread-local free lists.

## Files changed (in worktree, not merged)

- `src/node.rs` — Node::Or changed to flat representation, step_or rewritten
- `src/work/mod.rs` — Or construction sites updated
- `src/work/pipe.rs` — Or construction in call handling updated
- `src/work/tests.rs` — Test Or constructions updated

## Notes

The 6.16% drop overhead may be fundamentally unavoidable without unsafe code (ManuallyDrop) or architectural changes to how nodes are allocated (arena allocation). The previous iterative drop investigation (ManuallyDrop + NodeParts) also failed (1.3% regression) due to into_parts() overhead. The conclusion: Node drop at ~6% is the cost of the current architecture, and attempts to reduce it add more overhead than they save.
