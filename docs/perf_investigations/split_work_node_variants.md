# Investigation: Split Node::Work into Specialized Node Variants

## Summary

Attempted to split `Node::Work(Box<Work<C>>)` into separate Node variants (`Node::FixWork(Box<FixWork>)`, `Node::ComposeWork(Box<ComposeWork>)`, `Node::MeetWork(Box<MeetWork>)`) to eliminate the Work discriminant cache miss (5.63% of step_node self-time) and the if-let dispatch chain. The change caused a 12% regression.

**Verdict:** DISCARD
**Regression:** ~12% slower (U=0/100)

## Problem

In step_node, the `Node::Work(mut work)` arm dispatches through a chain of if-let statements:

```rust
if let Work::Fix(ref mut fix) = *work { ... }       // 5.63% cache miss here
if let Work::Compose(ref mut compose) = *work { ... }
if let Work::Meet(ref mut meet) = *work { ... }
match work.step(terms) { ... }  // fallthrough
```

The first `if let` dereferences `Box<Work>` and loads the Work discriminant from heap memory, often cache-missing. The hypothesis was that encoding the work type in the Node discriminant (already in registers) would skip this dereference.

## Approach

Added FixWork, ComposeWork, MeetWork as direct Node variants. Each takes `Box<SpecificWorkType>` directly, eliminating the Work enum indirection for the hot paths. The generic `Work` variant was kept for cold-path types (Pipe, Atom, JoinReceiver, etc.).

A `work_to_node` helper function converted `Box<Work<C>>` → Node by matching on the Work discriminant and re-wrapping into the appropriate Node variant.

## Why It Failed

The fundamental problem: **re-boxing overhead dominates.**

When `PipeWork::step()` returns `WorkStep::More(Box::new(Work::Compose(...)))`, the `work_to_node` function must:
1. Dereference the `Box<Work>`
2. Match on the Work discriminant
3. Destructure to extract the inner type
4. Allocate a new `Box<ComposeWork>`
5. Deallocate the old `Box<Work>`

This re-boxing happens on every WorkStep transition. The cost of allocate + deallocate + copy per transition far exceeds the original 5.63% cache miss on the Work discriminant, which only happens once per step_node call and is amortized over the actual work done.

The original design is actually well-optimized: `step_in_place` keeps the Work inside the same `Box<Work>` across steps, reusing the heap allocation. The specialized variants force re-allocation because WorkStep returns `Box<Work>`, not type-specific boxes.

## What Would Be Needed

A correct version of this optimization would require changing the WorkStep return type to avoid the re-boxing path — either having work types directly produce Node variants, or having WorkStep be generic over the specific work type. This would be a much larger refactor touching the entire work/node interface, and it's unclear if the 2-3% potential gain justifies the complexity.

## Files changed (in worktree, not merged)

- `src/node.rs` — Added FixWork, ComposeWork, MeetWork variants; work_to_node helper; updated step_node
- `src/work/mod.rs` — Updated wrap_compose_with_prefix_suffix
- `src/work/pipe.rs` — Updated fix_node construction
- `src/work/tests.rs` — Updated test helpers

## Notes

The existing if-let chain in step_node is actually the right design for this architecture. The step_in_place pattern avoids allocation by reusing the Box<Work>, and the 5.63% cache miss is the unavoidable cost of accessing heap-allocated Work data. The cache miss would still exist with specialized variants — it would just happen at the first field access instead of the discriminant load.
