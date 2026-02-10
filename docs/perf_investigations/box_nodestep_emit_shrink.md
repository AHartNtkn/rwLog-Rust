# Investigation: Box NF in NodeStep::Emit to Shrink NodeStep Enum

## Summary

Changed `NodeStep::Emit(NF<C>, Node<C>)` to `NodeStep::Emit(Box<NF<C>>, Node<C>)`, shrinking the NodeStep enum from ~152B to ~40B. This reduces sret (struct-return) copy costs when step_node returns Emit, and further shrinks step_node's stack frame. ~2.6% improvement on `recursive_even_backward_first64`, no secondary regression.

**Baseline:** 13.425ms (median, independently verified)
**After:** 13.075ms (median, independently verified)
**Improvement:** ~2.6% (worker measured 3.14%)
**Mann-Whitney U:** 100/100 (p < 0.01)
**Regression:** None — secondary neutral (0.77ms both)

## Problem

After the Round 5 box-emit optimization shrank Node from ~136B to ~24B, the NodeStep enum remained large:

```rust
pub enum NodeStep<C: ConstraintOps> {
    Emit(NF<C>, Node<C>),    // ~120B + ~24B = ~144B data
    Continue(Node<C>),        // ~24B data
    Exhausted,                // 0B data
}
```

With discriminant and alignment, NodeStep was ~152B. Every call to `step_node()` returns a NodeStep by value (sret convention — caller allocates space, callee writes through a pointer). The 152B size means:
- Every step_node return copies 152B even for Continue/Exhausted
- step_node's stack frame includes space for NodeStep-sized temporaries
- Callers (engine.rs, diagonal.rs, fix.rs, and_group.rs) all allocate 152B for the return value

Post-box-emit profiling showed memcpy had collapsed from 11.58% to 0.56%, but step_node's frame was still 1000 bytes. The NodeStep return value was a remaining source of unnecessary data movement.

## Solution

Box the NF in the Emit variant:
```rust
pub enum NodeStep<C: ConstraintOps> {
    Emit(Box<NF<C>>, Node<C>),  // 8B + ~24B = ~32B data
    Continue(Node<C>),           // ~24B data
    Exhausted,                   // 0B data
}
```

NodeStep shrinks from ~152B to ~40B (max variant is Emit at 32B data + discriminant).

Construction sites in step_node wrap NF in Box::new():
```rust
// Before:
NodeStep::Emit(nf, Node::Work(work))
// After:
NodeStep::Emit(Box::new(nf), Node::Work(work))
```

Consumption sites dereference the box:
```rust
// Before: engine.rs
StepResult::Emit(nf)
// After:
StepResult::Emit(*nf)

// Before: diagonal.rs
let nf = Arc::new(nf);
// After:
let nf = Arc::new(*nf);
```

The cost is one Box::new per Emit (heap allocation) and one dereference per consumption. With mimalloc, this is ~10ns — negligible compared to the sret copy savings across all step_node calls (Emit, Continue, and Exhausted all benefit from the smaller return size).

## Files changed

- `src/node.rs` — NodeStep enum definition, step_node construction sites (5 Emit paths)
- `src/engine.rs` — Engine::next() unboxes NF
- `src/work/fix.rs` — step_table_producer unboxes NF for table.add_answer()
- `src/work/diagonal.rs` — DiagonalJoin pull_side_in_place unboxes NF at 2 Arc::new() sites
- `src/work/and_group.rs` — AndProducer::step() unboxes NF

## Why this helps despite small size difference

The improvement is modest (~2.6%) because:
1. NodeStep is a **return value**, not a stored/boxed value — it's created and immediately consumed, so it doesn't participate in the Box/clone/drop chains that made Node shrinking so impactful
2. The benefit is entirely from reduced sret copy sizes and step_node stack frame reduction
3. Post-box-emit, memcpy was already only 0.56% of runtime, so there was less copy overhead to eliminate

## Relationship to Round 5 box-emit

This is a companion optimization to the Round 5 Node::Emit boxing. Together they form a complete size reduction:
- Round 5: Node from ~136B to ~24B (19% improvement)
- Round 6: NodeStep from ~152B to ~40B (2.6% improvement)

The asymmetry in impact reflects that Node is stored/boxed/cloned extensively (dominating memory traffic) while NodeStep is a transient return value (affecting only sret copies).

## Notes

The NF is immediately unboxed at every consumption site. This means the heap allocation is extremely short-lived — allocated in step_node, freed in the caller. mimalloc handles this pattern efficiently with thread-local free lists.
