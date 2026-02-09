# Investigation: Box NF in Node::Emit to Shrink Node Enum

## Summary

Changed `Node::Emit(NF<C>, Box<Node<C>>)` to `Node::Emit(Box<NF<C>>, Box<Node<C>>)`, shrinking the Node enum from ~136 bytes to ~24 bytes. This reduces the cost of every Node copy, Box allocation, drop, and stack spill by 5.7×. ~19% improvement on `recursive_even_backward_first64`, ~8% on `treecalc_first16`.

**Baseline:** 16.73ms (median)
**After:** 13.52ms (median)
**Improvement:** ~19.2% (independently verified)
**Mann-Whitney U:** 100/100 (p < 0.01)
**Regression:** None — secondary also improved 7.6% (0.85ms → 0.79ms)

## Problem

From profiling of `recursive_even_backward_first64`:
- `__memmove_avx_unaligned_erms` (memcpy) = 11.58% of total time
- `core::ptr::drop_in_place<Node>` = 6.17% of total time
- Combined 17.75% of runtime in Node copy/drop operations

The Node enum was sized by its largest variant:
```rust
pub enum Node<C: ConstraintOps> {
    Fail,                           // 0 bytes data
    Or(Box<Node<C>>, Box<Node<C>>), // 16 bytes data
    Emit(NF<C>, Box<Node<C>>),      // 128 bytes data (NF is 120B)
    Work(Box<Work<C>>),             // 8 bytes data
}
```

With discriminant and alignment, Node was ~136 bytes. Every Node operation — moving into/out of Box, Or spine walking, step_node dispatch, stack spills — processed 136 bytes even for the tiny Fail/Or/Work variants that only need 0-16 bytes.

perf annotate showed DiagonalJoin::pull_side_in_place calling memcpy with 0x88 (136) bytes per Node copy. step_node had a 1320-byte stack frame partly due to Node-sized locals.

## Solution

Box the NF in the Emit variant:
```rust
pub enum Node<C: ConstraintOps> {
    Fail,
    Or(Box<Node<C>>, Box<Node<C>>),
    Emit(Box<NF<C>>, Box<Node<C>>),  // Now 16 bytes data
    Work(Box<Work<C>>),
}
```

Node shrinks from ~136B to ~24B (max variant is Or/Emit at 16B data + discriminant).

Construction sites wrap NF in Box::new():
```rust
// Before:
Node::Emit(nf, Box::new(Node::Fail))
// After:
Node::Emit(Box::new(nf), Box::new(Node::Fail))
```

Consumption sites dereference the box:
```rust
// Before:
Node::Emit(nf, rest) => NodeStep::Emit(nf, *rest)
// After:
Node::Emit(nf, rest) => NodeStep::Emit(*nf, *rest)
```

The cost is one additional heap allocation (Box::new) per Emit construction and one deallocation per Emit consumption. With mimalloc, these are ~10ns each — negligible compared to the memcpy savings.

## Files changed

- `src/node.rs` — Node enum definition, step_node, size assertion (tightened to <= 24 bytes), tests
- `src/work/mod.rs` — 4 Node::Emit construction sites in rel_to_node
- `src/work/tests.rs` — ~40 Node::Emit construction sites (mechanical)

## Why 19% instead of 7-12%

The initial estimate underestimated the compound effects:
1. **Everywhere Node moves**: Not just DiagonalJoin::pull_side_in_place (6.74% of memcpy) but also step_or (Or spine walking), rebuild_or_chain, every Box::new(Node), and function return values
2. **Stack frame reduction**: step_node's 1320B frame shrinks significantly because Node-sized local variables are now 24B instead of 136B. Smaller frames improve instruction cache and stack cache behavior
3. **Drop cost reduction**: Dropping a 24B Node is cheaper than dropping a 136B Node (less memory to zero/release, better cache behavior during recursive drops)
4. **Universal benefit**: Both primary and secondary workloads improved, confirming this is a structural improvement that benefits all evaluation patterns

## Notes

NodeStep::Emit(NF<C>, Node<C>) retains inline NF — it's a stack return value consumed immediately by the caller, so boxing would add unnecessary indirection there. The Node shrinking specifically targets the stored/boxed Node instances that dominate memory traffic.
