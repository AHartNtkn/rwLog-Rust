# Investigation: Flat Vec Or with Index-Based Stepping (Disjunction Backlog)

## Summary

Attempted to replace binary Or tree with flat Vec<Node> + cyclic index for O(1) stepping. DISCARDED: 28% regression on left_rec_32. Binary tree depth is small (~4 levels), and FlatOr bookkeeping exceeds tree-walking savings.

**Baseline:** ~70,282 us (median)
**After:** ~90,342 us (median)
**Mann-Whitney U:** 0/100 (all baseline wins — massive regression)
**Verdict:** DISCARD

## Problem

left_rec_32 has 155K Or-spine walks with avg_siblings=1.6, max_siblings=13. The hypothesis was that replacing binary Or(Box, Box) tree with a flat Vec + index would eliminate O(depth) tree walks.

## Implementation

```rust
struct FlatOr<C> {
    branches: SmallVec<[Node<C>; 4]>,
    current: usize,
}
```

- O(1) stepping via cyclic index `(current + 1) % len`
- O(1) exhaustion via `swap_remove`
- Nested Ors flattened at construction and on step returns
- All 722+ tests pass, zero clippy warnings

## Why It Failed

1. **Binary tree depth is tiny:** left_rec_32 has max_siblings=13, meaning ~4 levels of binary tree. Walking 4 pointer hops is extremely fast (cache-line prefetching handles it).

2. **FlatOr bookkeeping exceeds savings:** Each step requires SmallVec indexing + bounds checking, `mem::replace` to extract a branch, potential `extend()` for nested Or flattening, and modular arithmetic.

3. **Node size impact:** Binary Or(Box, Box) uses 16 bytes. FlatOr with SmallVec<[Node; 4]> inline buffer is 96+ bytes, hurting cache locality.

4. **The real bottleneck is compose_nf:** left_rec_32 has 69,762 compose attempts. The 155K Or-spine walks at avg 1.56 siblings each are almost free compared to compose cost.

## Key Insight

Or-spine walk cost is NOT the bottleneck for left_rec_32. The left_rec investigation's claim about "155K Or-spine walks" being the bottleneck was misleading — each walk is ~4 pointer hops, totaling microseconds. The actual cost is dominated by 69,762 compose_nf attempts. Flat Vec representations would only help for MUCH deeper Or trees (100+ branches), which don't occur in practice.

Consistent with prior flatten_or_spine investigation (VecDeque/Vec, 0.8-1.6% regression) — both approaches confirm that Or tree walking is not a bottleneck worth optimizing.

## Files Changed (not merged)

- `src/node.rs` — Added FlatOr struct, rewrote step_or, modified all Node::Or match arms
