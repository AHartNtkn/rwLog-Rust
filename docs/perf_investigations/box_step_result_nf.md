# Investigation: Box NF in DiagonalStepResult/FixStepResult

## Summary

Attempted to box `NF<C>` in the `Emit` variant of `DiagonalStepResult` and `FixStepResult` to shrink these return values from ~128B to ~16B, reducing sret (struct-return) copy costs from step_in_place functions. Both versions (full and partial) regressed.

**Verdict:** DISCARD
**Full boxing (both types):** ~3.5% regression (U=0/100)
**Partial (DiagonalStepResult only):** ~5% regression (U=0/100)

## Problem

After Round 6's successful NodeStep boxing (152B → 40B, ~2.6% improvement), the next largest sret return values were `DiagonalStepResult<C>` and `FixStepResult<C>`, both ~128B due to inline `NF<C>` (~120B) in their `Emit` variant:

```rust
pub enum DiagonalStepResult<C: ConstraintOps> {
    Emit(NF<C>),  // ~120B
    More,
    Done,
}
pub enum FixStepResult<C: ConstraintOps> {
    Emit(NF<C>),  // ~120B
    More,
    Done,
}
```

These are returned from ComposeWork::step_in_place, MeetWork::step_in_place (both `#[inline(never)]`), and FixWork::step_in_place. In step_node, the NF from these results is then boxed for NodeStep::Emit — so the Box::new could be moved to the construction site (allocation-neutral).

## Approaches Tried

### Attempt 1: Box both DiagonalStepResult and FixStepResult

Changed both types to `Emit(Box<NF<C>>)`. Updated 5 construction sites (3 in diagonal.rs, 2 in fix.rs) and 3 consumption sites (3 in node.rs — removed redundant Box::new).

**Result:** ~3.5% regression (U=0/100). Every optimized sample was slower.

### Attempt 2: Box only DiagonalStepResult (not FixStepResult)

Hypothesis: FixWork::step_in_place is likely inlined into step_node (not marked `#[inline(never)]`), so boxing its return adds allocation without sret savings. Only box DiagonalStepResult for ComposeWork/MeetWork which ARE `#[inline(never)]`.

**Result:** ~5% regression (U=0/100). Even worse than full boxing.

## Why It Failed

1. **sret is already well-optimized for these functions.** The compiler only writes the relevant variant data through the sret pointer — for More/Done, it writes just the discriminant, not the full 128B. The large enum size only matters for Emit, where we're adding a Box::new either way (just moving it from caller to callee).

2. **Box::new inside the callee is worse than in the caller.** In step_node, the NF arrives on the stack (cache-hot) and Box::new copies it to the heap. Inside step_in_place, the Box::new happens at multiple construction sites with different data flow patterns, potentially at a point where the data isn't cache-optimal.

3. **Code generation butterfly effects.** Modifying the return type of hot functions changes register allocation, stack layout, and instruction scheduling throughout step_node. The profile showed that step_node is highly sensitive to code generation details (42.54% self-time with hot cache-miss instructions).

4. **Different from NodeStep boxing.** NodeStep boxing worked because ALL step_node return paths write through the same sret pointer, and the function is much larger with many temporaries competing for stack/register space. step_in_place functions are simpler — the compiler handles their sret efficiently without boxing.

## Key Insight

The success of NodeStep boxing (152B → 40B) does NOT generalize to all large enum return values. The benefit depends on:
- How many code paths write through the sret pointer (more paths = more benefit from smaller sret)
- Whether the function is inlined (inlined = no sret, boxing is pure overhead)
- The complexity of the callee (simpler callee = compiler optimizes sret well already)
- Whether the Box::new can be elided by moving it vs. adding a new allocation

## Files changed (in worktree, not merged)

- `src/work/diagonal.rs` — DiagonalStepResult::Emit changed to Box<NF<C>>
- `src/work/fix.rs` — FixStepResult::Emit changed to Box<NF<C>> (attempt 1 only)
- `src/node.rs` — Updated consumption sites to pass Box directly
