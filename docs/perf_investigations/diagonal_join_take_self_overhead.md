# DiagonalJoin take_self() Overhead: In-Place Stepping for ComposeWork/MeetWork

## Summary

Profiled the post-optimization state of the critical `recursive_even_backward_first64` workload (~46ms, 2.28× faster than original ~105ms). Found that **DiagonalJoin::new** accounts for **4.74% of self-time** — entirely from the `take_self()` pattern creating dummy instances. Additionally, **nearly 100% of the 443K `Box<Node>` allocations** (102MB) are dummy `Box<Node::Fail>` created by `take_self()`.

**Estimated improvement from in-place stepping: 10-15% wall-time reduction.**

This is the same alloc-take-box-drop anti-pattern that was fixed for FixWork (yielding ~20% improvement there). Applying the same technique to ComposeWork and MeetWork would eliminate 665K allocations (165MB) — an **88% reduction in total allocations**.

## The Problem: take_self() Pattern

`DiagonalJoin::step()` (used by both ComposeWork and MeetWork) ends every return path with:

```rust
WorkStep::Emit(nf, Box::new(wrap(self.take_self())))
WorkStep::More(Box::new(wrap(self.take_self())))
```

Where `take_self()` does:

```rust
fn take_self(&mut self) -> Self {
    std::mem::replace(self, DiagonalJoin::new(Node::Fail, Node::Fail, S::default()))
}
```

This creates a dummy `DiagonalJoin` with two `Box::new(Node::Fail)` allocations (232 bytes each), then wraps the real data in a new `Box<Work>` (280 bytes). The dummy is then dropped.

**Per step cost:** 3 heap allocations (2 × Box<Node::Fail> + 1 × Box<Work>) and 3 frees.

All the real work in DiagonalJoin (stepping child nodes, updating seen_l/seen_r, push/pop pending) is already done via `&mut self` mutations. The take_self pattern exists solely for the ownership transfer required by the `WorkStep` return type.

## Profiling Evidence

### Current Profile (post all prior optimizations, ~46ms baseline)

Profiled with `perf record -g --call-graph dwarf -F 9997`, 50 iterations, 27K samples.

| Function | Self % | Category |
|---|---|---|
| step_node | 10.71% | Dispatch |
| FixWork::step_in_place | 7.77% | Tabling |
| ComposeWork::step | 5.20% | DiagonalJoin step |
| DiagonalJoin::pull_side | 4.83% | DiagonalJoin step |
| **DiagonalJoin::new** | **4.74%** | **take_self dummy creation** |
| drop_in_place\<Node\> | 4.66% | Drop (includes dummy Box\<Node::Fail\>) |
| Table::answer_at | 4.13% | Tabling |
| malloc | 2.99% | Allocation |
| drop_in_place\<Work\> | 1.83% | Drop |
| SipHash write | 1.68% | Hashing |
| cfree | 1.45% | Deallocation |
| drop_in_place\<HashSet\<NF\>\> | 1.40% | Drop |
| drop_in_place\<Vec\<NF\>\> | 1.32% | Drop |
| ChrState::clone | 0.68% | Clone |

**DiagonalJoin-related overhead (direct):** ComposeWork::step (5.20%) + pull_side (4.83%) + new (4.74%) = **14.77%**.

Of this, `DiagonalJoin::new` at **4.74% is pure waste** — it does nothing useful, just creates the dummy replacement.

### Allocation Profile

Current allocation profile for `recursive_even_backward_first64` (64 answers):

| Size Range | Alloc Count | Bytes | What |
|---|---|---|---|
| 129-256 B | 443,716 | 103 MB | Box\<Node\> (232 bytes) |
| 257-512 B | 222,588 | 62 MB | Box\<Work\> (280 bytes) |
| 0-16 B | 77,354 | 0.9 MB | Small allocs |
| Others | 8,012 | 13 MB | Various |
| **TOTAL** | **751,670** | **179 MB** | |

### Critical Correlation

222K ComposeWork/MeetWork steps × 2 dummy `Box<Node::Fail>` = **444K** predicted dummy node allocations.

Observed Box\<Node\> allocations: **443,716**.

**Nearly 100% of all Box\<Node\> allocations are dummy `Box<Node::Fail>` from take_self().** The real search tree creates almost no Box\<Node\> allocations (< 1K).

Combined take_self waste:
- 443K Box\<Node::Fail\> allocations: 103 MB
- 222K Box\<Work\> allocations: 62 MB
- **Total: 665K allocations, 165 MB — 88% of all allocations and 92% of all bytes**

## Proposed Fix: In-Place Stepping for DiagonalJoin

The same approach that yielded ~20% improvement for FixWork:

### 1. Add `DiagonalStepResult` enum

```rust
pub(crate) enum DiagonalStepResult<C: ConstraintOps> {
    Emit(NF<C>),  // Answer produced; DiagonalJoin updated in-place
    More,          // No answer yet; DiagonalJoin updated in-place
    Done,          // Exhausted
}
```

### 2. Add `step_in_place` to DiagonalJoin

Convert `step()` to mutate in-place and return the simple result type. The current step already does all mutations in-place — only the final `take_self() + Box::new(wrap(...))` needs to be removed:

```rust
pub(crate) fn step_in_place(&mut self, terms: &mut TermStore) -> DiagonalStepResult<C> {
    if let Some(nf) = self.pop_pending() {
        return DiagonalStepResult::Emit(nf);
    }
    // ... same logic, same mutations, no take_self, no Box::new ...
}
```

### 3. Add fast-paths in `step_node`

```rust
Node::Work(mut work) => {
    if let Work::Fix(ref mut fix) = *work {
        // existing fast-path
    }
    if let Work::Compose(ref mut compose) = *work {
        return match compose.core.step_in_place(terms) {
            DiagonalStepResult::Emit(nf) => NodeStep::Emit(nf, Node::Work(work)),
            DiagonalStepResult::More => NodeStep::Continue(Node::Work(work)),
            DiagonalStepResult::Done => NodeStep::Continue(Node::Fail),
        };
    }
    if let Work::Meet(ref mut meet) = *work {
        return match meet.core.step_in_place(terms) {
            DiagonalStepResult::Emit(nf) => NodeStep::Emit(nf, Node::Work(work)),
            DiagonalStepResult::More => NodeStep::Continue(Node::Work(work)),
            DiagonalStepResult::Done => NodeStep::Continue(Node::Fail),
        };
    }
    // ... fallback for remaining variants
}
```

### Why this works

- **No data structure size changes**: DiagonalJoin, ComposeWork, MeetWork, Work, Node all remain unchanged
- **No API changes**: Existing `step()` still works for all paths; the fast-path is purely internal to `step_node`
- **Zero overhead for non-Compose/Meet variants**: Single `if let` discriminant check
- **Eliminates 665K alloc+free cycles**: The existing `Box<Work>` is reused via `mut work` ownership transfer
- **Eliminates all dummy DiagonalJoin creation**: No more DiagonalJoin::new in the hot loop

### Risk assessment

**Low risk.** The fix is purely mechanical:
1. All mutations already happen via `&mut self` — the stepping logic is unchanged
2. The `take_self` pattern exists solely for `WorkStep`'s ownership requirements
3. The same pattern was successfully applied to FixWork without issues

## Measured Impact

### Allocation reduction

| Metric | Before | After | Change |
|---|---|---|---|
| Total allocs | 751K | 88K | **-88%** |
| Total bytes | 179 MB | 14 MB | **-92%** |
| Box\<Node\> allocs (129-256B) | 443K | 1.4K | **-99.7%** |
| Box\<Work\> allocs (257-512B) | 222K | 1.4K | **-99.4%** |

### Wall-time reduction

| Benchmark | Before | After | Change |
|---|---|---|---|
| recursive_even_backward_first64 | ~46ms | ~32ms | **-31%** |
| recursive_even_backward_first10 | ~610µs | ~510µs | -16% |
| recursive_add_forward_n24 | ~2.0ms | ~1.3ms | -35% |
| recursive_add_backward_n24 | ~5.0ms | ~2.9ms | -42% |
| identity_atom | ~7.6µs | ~8.1µs | neutral |
| conjunction_selective | ~33.9µs | ~33.6µs | neutral |

The improvement exceeded predictions (31% vs estimated 10-15%), likely because eliminating the dummy allocations also eliminated significant `drop_in_place` overhead that was attributed to other categories in the profile.

**Cumulative speedup from original ~105ms: 3.28×** (105ms → 32ms across all optimizations).

## Relationship to Backlog Items

This fix covers:
- **Work Graph #10**: Object pool / free list for Box\<Work\> and Box\<Node\> — **superseded** by in-place stepping (eliminates the allocations entirely rather than pooling them)
- **Work Graph #2**: Arena-backed nodes — partially superseded for Box\<Node\> (99.7% of Box\<Node\> allocs eliminated)
- **Per-Step Cost Decomposition Target 5**: Arena allocation — partially superseded

Remaining allocation overhead:
- ~88K allocs, ~14MB — dominated by small allocations (0-16B, 77K), Vec/HashSet growth, and a few genuine Box\<Node\>/Box\<Work\> from PipeWork and Or construction
- Further allocation reduction would require arena/pool for the remaining ~1.4K genuine Box\<Node\>/Box\<Work\> and the small-alloc traffic

## Files Changed

- `src/work/diagonal.rs` — Added `DiagonalStepResult` enum, `step_in_place`, and `pull_side_in_place` methods
- `src/work/compose.rs` — Added `step_in_place` delegation method
- `src/work/meet.rs` — Added `step_in_place` delegation method
- `src/node.rs` — Added ComposeWork and MeetWork fast-paths in `step_node`
- `src/work/mod.rs` — Exported `DiagonalStepResult`

## Decision

**Implemented.** Low-risk, high-reward optimization:
1. Eliminated 88% of allocations (663K alloc+free cycles)
2. Removed 4.74% pure-waste profile entry (DiagonalJoin::new)
3. Used a pattern already proven on FixWork
4. Required no architectural changes
5. 31% wall-time improvement, cumulative 3.28× from baseline
