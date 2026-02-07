# Per-Step Cost Decomposition (Beyond ChrState)

**Status:** Completed
**Date:** 2026-02-07
**Workload:** `recursive_even_backward_first64` (105ms, 4793 steps, 64 answers)
**Profiling:** `perf record -g --call-graph dwarf` with frame pointers, 50 iterations, 22k samples

## Motivation

Prior investigations identified ChrState clone/hash/eq as ~45% of execution time
(or_tree_and_per_step_cost.md). However, attempts to optimize ChrState directly
(Arc-wrapping, caching frozen bytes) yielded limited results. This investigation
aims to decompose the *full* per-step cost to identify the true root causes and
whether ChrState overhead is a symptom of a deeper structural issue.

## Key Finding: ChrState Is a Symptom, Not the Root Cause

**89.8% of ChrState cloning originates from `FixWork::clone`.** The real problem
is that `FixWork::step()` calls `self.clone()` on every step, and FixWork
contains a `CallKey<C>` which deep-copies `Option<NF<C>>` boundaries — triggering
the full NF → DropFresh → ChrState clone cascade.

The prior investigation attributed 45% to "ChrState overhead" but that was
measuring a symptom. The root cause is the FixWork clone-per-step pattern.

## Full Cost Breakdown (Self-Time, Leaf Functions)

### Categorized Breakdown

| Category    | Self-Time | Key Functions                                         |
|-------------|-----------|-------------------------------------------------------|
| Tabling     | 26.4%     | answer_at, step_producer, FixWork clone, Mutex ops    |
| libc        | 17.4%     | Internal malloc/free, mmap, other libc                |
| Dispatch    | 14.4%     | Work::step (10.4%), step_node (4.0%)                  |
| Clone       | 13.7%     | ChrState (7.4%), DropFresh (3.3%), SmallVec (3.0%)    |
| Drop        | 10.1%     | Work (3.6%), ChrState (2.5%), Node (2.2%), others     |
| DiagonalJoin| 5.4%      | new (2.7%), pull_side (2.7%)                          |
| Alloc       | 4.4%      | malloc (2.6%), cfree (1.3%), exchange_malloc, realloc |
| Kernel      | 2.4%      | collect_vars, apply_subst, compose_pair, intern, etc. |
| Hash        | 1.4%      | SipHasher, DropFresh hash, hash_one                   |
| Other       | 4.4%      | HashMap, Engine::next, unknown                        |

### The Revelation

**Actual kernel computation (compose, match, substitute) is only 2.4% of
total time.** The remaining 97.6% is infrastructure overhead: cloning,
dropping, dispatch, memory allocation, tabling bookkeeping.

## Detailed Analysis

### 1. Tabling Machinery (26.4% self-time)

The dominant cost center. Breakdown:

| Function                        | Self-Time | What It Does                           |
|---------------------------------|-----------|----------------------------------------|
| Table::answer_at                | 8.2%      | Mutex lock + NF clone from answer Vec  |
| step_table_producer             | 6.7%      | Producer step orchestration            |
| FixWork::clone                  | 3.9%      | Deep clone of CallKey → NF → ChrState |
| Table::set_producer_node        | 3.6%      | Mutex lock + Node move                 |
| Table::set_producer_task_active | 2.5%      | Mutex lock + bool set                  |
| CallKey::clone                  | 1.1%      | NF deep clone for boundary constraints |

**Root cause**: `FixWork::step()` clones self on every step (lines 487, 498, 506, 512):
```rust
WorkStep::Emit(nf, Box::new(Work::Fix(self.clone())))
WorkStep::More(Box::new(Work::Fix(self.clone())))
```

FixWork contains:
- `key: CallKey<C>` — contains `Option<NF<C>>` for left/right boundaries → **deep clone**
- `table: Arc<Table<C>>` — O(1) Arc clone
- `answer_index: usize` — trivial
- `tables: Tables<C>` — O(1) Arc clone

The clone cascade: FixWork → CallKey → NF → SmallVec + DropFresh → ChrState

### 2. Clone Cascade (13.7% self-time)

Nearly all cloning traces back to FixWork::clone:

| Clone Target  | Self-Time | Via FixWork | Via answer_at | Other |
|---------------|-----------|-------------|---------------|-------|
| ChrState      | 7.4%      | 89.8%       | 0.5%          | 9.7%  |
| DropFresh     | 3.3%      | ~90%        | ~1%           | ~9%   |
| SmallVec      | 3.0%      | ~80%        | ~5%           | ~15%  |

### 3. Dispatch Overhead (14.4% self-time)

- `Work::step`: 10.4% — The enum match dispatch. Some of this is inlined callee
  work being attributed to the dispatch site, but the enum is large (Work has 8
  variants, each with substantial data) which causes poor cache locality.
- `step_node`: 4.0% — Node enum dispatch (4 variants).

### 4. Drop Overhead (10.1% self-time)

Every clone creates owned data that must be dropped. Dropping mirrors cloning:

| Drop Target          | Self-Time |
|----------------------|-----------|
| Work                 | 3.6%      |
| ChrState             | 2.5%      |
| Node                 | 2.2%      |
| HashSet<NF>          | 1.0%      |
| Vec<NF>              | 0.5%      |
| CallKey              | 0.4%      |
| VecDeque<NF>         | 0.4%      |

### 5. DiagonalJoin (5.4% self-time)

ComposeWork uses DiagonalJoin to coordinate left/right stepping. DiagonalJoin
uses `take_self()` (std::mem::replace with empty) on every step — this is a move,
not a clone, so it's cheaper. But the struct is large (contains seen_l, seen_r,
pending queues, HashSets) so the move still has cost.

### 6. Allocation (4.4% self-time, plus 17.4% in libc)

Every `WorkStep::More(Box::new(Work::Fix(self.clone())))` allocates a Box.
With ~4793 steps, many involving multiple Work variants, that's thousands of
heap allocations per query. The 17.4% in libc includes internal malloc/free
bookkeeping triggered by these allocations.

### 7. Table::answer_at Deep Dive

```rust
pub fn answer_at(&self, index: usize) -> Option<NF<C>> {
    self.answers.lock().answers.get(index).cloned()
}
```

At 8.2% self-time, this is expensive because:
1. parking_lot Mutex lock/unlock on every call
2. NF::clone inlined into the function body (95% of self-time is inlined clone work)
3. Called up to 2× per FixWork step (lines 485 and 504)

## Inclusive Time (Top Functions)

For context, here is where time flows through the call tree:

| Function               | Inclusive | What This Means                                    |
|------------------------|-----------|---------------------------------------------------|
| Work::step             | 94.7%     | Nearly all time flows through work dispatch        |
| step_node              | 94.6%     | Nearly all time flows through node dispatch        |
| DiagonalJoin::pull_side| 87.1%     | Compose coordination is the main execution path    |
| step_table_producer    | 73.3%     | 73% of time is inside tabled producer stepping     |
| FixWork::clone         | 20.1%     | 20% of time in FixWork clone cascade               |
| CallKey::clone         | 15.2%     | 15% of time in CallKey clone cascade               |
| DropFresh::clone       | 10.6%     | 10.6% of time in DropFresh clone cascade           |
| ChrState::clone        | 7.4%      | Bottom of the clone cascade                        |
| Table::answer_at       | 8.3%      | Answer NF cloning                                  |
| compose_nf             | 2.6%      | Actual kernel computation                          |

## Optimization Targets (Ranked by Expected ROI)

### Target 1: Arc-wrap CallKey in FixWork (~15-20% reduction)

Change `key: CallKey<C>` to `key: Arc<CallKey<C>>` in FixWork. This makes
FixWork::clone O(1) for the key field instead of deep-copying two NFs.

**Affected costs:**
- FixWork clone: 3.9% → near-zero
- CallKey clone: 1.1% → near-zero
- ChrState clone: 7.4% × 89.8% = 6.6% → near-zero
- DropFresh clone: 3.3% × ~90% = 3.0% → near-zero
- SmallVec clone: 3.0% × ~80% = 2.4% → near-zero
- Proportional drop reduction: ~5%
- **Total estimated savings: ~22%**

**Risk:** Low. CallKey is never mutated after construction. Arc is semantically
correct here.

### Target 2: Arc-wrap NFs in Table answer store (~5-8% reduction)

Store answers as `Vec<Arc<NF<C>>>` instead of `Vec<NF<C>>`. Then answer_at
returns Arc clone (O(1)) instead of deep NF clone.

**Affected costs:**
- Table::answer_at: 8.2% → near-zero for clone portion
- Estimated savings: ~6%

**Risk:** Low. Answers are immutable once inserted. Downstream consumers would
need to accept `Arc<NF<C>>` or deref.

### Target 3: Replace Mutex with RefCell for single-threaded (~3-6% reduction)

Table uses parking_lot::Mutex but execution is single-threaded. The Mutex
lock/unlock overhead appears in set_producer_node (3.6%), set_producer_task_active
(2.5%), and answer_at (part of 8.2%).

**Affected costs:**
- Mutex acquisition in 5+ methods: ~6% total
- Estimated savings: ~3-5%

**Risk:** Medium. Would need a compile-time or runtime flag to choose between
Mutex (for future parallel) and RefCell (for current single-threaded). Or
accept single-threaded-only for now.

### Target 4: Reduce Work::step dispatch overhead (~3-5% reduction)

Work is a large 8-variant enum. The match dispatch + data movement has poor
cache locality. Options:
- Use vtable-based dispatch (trait object) instead of enum
- Reduce enum size by boxing less-common variants
- Profile branch prediction to see if variant ordering matters

**Risk:** Medium-High. Architectural change with uncertain payoff since
some of the 10.4% may be inlined callee work.

### Target 5: Arena allocation for Work/Node (~3-5% reduction)

Replace per-step Box::new(Work::...) and Box::new(Node::...) with arena
allocation. A per-query bump allocator would amortize allocation overhead.

**Affected costs:**
- malloc: 2.6%, cfree: 1.3%, exchange_malloc: 0.2%
- Part of libc 17.4%
- Estimated savings: ~3-5%

**Risk:** Medium. Requires lifetime management for the arena.

## Relationship to Backlog Items

| Backlog Item                                    | Relevance | Est. ROI |
|-------------------------------------------------|-----------|----------|
| Work Graph #2: Arena-backed nodes               | High      | 3-5%     |
| Term Repr #3: Per-query temp arena              | Medium    | 2-3%     |
| DropFresh #4: Identity fast-paths               | Low       | <1%      |
| NF/Kernel #10: Unary specialization             | Low       | <1%      |
| NF/Kernel #4: Cheap syntactic rejection         | Low       | <1%      |
| Matching #2: Constructor-indexed dispatch       | Low       | <1%      |
| Tabling #3: Answer-trie indexes                 | Medium    | 2-3%     |
| Constraint/CHR #7: ChrState clone optimization  | **Superseded** | —   |

**Constraint/CHR #7 is superseded**: The ChrState overhead is a symptom of
FixWork::clone, not an independent cost center. Optimizing ChrState clone
directly (as attempted in prior investigations) attacks the wrong level.
Arc-wrapping CallKey in FixWork eliminates 89.8% of ChrState cloning without
touching ChrState at all.

## Conclusion

The critical workload spends **97.6% of time on infrastructure** and only
**2.4% on actual computation**. The dominant infrastructure cost is the
tabling machinery's clone-per-step pattern in FixWork, which triggers a
cascade through CallKey → NF → DropFresh → ChrState.

**The single highest-ROI optimization is Arc-wrapping CallKey in FixWork**,
which would eliminate ~22% of total execution time with minimal risk. Combined
with Arc-wrapping table answers (~6%) and removing unnecessary Mutex overhead
(~3-5%), a total improvement of ~30% is achievable with straightforward changes.

The prior investigation's conclusion — that ChrState is the dominant cost
center at 45% — was measuring the aggregate clone/hash/drop cascade rather
than the root cause. ChrState is at the bottom of the cascade but is not
the originating trigger. The trigger is FixWork::step's self-clone pattern.
