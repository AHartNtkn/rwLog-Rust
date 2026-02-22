# Investigation: Parallel Or-Branch Execution via Rayon (Major Proposal 6)

## Summary

Investigated parallelizing Or-branch stepping with Rayon. DISCARDED without implementation: fundamental architectural barriers make parallel Or infeasible without a major refactoring that would regress single-threaded performance.

**Verdict:** DISCARD (architectural incompatibility)

## Problem

treecalc_synth_flip dominates at 396ms (69.7% of corpus) with 1547 Or-spine walks and up to 5 siblings. Hypothesis: stepping independent Or branches in parallel via Rayon could yield wall-time reduction.

## Why It Failed (Architectural Barriers)

### Barrier 1: `&mut TermStore` API prevents shared access

The entire stepping pipeline — `step_node()`, `step_or()`, and all Work types — takes `&mut TermStore`. This exclusive reference exists because hot-path term operations use `_unlocked` methods (`get_unlocked()`, `intern_unlocked()`) that bypass the RwLock via `RwLock::get_mut()`. These were introduced because the locked path was measured as too slow.

Parallel branches would each need `&mut TermStore`, which is impossible. Changing 144 call sites across 24 files to `&TermStore` would eliminate the unlocked fast path, regressing single-threaded performance.

### Barrier 2: FastLock is a zero-cost fake mutex

`FastLock` wraps `UnsafeCell<T>` with `unsafe impl Sync` — explicitly designed for single-threaded use. All Table state uses FastLock. Replacing with `parking_lot::Mutex` adds overhead to every table access, and Or branches that share tables (common in treecalc's recursive calls) would contend on these locks.

### Barrier 3: Lock contention would likely negate gains

Even with `&TermStore`: TermStore's sharded hashcons maps use `RwLock` (parallel branches contend on every term lookup/creation), and tables are shared between recursive siblings (producer/consumer contention).

### Barrier 4: Search semantics

Parallel stepping changes the search strategy from deterministic rotation-based interleaving to race-condition-based ordering, making search order non-deterministic.

## What Would Be Required

1. Split TermStore into read-only `TermReader` and write-only `TermWriter` interfaces (~400-600 lines across 24 files)
2. Replace FastLock with real Mutex and accept overhead
3. Make `Node<C>` and `Work<C>` Send + Sync
4. Add Rayon and parallelize `step_or`

## Key Insight

The codebase was explicitly designed for single-threaded performance. Retrofitting parallelism at the Or level is an architectural change, not a targeted optimization. A more promising approach would be parallelism at the **Engine** level (multiple independent queries) rather than within a single query's search tree.

## Files Changed (none)

No code changes — investigation concluded at the architectural analysis stage.
