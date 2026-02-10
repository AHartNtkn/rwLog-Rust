# Investigation: Convert recursive exec_body_inline to iterative DFS with explicit worklist

## Summary

Attempted to convert recursive `exec_body_inline` + `try_inline_match` to iterative DFS with explicit frame stack and RVarEnv pooling. 10% regression — Vec-indexing indirection and pool bookkeeping outweigh stack frame savings.

**Baseline:** 839342us (median, all values: 838155, 837449, 840833, 839675, 842737, 839010, 837679, 846538, 842344, 838895)
**After:** 923622us (median, all values: 940925, 931831, 929287, 907404, 936372, 907416, 912883, 919518, 927727, 913484)
**Improvement:** -10.0% (regression)
**Mann-Whitney U:** 0/100 (complete separation, optimized always slower)
**Regression:** N/A (primary regressed)

## Problem

`exec_body_inline` at 14.24% of profile shows 8+ recursion levels in the call graph. Each recursion level allocates a new stack frame (~200+ bytes) and creates a new `RVarEnv` via `RVarEnv::new(program.max_rvars)`. The hypothesis was that converting to iterative DFS would eliminate function call overhead and allow RVarEnv reuse.

## Solution Attempted

Replaced recursive `exec_body_inline` + `try_inline_match` with an iterative version using:

1. **Explicit frame stack:** `Vec<Frame>` where each Frame tracks body instructions, instruction pointer, and indices into an env pool.
2. **RVarEnv pool with free list:** `Vec<RVarEnv>` as pool, `Vec<usize>` as free list. When a match succeeds and a new frame is pushed, the match_env becomes the child's env and a new match_env is acquired from the pool.
3. **`try_inline_match_iter`:** Variant that returns the matched rule's body reference instead of recursing, allowing the caller to push a new frame.
4. **Borrowed-env sentinel:** Special handling for the first frame's env (borrowed from caller) to avoid cloning.

## Why it failed

1. **Stack frame allocation is nearly free.** Modern CPUs handle stack pointer adjustment in a single cycle. The compiler optimizes register usage across the call boundary. The iterative version replaces this with Vec indexing (`env_pool[idx]`), which requires pointer dereference + bounds checking.

2. **RVarEnv::new() allocations are cheap.** With mimalloc as the global allocator, small Vec allocations go through the thread-local freelist, essentially O(1). The pool-based approach saves these allocations but adds free-list management overhead (Vec push/pop, index tracking) on every matched rule.

3. **Indirection cost dominates.** Every `collect_args` call in the iterative version indexes into `env_pool[]` with a data-dependent load on the critical path. The recursive version passes a direct `&RVarEnv` reference — no indirection.

4. **Lost compiler optimizations.** The recursive version allows the compiler to inline `try_inline_match` into `exec_body_inline` and optimize the entire call chain. The iterative version's dynamic indexing prevents similar optimizations.

5. **The 14.24% was actual work, not overhead.** The profiled time includes matching (`match_head_direct`), guard evaluation (`GuardProg::eval`), and term construction (`collect_args`), not just the recursion wrapper. Converting to iterative doesn't reduce this work.

## Files changed

- `src/chr/mod.rs` — Replaced recursive `exec_body_inline` + `try_inline_match` with iterative version using frame stack and RVarEnv pool.

## Remaining opportunities

- The 14.24% in exec_body_inline is dominated by actual CHR matching/guard/body work. Optimizing those individual operations (match_head_direct, collect_args, GuardProg::eval) would be more productive than changing the control flow.
- The deep recursion (8+ levels) suggests the CHR rules produce long chains of immediately-matching constraints. If the chain structure is predictable, a specialized "fast chain" mode that skips per-step matching overhead might help.
