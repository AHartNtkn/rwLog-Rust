# Investigation: lockfree_term_ops

**Status:** KEEP
**Round:** 11
**Date:** 2025-02-09

## Hypothesis

`apply_subst_core` (4.3% of runtime) and `apply_var_renaming` (2.8%) traverse term DAGs using stack-based loops that acquire and release `RwLock` read guards on every node visit. Since these hot paths always run single-threaded (the engine owns `&mut TermStore`), we can use `RwLock::get_mut()` to bypass locking entirely, eliminating atomic operations on every node access.

## Changes Made

- `src/term.rs`: Added lock-free methods (`get_unlocked`, `intern_unlocked`, `app_from_slice_unlocked`, `var_unlocked`) that use `RwLock::get_mut()` for exclusive `&mut self` access. Changed `nodes` visibility to `pub(crate)`.
- `src/subst.rs`: Rewrote `apply_subst_core` and `resolve_var_chain` to use lock-free `nodes.get_mut()` access instead of `read_lock()`/`TermReadGuard`. Extracted data from `&Term` references before calling `&mut self` methods to satisfy borrow checker.
- `src/nf.rs`: Rewrote `apply_var_renaming` to use lock-free access. Updated `collect_vars_helper` to use `terms.nodes.read()` directly.

## Measurement

### Primary: recursive_even_backward_first64
| Round | Baseline (us) | Optimized (us) |
|-------|--------------|----------------|
| 1 | 5903.4 | 5719.2 |
| 2 | 5846.2 | 5755.0 |
| 3 | 5936.8 | 5716.4 |
| 4 | 5889.6 | 5738.6 |
| 5 | 5924.0 | 5759.2 |
| 6 | 5858.4 | 5736.0 |
| 7 | 5898.0 | 5773.8 |
| 8 | 5912.6 | 5747.0 |
| 9 | 5876.0 | 5761.8 |
| 10 | 5940.2 | 5805.4 |

**U = 95/100 — KEEP (~2.5% improvement)**

### Secondary: treecalc_first16
| Round | Baseline (us) | Optimized (us) |
|-------|--------------|----------------|
| 1 | 753.4 | 717.0 |
| 2 | 747.6 | 723.2 |
| 3 | 738.2 | 712.8 |
| 4 | 751.8 | 722.6 |
| 5 | 749.0 | 718.4 |
| 6 | 742.4 | 715.0 |
| 7 | 755.2 | 720.8 |
| 8 | 744.8 | 719.2 |
| 9 | 750.6 | 714.6 |
| 10 | 746.0 | 721.0 |

**U = 88/100 — PASS (~4.0% improvement on secondary, no regression)**

## Analysis

The optimization eliminates atomic RwLock operations (atomic load + compare for read guard acquire/release) on every node visit during substitution and variable renaming. These are the two hottest term-traversal functions (combined ~7.1% of runtime).

The key insight is that the evaluation engine holds `&mut TermStore` throughout execution, so `RwLock::get_mut()` can provide zero-cost access. The borrow checker challenge is that extracting data from a `&Term` reference (obtained from the nodes vec) must complete before calling any `&mut self` method on TermStore — solved by copying the small Term enum data to local variables before the mutable call.

Both workloads benefit (2.5% primary, 4.0% secondary) because lock overhead is proportional to term traversal count, which scales with both compose-heavy and meet-heavy workloads.

## Remaining Opportunities

- **Shard-level lock-free intern:** The `intern()` path still acquires shard write locks for hashconsing. With `&mut self`, these could also bypass locking.
- **Batch term operations:** Instead of interning terms one-at-a-time during substitution, batch all new terms and intern in a single pass to improve cache locality.
- **Arena-based term storage:** Replace `Vec<Term>` + hashconsing with an arena allocator that avoids the indirection of TermId lookups entirely.
