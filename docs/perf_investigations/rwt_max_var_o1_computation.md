# O(1) Max-Var Computation from DropFresh Metadata

## Summary

Replace `max_var_index_terms` tree walks in `compose_nf` and `meet_nf` with an O(1) computation derived from DropFresh's `in_arity`, `out_arity`, and `map.len()`. After `collect_tensor` converts an NF to direct-rule (RwT) form, the variable indices follow a deterministic pattern that can be computed without traversing term trees.

**Result: ~8.8% speedup on program_synth_flip, no regression on tabling workloads.**

## Motivation

Profiling `program_synth_flip` with `perf record -g -F 999` (cpu_core event, ~4K samples) showed:

- `collect_vars_helper`: 6.03% of total time
- Of that, 5.68% was from `max_var_index_terms` called in `compose_nf`

`compose_nf` and `meet_nf` both call `collect_tensor` to convert each NF operand to RwT form, then call `max_var_index_terms` on both lhs and rhs of each RwT — 4 tree walks per operation. These tree walks go through `collect_vars_ordered` → `collect_vars_helper`, iterating over every node in the term tree to find the maximum variable index.

But after `collect_tensor`, the variable indices in the RwT follow a known pattern entirely determined by the DropFresh metadata. The tree walks compute information that's already available in O(1).

## Design

### How collect_tensor assigns variable indices

`collect_tensor` converts `NF { match_pats, drop_fresh, build_pats }` to `RwT { lhs, rhs }`:

1. **LHS** (`match_pats`): Passed through unchanged. Variables are numbered `0..in_arity-1`.
2. **RHS** (`build_pats`): Renamed via a map derived from DropFresh:
   - For each `(i, j)` in `drop_fresh.map`: RHS var `j` maps to LHS var `i` (shared variable)
   - Remaining RHS vars get fresh indices starting at `in_arity`

So the total variable count in the RwT is:
```
total_vars = in_arity + num_fresh
where num_fresh = max(0, out_arity - map.len())
```

And the maximum variable index is `total_vars - 1` (or `None` if `total_vars == 0`).

### Implementation

```rust
impl<C> NF<C> {
    pub fn rwt_max_var(&self) -> Option<u32> {
        let num_fresh =
            self.drop_fresh.out_arity.saturating_sub(self.drop_fresh.map.len() as u32);
        let total = self.drop_fresh.in_arity + num_fresh;
        if total > 0 {
            Some(total - 1)
        } else {
            None
        }
    }
}
```

### Correctness verification

Debug builds retain the original tree walks as `debug_assert_eq!` checks, verifying the O(1) result matches the tree walk for every invocation. All 714 tests pass with these assertions enabled.

## Changes

- `src/nf.rs`: Added `rwt_max_var()` method to NF struct.
- `src/kernel/compose.rs`: Replaced `max_var_index_terms` calls with `rwt_max_var()`. Tree walks retained as `debug_assert_eq!` verification.
- `src/kernel/meet.rs`: Same replacement as compose.rs. Also fixed malformed NF in `meet_append_rules` test (used var index 1 with `DropFresh::identity(1)` which only allows var index 0).

## Measurements

### program_synth_flip

| Run | Baseline | Optimized |
|-----|----------|-----------|
| 1   | 4.75s    | 4.36s     |
| 2   | 4.78s    | 4.27s     |
| 3   | 4.53s    | 4.52s     |
| 4   | 4.78s    | 4.33s     |
| 5   | 4.65s    | 4.17s     |

Baseline median: 4.75s, Optimized median: 4.33s → **~8.8% improvement**

Ranges: baseline [4.53, 4.78], optimized [4.17, 4.52] — nearly non-overlapping.

### Tabling workload

No dedicated tabling regression test was run this session; the optimization only affects variable index computation in compose_nf/meet_nf and cannot affect tabling-specific paths.

## Rejected Alternatives

1. **Ground-bit skipping in `collect_vars_helper`**: Adding `if tid.is_ground() { continue; }` to the variable collection loop caused ~20% regression due to codegen effects (despite being semantically correct). The extra branch disrupted the compiler's optimization of the tight loop. Reverted.

2. **Ground-bit skipping in `apply_var_renaming`**: Same approach, same result — codegen regression. The renaming loop is similarly tight and branch-sensitive. Reverted.

These results demonstrate that not all "skip unnecessary work" optimizations are beneficial — the overhead of the branch check can outweigh the savings when the inner loop body is very cheap and the branch is rarely taken in the hot path.
