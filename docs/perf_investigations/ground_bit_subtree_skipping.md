# Ground-Bit Subtree Skipping in TermId

## Summary

Encode a ground-term flag in bit 31 of `TermId` to enable O(1) subtree skipping in `apply_subst` and `shift_vars`. Ground terms (containing no variables) are unaffected by substitutions or variable shifts, so entire subtrees can be skipped with a single bit test on a value already in a register.

**Result: ~9% speedup on program_synth_flip, no regression on tabling workloads.**

## Motivation

Post-CHR-optimization profiling of `program_synth_flip` showed:
- `apply_subst`: 15.05% of total time
- `shift_vars`: 5.57% of total time
- Combined: ~20.6% of execution time

Both functions walk entire term trees node-by-node, even through ground subtrees where no variable substitution or shifting can have any effect. Skipping ground subtrees is a principled optimization — if a subtree contains no variables, no substitution or shift can change it.

## Design

### Approach: TermId Bit Encoding

Encode the ground flag in bit 31 of the `TermId` u32:

```rust
const GROUND_BIT: u32 = 1 << 31;
const INDEX_MASK: u32 = !GROUND_BIT;

impl TermId {
    fn index(self) -> usize { (self.0 & INDEX_MASK) as usize }
    fn is_ground(self) -> bool { self.0 & GROUND_BIT != 0 }
}
```

This reserves 2^31 (~2 billion) term slots, which is more than sufficient.

### Why Bit Encoding

Two earlier approaches were tried and rejected:

1. **Separate `Vec<bool>` ground flags + per-node check**: Added a `ground: Vec<bool>` alongside `terms: Vec<Term>` under the same lock. Per-node checks in `apply_subst`/`shift_vars` Visit paths accessed `data.ground[id]` for each node. Result: 5% improvement on program_synth_flip but **+18.5% regression on tabling workloads** due to extra cache-line fetch per node.

2. **Separate `Vec<bool>` + top-level-only check**: Same Vec<bool> but only checked at the top level before entering the traversal loop. Result: marginal ~1-2% improvement (only helps when the entire term is ground, not for ground subtrees within non-ground terms). No regression.

The bit encoding solves both problems:
- **Zero extra memory access**: The ground flag is encoded in the TermId value already in a register. No additional cache line needed.
- **Per-node granularity**: Every node in the traversal can be checked, enabling subtree skipping at any depth.
- **Lock avoidance**: Ground subtrees skip the `read_lock()` acquisition entirely, since the check happens before the lock.

### Integration

Ground flag is computed at intern time from children's TermId ground bits:
```rust
let is_ground = match &term {
    Term::Var(_) => false,
    Term::App(_, children) => children.iter().all(|c| c.is_ground()),
};
```

All Vec indexing uses `id.index()` (strips ground bit) instead of `id.0 as usize`.

## Changes

- `src/term.rs`: Added `GROUND_BIT`/`INDEX_MASK` constants, `TermId::index()`/`is_ground()` methods. Removed separate `TermData` struct and `ground: Vec<bool>`. Updated `intern()` to set ground bit on returned TermId. Updated all indexing to use `id.index()`.
- `src/subst.rs`: Added top-level `term.is_ground()` check (zero cost, replaces `terms.read_lock().is_ground()`) and per-node `tid.is_ground()` skip in `apply_subst` Visit path.
- `src/kernel/util.rs`: Same pattern for `shift_vars`.

## Measurements

### program_synth_flip (interleaved A/B)

| Round | Optimized | Baseline | Δ |
|-------|-----------|----------|---|
| 1     | 4.61s     | 5.28s    | -12.7% |
| 2     | 4.76s     | 5.10s    | -6.7% |
| 3     | 5.01s     | 5.40s    | -7.2% |

Optimized median: 4.76s, Baseline median: 5.28s → **~9.9% improvement**

### recursive_even_backward_first64 (tabling regression check)

Criterion: [23.432 ms 23.676 ms 23.927 ms], change: [-3.35% -2.01% -0.77%]
No change in performance detected (within noise threshold).

## Rejected Alternatives

1. **Substitution composition in meet_nf**: Could reduce 4 `apply_subst_list` calls to 2 by pre-composing substitutions. Not attempted this session — orthogonal optimization.
2. **Subst::is_empty() semantic fast-path**: Investigated and determined unnecessary — `split_match_subst` already produces genuinely empty Vecs when there are no bindings.
