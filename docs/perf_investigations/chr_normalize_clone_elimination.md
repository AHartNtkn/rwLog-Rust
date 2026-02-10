# CHR Normalize/Combine Clone Elimination for ~10% Speedup

## Summary

Profiled the `program_synth_flip_query_emits_answer` workload (~5.5s baseline after CHR trigger indexing). Instrumented `ChrState::normalize` to measure call patterns: 259K calls, 98.8% failing (UNSAT), 0% early-exits. Every call cloned the ChrState before running the fixpoint loop, then discarded the clone on failure.

The root cause: `normalize(&self)` takes a reference and clones internally, but callers in `compose_nf` and `meet_nf` always pass owned temporaries that are immediately dropped. The clones are pure waste — the callers never use the original after calling normalize.

Implemented two ownership-based optimizations:
1. **`normalize_owned(self)`**: Takes ownership instead of cloning. For the 98.8% of calls that fail, the owned value is simply dropped — no clone needed. For the 1.2% that succeed, the owned value is modified in place and returned.
2. **`combine_owned(self, other)`**: Reuses `self`'s allocation instead of cloning when merging constraint stores.

**Result: ~10% improvement on program_synth_flip (5.50s → 4.94s median). No regression on tabling workloads (21.7ms, improved from 22.9ms baseline).**

## Instrumentation Data

Before optimization, added atomic counters to normalize:

```
=== normalize stats ===
  total calls:            259,088
  no_data (trivial):      0 (0.0%)
  pre-failed (no work):   0 (0.0%)
  fixpoint-failed:        256,077 (98.8%)
  succeeded:              3,011 (1.2%)
  total alive enqueued:   2,314,853
  total initial agenda:   2,314,853
  total agenda processed: 10,171,649
  rules fired:            6,309,033
  zero-fire successes:    2,470 (82.0% of succeeded)
  avg alive per call:     8.9
  avg initial agenda:     8.9
  avg items before fail:  40.7
```

Key observations:
- **0 early exits**: Every normalize call has constraint data and runs the full clone + fixpoint pipeline.
- **98.8% fail**: The constraint system (no_c theory) prunes most search branches. Each failing call clones the ChrState, runs the fixpoint until contradiction is detected, then discards the clone.
- **82% of successes are no-ops**: 2,470 of 3,011 successful normalizations fired zero rules — the fixpoint was already reached. The clone was unnecessary.
- **40.7 items processed before failure**: Failures aren't detected immediately; the fixpoint loop processes ~41 agenda items (including rule firings that expand constraints) before finding a contradiction.

## Optimization 1: normalize_owned

### Before

```rust
fn normalize(&self, terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
    // ...
    let mut st = self.clone();  // 259K clones, 98.8% immediately discarded
    // ... run fixpoint on st ...
    if !st.solve_to_fixpoint(terms) {
        return None;  // clone wasted
    }
    Some((st, subst_opt))
}
```

### After

```rust
fn normalize_owned(mut self, terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
    // No clone: modify self in place
    // ... run fixpoint on self ...
    if !self.solve_to_fixpoint(terms) {
        return None;  // self simply dropped, no clone cost
    }
    Some((self, subst_opt))
}

// Existing method delegates to owned version
fn normalize(&self, terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
    self.clone().normalize_owned(terms)
}
```

Added to `ConstraintOps` trait with default implementation delegating to `normalize(&self)`.

## Optimization 2: combine_owned

### Before

```rust
fn combine(&self, other: &Self) -> Option<Self> {
    // ...
    let mut merged = self.clone();  // clone self to build merged state
    // ... add other's constraints to merged ...
    Some(merged)
}
```

### After

```rust
fn combine_owned(mut self, other: Self) -> Option<Self> {
    // Reuse self's allocation instead of cloning
    let md = self.data.as_mut().unwrap();
    // ... add other's constraints to md ...
    Some(self)
}
```

## Call Site Changes

In `compose_nf` and `meet_nf`, the constraint operations chain on owned temporaries:

```rust
// Before: clone + clone + clone
let combined = a_constraint.combine(&b_constraint);   // clones
let (normalized, _) = combined.normalize(terms);       // clones

// After: reuse + reuse
let combined = a_constraint.combine_owned(b_constraint);  // reuses a's allocation
let (normalized, _) = combined.normalize_owned(terms);     // modifies in place
```

## Results

### program_synth_flip_query_emits_answer

| | Baseline (10 runs) | Optimized (10 runs) | Change |
|---|---|---|---|
| Min | 5.24s | 4.68s | -10.7% |
| Median | 5.50s | 4.94s | -10.2% |
| Max | 5.65s | 5.08s | -10.1% |

Ranges are non-overlapping (baseline min 5.24 > optimized max 5.08).

### recursive_even_backward_first64 (regression check)

```
time:   [21.599 ms 21.744 ms 21.897 ms]
change: [-7.0164% -5.0590% -3.1104%] (p = 0.00 < 0.05)
Performance has improved.
```

No regression; slight improvement from reduced code size / cleaner inlining.

## Profile: Before vs After

| Function | Before | After |
|---|---|---|
| `apply_subst` | 18.1% | 16.5% |
| `HashMap::get_inner` | 10.1% | 10.4% |
| `match_head` | 7.6% | 8.2% |
| `shift_vars` | 7.1% | 6.3% |
| `collect_vars_helper` | 6.2% | 5.4% |
| `normalize`/`normalize_owned` | 5.1% | 5.3% |
| `ChrStore::clone` | 3.8% | 4.2% |
| `SmallVec::clone` | 3.6% | 1.8% |
| `TermStore::intern` | 3.2% | 3.0% |
| `malloc` | 2.4% | 1.3% |
| `cfree` | 2.0% | 1.8% |

Notable: `SmallVec::clone` halved (3.6% → 1.8%) and `malloc` nearly halved (2.4% → 1.3%) due to eliminated allocations from ChrState cloning.

## Files Changed

- `src/constraint.rs`: Added `normalize_owned` and `combine_owned` to `ConstraintOps` trait with default implementations.
- `src/chr/mod.rs`: Implemented `normalize_owned` (in-place fixpoint) and `combine_owned` (allocation reuse) for `ChrState`. Changed `normalize` to delegate to `normalize_owned`.
- `src/kernel/compose.rs`: Changed `combine` → `combine_owned`, `normalize` → `normalize_owned`.
- `src/kernel/meet.rs`: Same changes as compose.

## Remaining Targets

The investigation revealed several further optimization opportunities for the program_synth_flip workload:

1. **Fast-fail contradiction detection**: 256K normalize calls fail after processing 40.7 agenda items on average. For the `no_c` theory, failure means a `c` constructor appears somewhere in a constraint argument. A quick pre-check scanning constraint terms for forbidden constructors could short-circuit the full fixpoint, potentially saving 15-20% of total runtime (most of match_head, CHR apply_subst, and fixpoint processing).

2. **Dirty-flag fixpoint skip**: 82% of successful normalizations fire zero rules. Tracking whether the constraint state has changed since last normalization could skip these no-op fixpoint runs. Impact is small (~0.2% of total time for 2,470 skipped calls).

3. **apply_subst** remains the largest single hotspot at 16.5%. This is fundamental substitution work spread across kernel compose (9%) and CHR normalization (5%). Reducing the number of substitution passes through the compose pipeline could help.

4. **shift_vars** at 6.3% is entirely from compose_nf variable renaming-apart. Integrating the offset into the matching step (virtual shift instead of physical shift) could eliminate this entirely.

5. **collect_vars_helper** at 5.4% — repeated variable collection across collect_tensor, max_var_index_terms, and factor_tensor. Caching variable metadata on NF structs could reduce this.

## PERFORMANCE_INVESTIGATIONS.md Updates

- **CHR #3**: "Add incremental constraint store deltas to avoid full rechecks after each introduce" — **Partially addressed** by normalize_owned/combine_owned. Full incremental CHR (only enqueuing newly-added constraints) remains uninvestigated.
- **CHR #7**: "Explore persistent constraint store snapshots to reduce clone costs across branches" — **Superseded** by ownership-based clone elimination. Persistent snapshots are no longer needed for the normalize path.
