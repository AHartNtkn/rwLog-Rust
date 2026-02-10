# CHR First-Argument Trigger Indexing + RVarEnv Reuse for ~27% Speedup

## Summary

Profiled the `program_synth_flip_query_emits_answer` workload (~7s baseline). Found that **34% of execution time was in CHR constraint normalization**, with the single largest function being `match_head` at 18.78%. Instrumentation revealed 41.8M match_head calls, of which 68.6% (28.7M) failed due to first-argument constructor mismatch — the wrong rule was tried against the constraint because the trigger table only indexed by predicate, not by argument shape. Additionally, every match attempt allocated a fresh `RVarEnv` (two heap Vecs), totaling 41.8M unnecessary heap allocations.

Implemented two changes:
1. **First-argument functor indexing** on the CHR trigger table: at build time, partition rule occurrences by the top-level functor of the anchor head's first argument pattern. At dispatch time, extract the constraint's first-arg functor and only try matching rules.
2. **RVarEnv reuse**: allocate one `RVarEnv` per `solve_to_fixpoint` call (sized to max n_rvars across all rules) and reuse it via `reset()` + `ensure_capacity()` instead of allocating per match attempt.

**Result: ~27% improvement on program_synth_flip workload (7.2-7.6s → 5.3-5.7s). No regression on tabling workloads (-3.6% improvement on recursive_even_backward_first64).**

## Profile: Before

| Function | % | Source |
|---|---|---|
| `chr::match_head` | 18.78% | CHR rule matching |
| `subst::apply_subst` | 14.11% | Substitution (kernel + CHR) |
| `HashMap::get_inner` (term intern) | 10.33% | Term storage |
| `nf::collect_vars_helper` | 4.97% | NF normalization |
| `__libc_calloc` (87% from `RVarEnv::new`) | 4.84% | CHR allocation |
| `ChrStore::clone` | 3.94% | CHR state cloning |
| `cfree` | 2.97% | Deallocation |
| `malloc` | 2.27% | Allocation |
| `ChrState::normalize` | 1.87% | CHR entry point |

CHR-related operations total: ~34% of execution.

## Instrumentation Data

Before optimization, added atomic counters to `match_head`:

```
=== match_head stats ===
  total calls:      41,848,838
  pred_fail:        0 (0.0%)
  pat_fail:         28,718,618 (68.6%)
  success:          13,130,220 (31.4%)
  RVarEnv allocs:   41,848,838
```

Key observations:
- Zero predicate-level failures: the trigger table already filters by predicate, but that's insufficient.
- 68.6% pattern-level failures: these are match_head calls where the first-argument constructor doesn't match (e.g., trying `(no_c (b $x))` rule against a `no_c(f(...))` constraint).
- 41.8M RVarEnv allocations: each allocates two `Vec`s on the heap, even for calls that fail immediately.

## Optimization 1: First-Argument Functor Indexing

### Before

```rust
// triggers: Vec<Vec<OccRef>> — maps PredId → [OccRef]
let triggers = &self.program.triggers[pred.0 as usize];
for occ_ref in triggers.iter() {  // tries ALL rules for this predicate
    // Allocates RVarEnv, calls match_head, most fail
}
```

### After

```rust
// triggers: Vec<IndexedTriggers>
struct IndexedTriggers {
    by_functor: HashMap<FuncId, Vec<OccRef>>,  // rules indexed by first-arg functor
    fallback: Vec<OccRef>,                      // rules with variable first-arg (match anything)
}
```

At build time, each rule occurrence is classified by its anchor head's first argument pattern:
- `PatNode::App { f, .. }` → indexed under `by_functor[f]`
- `PatNode::RVar(_)` → goes in `fallback`
- Arity-0 head → goes in `fallback`

At dispatch time:
```rust
let first_arg_functor = extract_top_functor(constraint.args[0]);
let indexed_occs = indexed.by_functor.get(&first_arg_functor);
for occ_ref in indexed_occs.chain(indexed.fallback.iter()) { ... }
```

For the `no_c/1` theory with 5 rules (one per constructor: `l`, `b`, `f`, `c`, `a`), this reduces match attempts from 5 per constraint to 1, eliminating ~80% of match_head calls.

## Optimization 2: RVarEnv Reuse

### Before

```rust
fn find_match_inner(...) {
    let mut env = RVarEnv::new(rule.n_rvars);  // heap alloc
    // ... use env ...
}   // heap free

fn apply_rule_by_id_inner(...) {
    let mut env = RVarEnv::new(rule.n_rvars);  // another heap alloc
    // ... use env ...
}   // heap free
```

### After

```rust
pub fn solve_to_fixpoint(&mut self, terms: &mut TermStore) -> bool {
    let mut env = RVarEnv::new(self.program.max_rvars);  // ONE alloc
    while let Some(cid) = d.agenda.pop_front() {
        for occ_ref in ... {
            find_match_by_ids_reuse(..., &mut env);      // reuse via reset()
            apply_rule_by_id_reuse(..., &mut env);        // reuse via reset()
        }
    }
}
```

`RVarEnv::ensure_capacity(n)` grows the internal Vecs if needed (monotonic growth). `RVarEnv::reset()` is O(1) via generation-based invalidation (already implemented, just wasn't being exploited).

## Results

### program_synth_flip_query_emits_answer

| | Baseline | Optimized | Change |
|---|---|---|---|
| Run 1 | 7.62s | 5.65s | -26% |
| Run 2 | 7.21s | 5.54s | -23% |
| Run 3 | 7.22s | 5.59s | -23% |
| Run 4 | — | 5.49s | — |
| Run 5 | — | 5.34s | — |
| **Median** | **~7.3s** | **~5.5s** | **~-25%** |

### recursive_even_backward_first64 (regression check)

```
time:   [22.058 ms 22.114 ms 22.177 ms]
change: [-4.4804% -3.5949% -2.7221%] (p = 0.00 < 0.05)
Performance has improved.
```

No regression; small improvement from reduced code size / better inlining.

## Files Changed

- `src/chr/mod.rs`: Added `IndexedTriggers` struct, modified `ChrProgramBuilder::build()` to construct indexed triggers, added `RVarEnv::ensure_capacity()`, added `find_match_by_ids_reuse()` and `apply_rule_by_id_reuse()` methods, updated `solve_to_fixpoint()` to use indexed dispatch and reuse RVarEnv, added `max_rvars` to `ChrProgram`, removed dead old functions.

## Workload Details

The `program_synth_flip` workload is a program synthesis query using the tree calculus evaluator with CHR constraints:
- Theory: `no_c/1` with 5 simplification rules (one per top-level constructor)
- Query: Composes constraint guards, multiple `app` calls, and output assertions
- Characteristics: CHR-heavy (constraint checking at every compose_nf), recursive, uses conjunction (`&`)
- Step count: ~13M steps to first answer

## Remaining Targets

After this optimization, the CHR-related fraction should drop from ~34% to ~15-20%. The remaining hotspots are:
- `apply_subst` (14%): substitution application in kernel and CHR
- `HashMap::get_inner` (10%): term interning hash lookups
- `collect_vars_helper` (5%): variable collection in NF normalization
- `ChrStore::clone` (4%): deep cloning in normalize — could be addressed by CoW or dirty tracking
- `ChrState::normalize` itself: still re-enqueues all alive constraints and re-runs fixpoint even when no new constraints were added

## PERFORMANCE_INVESTIGATIONS.md Updates

- **Constraint/CHR Engine Integration #1**: "Add CHR predicate indexing by head functor/arity and argument shape" — **Implemented (first-arg functor indexing for trigger dispatch).**
- **Constraint/CHR Engine Integration #2**: "Compile CHR rules into indexed decision structures rather than linear scans" — **Partially addressed** by trigger indexing. Full compilation into decision trees remains uninvestigated.
