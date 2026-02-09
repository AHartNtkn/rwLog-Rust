# Investigation: Root Functor Precheck in compose_nf

## Summary

Added a root functor precheck at the top of compose_nf_impl that skips expensive matching work when the first build pattern of the left NF and the first match pattern of the right NF have incompatible root functors. ~3.2% improvement on treecalc_synth_flip.

**Baseline:** 2480025us (median, all values: 2475716, 2449779, 2502897, 2488001, 2536015, 2530482, 2484333, 2475686, 2407104, 2374856)
**After:** 2400593us (median, all values: 2369571, 2389408, 2468770, 2462652, 2400655, 2478559, 2414284, 2334884, 2360093, 2400532)
**Improvement:** ~3.2% (same-session comparison)
**Mann-Whitney U:** 84/100 (p < 0.01)
**Regression:** None observed on recursive_even_backward_first64 (U=80/100, slight improvement)

## Problem

In treecalc_synth_flip, 99.14% of compose_nf calls fail at `match_term_lists_shifted` (321K failures out of 324K attempts). Each failed compose still incurs the cost of `collect_tensor` (~3.4% of runtime) and `pre_create_shifted_vars` (~5.1%) before discovering the failure.

A prior investigation (compiled_match_prefilter) tried a top-constructor precheck but was discarded because it was measured only on recursive_even_backward_first64, where compose rarely fails (83% success rate) and the constructor vocabulary is small (s, z, cons). The prior approach also required `read_lock()` on TermStore for every call.

## Solution

Added a root functor precheck after the arity mismatch check in `compose_nf_impl`, before `collect_tensor`. The check compares the root functor of `a.build_pats[0]` with `b.match_pats[0]` using `get_unlocked()` (lock-free Vec index access via `&mut TermStore`).

```rust
if !a.build_pats.is_empty() {
    let a_root = match terms.get_unlocked(a.build_pats[0]) {
        Some(Term::App(f, _)) => Some(*f),
        _ => None,
    };
    let b_root = match terms.get_unlocked(b.match_pats[0]) {
        Some(Term::App(f, _)) => Some(*f),
        _ => None,
    };
    if let (Some(af), Some(bf)) = (a_root, b_root) {
        if af != bf { return None; }
    }
}
```

### Key design decisions

1. **Lock-free access via `get_unlocked`**: Instead of `read_lock()` (which adds atomic operation overhead), uses `get_unlocked()` which calls `RwLock::get_mut()`. This is lock-free because `compose_nf` takes `&mut TermStore`, guaranteeing exclusive access.

2. **On-the-fly extraction vs NF fields**: The brief suggested adding `first_build_functor` / `first_match_functor` fields to NfInner, but this would require updating 80+ `NF::new` call sites. On-the-fly extraction with `get_unlocked` is equally fast (one array index) and much simpler.

3. **First position only**: Only checks the first pattern position. Extending to all positions would catch more failures but adds a loop per compose attempt. The first-position check already catches a meaningful fraction of failures.

4. **Safe fallthrough**: When either side has a variable-rooted pattern (or empty patterns), the precheck is skipped and compose_nf proceeds normally. Variables can match anything, so no precheck is valid.

## Files changed

- `src/kernel/compose.rs` — Added root functor precheck after arity mismatch check, before collect_tensor

## Why 3.2% instead of 6.5%

The theoretical maximum was ~6.5% (the full cost of 321K failure-path executions). The actual improvement is lower because:

1. **Not all failures have incompatible root functors**: Many failed compose attempts have compatible root functors but fail deeper in the pattern (e.g., both start with the same functor but differ in child structure). These are not caught by the precheck.

2. **Variable-rooted patterns bypass precheck**: When either side starts with a variable, the precheck can't fire. In tree calculus synthesis, some patterns are variable-rooted.

3. **The failure path is already cheap**: After prior optimizations (ground-bit subtree skipping, virtual shift_vars), the per-failure cost is relatively low. The precheck saves the cost difference between a quick functor comparison and the full collect_tensor + pre_create_shifted + match path.

## Remaining opportunities

- Extend precheck to compare ALL pattern positions (not just the first) for multi-arity NFs
- Check arity of the root App node (number of children) as an additional filter
- Cache the root functor in the NF struct for patterns that are accessed very frequently (amortizes the Vec index lookup)
