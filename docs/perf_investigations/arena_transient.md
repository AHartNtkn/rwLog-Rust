# Investigation: Per-Query Arena for Transient Compose Terms

## Summary

Investigated whether transient terms created during compose_nf matching could benefit from a scratch arena. DISCARD: instrumentation shows <0.1 terms created per compose attempt — 96% of failures create zero terms. The optimization target does not exist.

**No performance measurement needed** — the opportunity is below threshold.

## Problem

The hypothesis was that compose_nf matching creates many transient terms (via apply_subst, shift_term) that are immediately consumed and never survive to output. A lightweight scratch arena skipping hash-consing could reduce the ~9% interning overhead.

## Why It Failed

1. **96% of compose failures create zero terms.** Of 275,207 failures on treecalc_synth_flip, 264,422 created zero terms. The root functor precheck, var_range checks, and early matching failures exit before any term creation.

2. **Only 29,087 terms created across 277,985 compose attempts** — 0.1 terms per attempt. Even with infinitely fast allocation, savings would be negligible.

3. **Hash-consing is beneficial, not wasteful.** Terms created during matching may be reused across compose attempts. A scratch arena would lose this deduplication.

4. **The 9% interning overhead comes from engine stepping** (apply_subst in step_node, factor_tensor, collect_tensor) — not from compose_nf matching.

## Instrumentation Results

**treecalc_synth_flip:**
- 275,207 compose failures, 2,778 successes
- Total terms created: 29,087
- 96.1% of failures: zero terms
- Only 10,785 failures created any terms (avg 2.1 each)
- Success path: 5,972 terms (avg 2.1 per success)

**recursive_even_backward_first64:**
- 63 failures, 315 successes
- Total terms: 252 (all on success path)
- 100% of failures: zero terms

## Files changed

None — instrumentation only, no code changes merged.

## Remaining opportunities

- The precheck cascade (root functor → var_range → matching) is extremely effective — 96% zero-allocation failures
- Future compose allocation optimization should target the SUCCESS path (~2 terms per success) not the failure path
- The 9% interning overhead is dominated by apply_subst in engine stepping and factor_tensor, not compose_nf matching
- Per-query arena for engine-level apply_subst terms could still be investigated, but terms there may be long-lived
