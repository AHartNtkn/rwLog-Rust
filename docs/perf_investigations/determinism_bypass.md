# Investigation: Determinism Bypass — Skip Tabling for Single-Rule Relations (Major Proposal 2)

## Summary

Attempted to bypass Fix/Table machinery for `Rel::Fix(_, Rel::Atom(nf))` Call bodies. DISCARDED: the optimization never fires because `env.lookup()` returns unwrapped bodies (the Fix is stripped at bind time). The existing `Rel::Atom(nf)` batch advance path already handles this case. Adding the dead branch caused a marginal treecalc_synth_flip regression (U=27).

**Primary (inline_amplification_256):** U=83, ~1.5% — but the improvement is noise since the new code path never executes.
**Regression (treecalc_synth_flip):** U=27 (significant regression from dead branch in hot path).
**Verdict:** DISCARD

## Problem

inline_amplification_256 (948us) calls 256 trivially-deterministic relations. Each is `rel stepN { $x -> (sN $x) }` — single rule, no recursion. The hypothesis was that these go through full Fix/Table machinery unnecessarily.

## Why It Failed

The hypothesis was wrong about what `env.lookup()` returns:
1. The parser creates `Fix(id, body)` for `rel name { ... }` definitions
2. `repl.rs::build_env()` unwraps the Fix: `if let Rel::Fix(id, body) = rel { env.bind(*id, body.clone()) }`
3. `advance_fix()` in pipe.rs also calls `env.bind(id, body)` with the unwrapped body

So `env.lookup(id)` always returns the **unwrapped** body, never a Fix-wrapped body. The existing `Rel::Atom(nf)` check in `try_advance_call_at_end()` already handles single-rule relations correctly. The batch advance path is already optimal for this case.

## Key Insight

The 948us overhead in inline_amplification_256 comes from the 256 compose operations themselves (each wrapping the term in a new constructor), not from Fix/Table dispatch. The batch advance already eliminates the dispatch overhead. To improve further, the focus should be on reducing per-compose cost or batching multiple composes into a single operation (e.g., recognizing chains of identity-like compositions).

## Files Changed (not merged)

- `src/work/pipe.rs` — Added 13-line Fix(_, Atom) check in try_advance_call_at_end (never fires)

## Remaining Opportunities for Major Proposal 2

- **Compile-time determinism detection**: Rather than runtime checks at call sites, analyze relation definitions at parse time. Mark relations as deterministic/non-recursive and use this to select specialized execution strategies (e.g., skip tabling entirely for provably-terminating deterministic relations).
- **Compose chain fusion**: For chains like `@a ; step0 ; step1 ; ... ; step255`, recognize that each step wraps in a new constructor and fuse the chain into a single operation that builds the nested term directly.
