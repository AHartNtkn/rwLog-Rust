# Investigation: Compiled Dispatch Tables for Multi-Rule Or Relations (Major Proposal 3)

## Summary

Implemented root-functor dispatch filtering for flat-Or-of-Atoms Call bodies. When resolving a Call whose body is a flat Or of Atoms, the optimization filters branches by root functor compatibility before composing, converting O(calls x rules) to O(calls x 1). hot_call_site_256 improved 216x.

**Baseline:** 68,382 us (median, all values: 68865, 68268, 69066, 66595, 68463, 67256, 67775, 68290, 68382, 69003)
**After:** 316 us (median, all values: 318, 315, 316, 268, 316, 282, 321, 321, 327, 262)
**Improvement:** ~99.5% (216x speedup)
**Mann-Whitney U:** 100/100 (p << 0.001, complete separation)
**Regression:** None observed on treecalc_synth_flip (U=54) or recursive_even_backward_first64 (U=38)

## Problem

hot_call_site_256 performs 256 calls to a 32-rule dispatch relation. Each call previously tried all 32 rules sequentially via Or-spine walking, producing 8,193 compose attempts. Only 1 of the 32 rules matches per call (each rule handles a distinct root functor). 97% of compose attempts were wasted.

## Solution

Extended `try_batch_advance_calls()` in PipeWork to handle flat-Or-of-Atoms Call bodies with root-functor dispatch:

1. `collect_flat_or_atoms()` — Flattens a Rel::Or tree into a Vec of Atom NFs
2. `try_dispatch_or_atoms()` — Core dispatch: reads the boundary NF's build/match pattern root functor, filters the Atom list to only compatible matches
3. `DispatchResult::Single(nf)` — exactly one match, absorb directly (like batch advance)
4. `DispatchResult::Filtered(rel)` — multiple matches, rebuild a filtered Or and fall through to normal stepping

### Key design decisions

1. **Runtime dispatch, not compile-time index**: Filters at call time rather than building a HashMap at parse time. This is simpler and avoids changing the Rel data structure. A pre-built index would be faster for very large rule sets but the current approach already reduces compose from 8K to 256.

2. **Handles Fix-wrapped bodies**: Many relations are `Rel::Fix(id, body)` — the dispatch unwraps Fix to find the inner Or.

3. **Integrates with batch advance**: When dispatch finds exactly one matching atom, it composes directly via `absorb_front`/`absorb_back`, just like the single-Atom fast path.

4. **Falls back gracefully**: If the body isn't a flat Or of Atoms, or if root functor can't be determined, falls through to the normal advance_call path with zero overhead.

## Files changed

- `src/term.rs` — Made `func_id_from_raw` `pub(crate)` (was private)
- `src/work/pipe.rs` — Added ~130 lines: root functor extraction, Or flattening, dispatch filtering, integration with batch advance

## Why 216x instead of 32x

The expected improvement was 32x (filtering 32 rules to 1). The actual 216x includes:
- Eliminating Or-spine walking overhead (17,380 steps → ~256 steps)
- Eliminating FixWork/Table/ComposeWork/DiagonalJoin creation per call
- Eliminating 97% of compose_nf calls
- The batch advance tight loop vs the full engine stepping loop

## Remaining opportunities (Major Proposal 3)

- **Pre-built dispatch index**: A HashMap<FuncId, Vec<NF>> compiled at parse time would make dispatch O(1) lookup instead of O(rules) scan per call. Matters for very large rule sets (512+ rules).
- **Discrimination trees**: For rules that share root functor but differ at depth 2+, a trie structure would further reduce candidates.
- **wide_match_512**: Should also benefit from this optimization — 512 rules sharing top functor `pair` but with distinct second-level constructors. Current dispatch filters by root functor only, so all 512 still match. Depth-2 discrimination would help.
