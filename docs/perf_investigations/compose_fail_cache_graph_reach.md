# Investigation: Compose Failure Cache for graph_reach_64

## Summary

Attempted a thread-local compose failure cache (hash-based) to skip known-failing compose pairs. DISCARDED: superseded by semi-naive fixpoint (tabling_semi_naive), and hash collisions cause unsound false positives.

**Against old baseline (pre-tabling):** ~32.9% improvement on graph_reach_64 (U=100/100), but 3.4% regression on treecalc_synth_flip (U=5/100).
**Against current baseline (post-tabling):** Irrelevant — graph_reach_64 already dropped from 190ms to 6.4ms via semi-naive.
**Verdict:** DISCARD

## Problem

graph_reach_64 performed 5.38M compose attempts with 2% success rate. The investigation attempted to cache failed compose pairs to skip known-incompatible NF combinations.

## Approach

- Thread-local `FxHashSet<u128>` keyed by `(left_nf_hash << 64) | right_nf_hash`
- Variable-identity fast path for `$x -> $x` NFs
- Arity pre-check before compose_nf

## Why It Failed

1. **Hash collisions cause false positives**: u64 NF hashes collide often enough that 4,034 out of 87,618 valid compose pairs (4.6%) were incorrectly cached as failures. While these happened to produce duplicate NFs in tested cases, this is NOT guaranteed — a hash-only failure cache is fundamentally unsound.

2. **Regression on treecalc_synth_flip**: 3.4% slower (U=5/100). The HashSet overhead on 275K entries (insert + lookup per compose attempt) exceeded savings.

3. **Superseded**: tabling_semi_naive reduced compose attempts from 5.38M to 131K at the source (semi-naive fixpoint), making the cache unnecessary.

## Key Insight

Hash-based failure caches are a heuristic — they approximate "this pair will fail" using indirect evidence (hash equality). The principled fix is to avoid generating redundant pairs in the first place (semi-naive evaluation). This validates the CLAUDE.md principle: "If you cannot prove that your solution is correct, you do not have a solution."

## Files Changed (not merged)

- `src/work/compose.rs` — thread-local failure cache
- `src/work/mod.rs` — re-export cache clear
- `src/engine.rs` — cache invalidation
