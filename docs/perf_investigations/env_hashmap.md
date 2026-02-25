# Investigation: HashMap-Based Env for O(1) Binding Lookup

## Summary

Replaced Env's linear-scan Vec with FxHashMap for O(1) lookup. DISCARDED: HashMap overhead at small N (1-3 bindings for most cases) offsets gains on deep-chain cases. sequence_chain_len4096 improved 3.4% but regressions elsewhere gave U=38 on full corpus.

**Baseline:** ~634,209 us (full corpus median)
**After:** ~639,914 us (full corpus median)
**Mann-Whitney U:** 38/100 (not significant, slightly worse)
**Verdict:** DISCARD

## Problem

Env::lookup does linear scan: `self.bindings.iter().rev().find(|b| b.rel == id)`. For sequence_chain_len4096 with 4096 chained calls, each adding a binding, lookup is O(n) per call giving O(n^2) total. Discovered by compose_chain_fuse investigation.

## Implementation

Replaced `Arc<Vec<Binding<C>>>` with `Arc<FxHashMap<RelId, Binding<C>>>`. Lookup becomes O(1) HashMap get. Bind clones the map and inserts (still O(n) clone but O(1) insert). Removed redundant `Binding::rel` field since RelId is now the map key.

## Why It Failed

1. **Most environments have 1-3 bindings.** At this size, Vec linear scan is faster than HashMap lookup + hashing. FxHashMap adds ~0.9% overhead across the corpus from hash computation, bucket management, and cache pressure.

2. **sequence_chain_len4096 improved ~3.4%** (83ms → 80ms), confirming the O(n) lookup was a real cost for deep chains. But this ~3ms gain is swamped by HashMap overhead on all other cases.

3. **The real bottleneck for sequence_chain is compose, not lookup.** With 4096 compose operations and only 3 engine steps, the bulk of time is in compose_nf, not env lookups. The batch_advance_calls fast path already handles call resolution efficiently.

## Key Insight

Env lookup is O(n^2) in theory for deep chains, but in practice: (a) most environments are tiny (1-3 bindings), making Vec faster, and (b) even for sequence_chain_len4096, lookup is only ~3ms of the 83ms total — compose dominates. A hybrid Vec/HashMap approach could help but would save only ~3ms (0.5% of total corpus), making it low priority.

## Raw Timings (Full Corpus)

| Round | Baseline (us) | Optimized (us) |
|-------|--------------|----------------|
| 1 | 635,393 | 640,556 |
| 2 | 639,578 | 639,914 |
| 3 | 639,232 | 640,545 |
| 4 | 622,216 | 624,665 |
| 5 | 629,076 | 626,341 |
| 6 | 647,870 | 640,429 |
| 7 | 628,065 | 632,151 |
| 8 | 634,209 | 640,624 |
| 9 | 617,565 | 623,151 |
| 10 | 617,231 | 627,601 |

## Files Changed (not merged)

- `src/work/fix.rs` — Replaced Vec with FxHashMap in Env, removed Binding::rel field
