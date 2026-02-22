# Investigation: HashMap Env — Reinvestigation with Targeted Benchmark

## Summary

Reinvestigation of env_hashmap with sequence_chain_len4096 as primary benchmark. KEEP: 6.3% improvement (U=100/100), no regressions.

**Baseline:** 84050.6 us (median, all values: 84211.9, 82286.8, 85243.7, 82117.1, 84575.8, 84537.7, 84499.9, 82341.3, 83889.2, 83641.8)
**After:** 78722.8 us (median, all values: 78668.2, 78303.1, 78008.7, 78516.7, 80482.1, 79212.0, 78777.4, 76565.4, 78784.1, 80511.9)
**Improvement:** ~6.3% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001)
**Regression:** None observed (treecalc_synth_flip U=54, recursive_even U=68)

## Problem

Env::lookup does linear scan: `self.bindings.iter().rev().find(|b| b.rel == id)`. For sequence_chain_len4096 with 4096 chained calls each adding a binding, lookup is O(n) per call giving O(n^2) total. The original investigation showed 3.4% improvement but was incorrectly discarded (U=38 full corpus).

## Solution

Replaced `Arc<Vec<Binding<C>>>` with `Arc<FxHashMap<RelId, Binding<C>>>`. Key improvement over original: used `Arc::make_mut` for copy-on-write bind semantics. During sequential env construction where `self` is the sole Arc owner, `make_mut` returns a mutable reference without cloning, making `bind()` O(1) amortized. Removed redundant `Binding::rel` field since RelId is now the map key.

### Key design decisions

1. **Pure FxHashMap, not hybrid** — A hybrid Vec/HashMap approach with `Option<FxHashMap>` in an `EnvInner` struct was tried first but the struct overhead regressed even when the Option was None. Pure FxHashMap is simpler and faster.
2. **Arc::make_mut for bind** — The critical fix vs the original investigation, which cloned the entire HashMap on every `bind()`. Arc::make_mut avoids cloning when refcount=1 (the common case during sequential construction).

## Files Changed

- `src/work/fix.rs` — Replaced Vec with FxHashMap in Env, removed Binding::rel field, used Arc::make_mut for bind

## Why 6.3% Instead of More

The 6.3% improvement on sequence_chain_len4096 (84ms → 79ms, ~5ms savings) reflects that env.lookup is only part of the workload. The majority of time is still spent in compose_nf operations (4096 composes). Further improvement would require reducing compose count (chain fusion at the Rel level).
