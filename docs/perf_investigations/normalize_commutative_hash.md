# Investigation: Order-independent hash for normalize_owned cache

## Summary

Replaced the order-dependent multiplicative hash chain in normalize_owned's cache key with an order-independent (commutative) scheme using per-constraint hashing combined via wrapping_add.

**Baseline:** 306527us (median, all values: 317550, 300342, 298258, 300408, 310325, 308074, 310421, 304979, 296657, 312523)
**After:** 73368us (median, all values: 74844, 74319, 70350, 71336, 71743, 74685, 79466, 72844, 71168, 73892)
**Improvement:** ~76.1% (same-session comparison)
**Mann-Whitney U:** 100/100 (p < 0.0001, complete separation)
**Regression:** None observed on recursive_even_backward_first64 (U=70/100, neutral)

## Problem

The normalize_owned cache (R38, ~33.7% improvement) keyed by a 64-bit hash of the pre-normalization ChrState. The hash used a multiplicative chain that iterated alive constraints in inst Vec order:

```rust
let mut h = 0u64;
h = h.wrapping_mul(MUL).wrapping_add(d.store.alive_count as u64);
for inst in d.store.inst.iter() {
    if inst.alive {
        h = h.wrapping_mul(MUL).wrapping_add(inst.pred.0 as u64);
        for arg in d.store.args(inst) {
            h = h.wrapping_mul(MUL).wrapping_add(arg.raw() as u64);
        }
    }
}
```

This hash is **order-dependent**: two ChrStates with identical alive constraints at different positions in the inst Vec produce different hash values. This happens naturally after `combine_owned` with different operand orderings (e.g., the search tree's And fairness rotation produces combine(A,B) and combine(B,A)).

The result: semantically equivalent constraint states were treated as cache misses, forcing redundant CHR engine runs that cascaded into additional compose work.

## Solution

Replaced the order-dependent chain with a commutative combination scheme:

1. Each alive constraint is hashed individually (order-dependent within a single constraint — pred ID + args in order, which is correct since arg order matters).
2. Per-constraint hashes are combined via `wrapping_add` after bit-spreading with `wrapping_mul(MUL)`. Addition is commutative, making the hash independent of constraint ordering.
3. The combined constraints_hash is mixed into the final hash alongside alive_count, token info, and program_id.

### Key design decisions

1. **wrapping_add instead of XOR.** XOR has the problem that identical per-constraint hashes cancel to zero. wrapping_add doesn't suffer from this. Both are commutative and associative.

2. **Bit-spreading before combination.** Each per-constraint hash is multiplied by MUL before adding. This spreads bits and reduces collision probability for constraints with correlated hash values.

3. **No equality checking in cache.** The cache trusts the 64-bit hash as a key. With ~54K unique states, the collision probability is ~54K²/2^64 ≈ 10^-10, negligible regardless of hash scheme.

## Files changed

- `src/chr/mod.rs` — Replaced hash computation in normalize_owned (~20 lines changed)

## Why 76.1% instead of 2-5%

The estimated 2-5% assumed a modest increase in cache hit rate. In practice, the improvement was transformative:

1. **Steps dropped from 4978 to 2922 (41% reduction).** The search tree explored far fewer branches because cached normalization results prevented redundant work that was spawning additional search branches.

2. **Compose operations dropped from 277985 to 63775 (77% reduction).** Fewer unique constraint states meant fewer normalization runs, which meant fewer new NFs being generated, which meant fewer compose attempts in the diagonal join.

3. **Cascading effect.** The order-dependent hash wasn't just missing a few cache hits — it was missing the MAJORITY of equivalent states produced by different combine orderings. Each cache miss ran the full CHR engine, which produced intermediate states that themselves triggered more compose work. The cascading amplification turned a hash quality issue into a 4x slowdown.

4. **Meet operations also dropped from 241 to 164 (32% reduction).** Less search = fewer And joins.

## Remaining opportunities

- The cache still uses HashMap<u64, Box<dyn Any>>. A monomorphized cache (avoiding type erasure) or a direct-mapped cache could reduce per-lookup overhead.
- The hash computation still iterates all inst entries (including dead ones, checking the alive flag). Maintaining an incremental hash could avoid this iteration.
- With the dramatically reduced compose count (63K vs 278K), the profile distribution will shift significantly. Fresh profiling is needed to identify the new hotspots.
