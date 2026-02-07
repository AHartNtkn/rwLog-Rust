# ChrState Hash/Eq: Empty Fast-Path + Frozen Cache

## Context

Follow-up to the Arc-wrapping investigation, which showed a ~21% improvement on
`recursive_even_backward_first64` but was reverted as too complex. That investigation
attributed the gain to hash/eq caching rather than O(1) clone.

This investigation tests two simpler ideas independently:
- **A**: Early return in `freeze_chr` when ChrState is empty (alive_count == 0 && builtins empty)
- **B**: Cache frozen bytes via `OnceLock<Vec<u8>>` on ChrState, invalidated by not cloning it

## Results

All timings are for `recursive_even_backward_first64` (4793 steps, 64 answers).
Each row is the median of 5 inner runs; 3 outer runs were taken per configuration.

| Configuration | Run 1 (ms) | Run 2 (ms) | Run 3 (ms) | vs Baseline |
|---------------|-----------|-----------|-----------|-------------|
| **Baseline**  | 99.7      | 108.0     | 107.8     | —           |
| **A only**    | 99.1      | 108.0     | 107.2     | ~0% (noise) |
| **A + B**     | 123.3     | 120.6     | —         | **+15-23% regression** |

## Analysis

### Optimization A: Empty fast-path — Neutral

The early return skips: Vec<AliveRec> allocation, sorting, remap allocation, token iteration,
and ByteWriter overhead. However, when `alive_count == 0`, the existing code already:
- Creates an empty `Vec<AliveRec>` (no heap alloc for empty vec)
- Sorts nothing
- Builds an empty remap (but this allocates `vec![u32::MAX; inst.len()]` — 0 elements when empty)
- Iterates zero tokens
- Produces `[0, 0, 0]` via ByteWriter

The fast-path avoids these zero-cost loops and produces the same 12-byte output directly.
The overhead saved is below measurement noise (~100µs over 4793 steps).

### Optimization B: Cached frozen bytes — Regression

Adding `OnceLock<Vec<u8>>` to ChrState increased struct size by 32 bytes (pointer + state + Vec).
The cache only helps when the *same* instance is hashed/compared multiple times. In practice:
- ChrState is cloned at every search branch (clone doesn't copy cache)
- Each cloned instance is hashed once for DashMap insertion, then compared 0-1 times
- The OnceLock initialization cost + Vec<u8> allocation on first access dominates

The 15-23% regression comes from:
1. Larger struct → slower clones (more bytes to memcpy)
2. OnceLock synchronization overhead on every `get_or_init`
3. The cached Vec<u8> itself allocates on the heap

## Conclusion

Neither optimization improves performance. The empty fast-path is kept as it's zero-cost
and logically correct (avoids unnecessary work). The cache is rejected — it actively hurts
because ChrState instances are short-lived and rarely hashed/compared more than once.

### What the Arc investigation actually measured

The Arc-wrapping investigation's 21% improvement was likely from **struct size reduction**
(Arc is one pointer vs the full ChrState), which made cloning cheaper. The "hash caching"
attribution was incorrect — caching doesn't help when instances are hashed once.

### Future directions

The bottleneck for `recursive_even_backward_first64` is not in hash/eq but in the
per-step cost of Or tree rotation and compose_nf operations (see `or_tree_and_per_step_cost.md`).
Reducing struct size (e.g., compacting ChrStore representation) would help more than caching.
