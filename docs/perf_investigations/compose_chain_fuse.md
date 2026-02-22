# Investigation: Compose Chain Fusion for Simple Wrapper NFs (Major Proposal 2 Remaining)

## Summary

Implemented chain fusion for simple wrapper NFs (`$x -> (f $x)`) in try_advance_call_at_end. Builds nested terms bottom-up in O(n) instead of O(n^2). DISCARDED: inline_amplification_256 improved 38% but is only 0.15% of total corpus time. U=59 on full corpus.

**Baseline:** ~643,020 us (full corpus mean)
**After:** ~642,029 us (full corpus mean)
**Mann-Whitney U:** 59/100 (not significant)
**Inline_amplification_256:** 958us → 591us (38.4% improvement)
**Verdict:** DISCARD (insufficient total impact)

## Problem

sequence_chain_len4096 (87ms, 14%) and inline_amplification_256 involve chains of simple compositions. The hypothesis was that detecting chains of `$x -> (f $x)` wrapper patterns and building the nested term bottom-up in one pass would break the O(depth^2) cost from individual compose_nf calls.

## Implementation

Added chain detection in `try_advance_call_at_end` (src/work/pipe.rs):

1. When consecutive front-end Calls resolve to simple wrapper NFs (single match/build pat, identity DropFresh, single-var match that appears exactly once in build), collect all wrapper FuncIds
2. Build the nested term bottom-up: `f_n(f_{n-1}(...f_1(boundary)...))` in O(n)
3. When boundary has single match/build pats, directly splice the wrapped term bypassing compose_nf entirely

## Why It Failed (Insufficient Impact)

1. **inline_amplification_256 is the ONLY case with simple-wrapper chains** — it's ~1ms out of ~640ms total (0.15% of corpus). The 38% improvement on this case moves the total by only 0.2%.

2. **sequence_chain_len4096 doesn't match the wrapper pattern** — its chains are ground-to-ground transformations, not `$x -> (f $x)` wrappers. The bottleneck for sequence_chain_len4096 is O(n^2) in `env.lookup` doing linear scan through 4096 bindings per call, not compose overhead.

3. **treecalc_synth_flip** (400ms, 63%) — nondeterministic CHR search, no chain pattern.

4. **left_rec_32** (71ms, 11%) — recursive tabled evaluation, no chain pattern.

## Key Insight

**sequence_chain_len4096's bottleneck is env.lookup, not compose.** Each call resolves to a single-Atom body via `try_batch_advance_calls`, but the env (environment/binding map) uses O(n) linear scan through accumulated bindings. With 4096 chained calls, this is O(n^2) total. A HashMap-based env would break this quadratic behavior.

## Bug Discovered

The initial implementation used `nf.drop_fresh.constraint != C::default()` to check for empty constraints. This always fails for ChrState because `ChrState::default()` allocates a fresh `program_id` each time, so equality never holds. Fixed by using `ConstraintOps::is_empty()` instead.

## Files Changed (not merged)

- `src/work/pipe.rs` — Added simple wrapper chain detection and bottom-up term building in try_advance_call_at_end

## Remaining Opportunities

- **env.lookup O(n^2) fix for sequence_chain_len4096**: Replace linear-scan env with HashMap or indexed lookup. This is the actual bottleneck, not compose chains.
- **Broader chain fusion**: Detecting non-wrapper chains (ground-to-ground, multi-variable) would require a more general approach but could help more cases.
