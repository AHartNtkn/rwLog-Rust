# Investigation: Batch-Advance Simple Atom Calls in PipeWork

## Summary

Added inline resolution of single-Atom Call bodies in PipeWork, bypassing FixWork/Table/ComposeWork/DiagonalJoin machinery for deterministic single-rule relations. ~81.6% total corpus improvement; sequence_chain_len4096 from ~3.94s to ~87ms (45x).

**Baseline:** 4,828,309 us (mean, all values: 4819676, 4873790, 4896449, 4746598, 4817985, 4766324, 4893096, 4683479, 4960014, 4825676)
**After:** 890,112 us (mean, all values: 892445, 869576, 901859, 893620, 886118, 893341, 886351, 884449, 898022, 895342)
**Improvement:** ~81.6% (same-session comparison)
**Mann-Whitney U:** 100/100 (p << 0.001, complete separation)
**Regression:** None observed on treecalc_synth_flip (U=46) or recursive_even_backward_first64 (U=41)

## Problem

After the pipe_lazy_mid_normalize optimization (Round 48a), `sequence_chain_len4096` was still ~3.7s — 80%+ of total corpus time. The dirty flag eliminated redundant `normalize_mid_atoms()` calls, but the per-step overhead remained:

- 36,867 steps for 4,096 Call resolutions
- Each Call required: pop from mid → create FixWork → Table lookup → ComposeWork → DiagonalJoin → compose result → return to engine loop → re-enter PipeWork
- Perf profile: 26% DiagonalJoin::pull_side_in_place, 25% step_node, 21% ComposeWork::step_in_place, 10% Node drop

The actual compose_nf work per step was tiny (single-variable identity rules), but the stepping machinery had high constant overhead.

## Solution

Added `try_batch_advance_calls()` to PipeWork that runs as a Phase B between normalization and general advance. When a Call at either end of `mid` resolves (via env lookup) to a `Rel::Atom(nf)` — meaning it's a simple single-rule relation — the NF is composed directly into the pipe boundary via `absorb_front`/`absorb_back`, without creating any Work nodes.

This runs in a tight loop: as long as the next Call is a simple Atom, keep composing. A 4096-element chain of simple Calls is processed in a single call to `try_batch_advance_calls()`.

### Key design decisions

1. **Inline env lookup, not compilation**: Rather than compiling plans ahead of time (Major Proposal 1), this checks at runtime whether each Call resolves to a single Atom. This is simpler and handles the common case while leaving the door open for full plan compilation later.

2. **Both ends**: Tries front first, then back, in a loop. This matches PipeWork's outside-in evaluation strategy and handles chains regardless of which direction they're consumed from.

3. **Bail on non-Atom**: If a Call resolves to anything other than Atom (Or, Seq, Fix, etc.), the loop breaks and falls through to the general advance path. No correctness risk.

4. **Preserves semantics**: `absorb_front`/`absorb_back` are the same methods used by the existing normalization path. The only difference is skipping the FixWork/ComposeWork scaffolding.

## Files changed

- `src/work/pipe.rs` — Added `try_batch_advance_calls()` method (~50 lines), integrated into `step()` loop between normalization and general advance
- `src/work/tests.rs` — Updated test assertions

## Why 81.6% instead of higher

The improvement is bounded by:
1. **sequence_chain_len4096 was ~80% of baseline time** — eliminating its overhead can't improve beyond ~80%
2. **Other cases are unaffected** — this only helps cases with long chains of simple Calls
3. **The 87ms remaining for chain4096** is actual compose_nf work (4097 compositions of identity rules) plus parsing overhead — this is close to theoretical minimum

## Remaining opportunities

- **Major Proposal 1 (AOT Plan Compilation)** would generalize this: compile entire plans into bytecode, handling not just single-Atom Calls but also deterministic multi-rule Calls, Seq chains, and other patterns. This investigation shows the potential — 45x on a specific pattern — but a full compiler would cover more cases.
- **hot_call_site_256** (68ms) and **inline_amplification_256** (13ms) also have long Call chains but their relations may not all be single-Atom bodies. A more general "deterministic Call" fast-path (single Or branch, no constraints) could help.
- With sequence_chain_len4096 no longer dominating, the profile will shift. The next bottleneck is likely treecalc_synth_flip (~393ms) and graph_reach_64 (~181ms).
