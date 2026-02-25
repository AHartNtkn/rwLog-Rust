# Investigation: Subsumption-Based Tabling for left_rec_32 (Major Proposal 7 Remaining)

## Summary

Generalized inner call keys to match parent table keys, enabling inner calls to enter the existing ReplayOnly path instead of creating redundant sub-tables. 446x speedup on left_rec_32 (72ms to 0.16ms). Steps reduced from 185,088 to 336, compose attempts from 40,393 to 66.

**Full corpus U:** 100/100 (p < 0.0001)
**treecalc_synth_flip U:** 59/100 (neutral)
**recursive_even_backward_first64 U:** 77/100 (slight improvement)
**Verdict:** KEEP

## Problem

left_rec_32 creates 528 inner tables during evaluation. Each inner call has a slightly different call key (different output-side boundary) but semantically subsumes the parent table's key. Each inner table independently rediscovers answers that the parent table already has, leading to O(n^2) redundant compose work.

The semi-naive investigation (left_rec_semi_naive.md) identified this 528-table cascade as the core problem but concluded it was "semantically required." Subsumption tabling proves that inner calls with subsuming keys can safely share their parent's table.

## Solution

Added `try_generalize_key` method to PipeWork. When a new call is about to create a table:

1. Check if any ancestor FixWork has a table for the same relation
2. Compare the inner call's key with the parent's key
3. If they differ only in output-side boundaries (right boundary for front-advancing, left boundary for back-advancing), generalize the inner key to match the parent's key
4. The generalized key matches the existing table, so the inner call enters the ReplayOnly path — getting semi-naive delta answers for free

### Key design decisions

1. **Output-side-only boundary relaxation**: Only relax output-side boundaries (build patterns for front-advancing, match patterns for back-advancing). Input-side boundaries constrain what the relation accepts; relaxing them would cause compose explosion by accepting unrelated inputs. This guard prevents treecalc regression.

2. **Inline rel-ID check**: The rel-ID must match between inner and parent calls. Without this, unrelated calls to different relations could be incorrectly subsumed. This prevents recursive_even regression.

3. **Parent key lookup via ancestor walk**: Walk up the FixWork chain looking for matching relation IDs. This is O(depth) per call but depth is small (typically 1-3 levels for left_rec).

## Files changed

- `src/work/pipe.rs` — Added `try_generalize_key` method (+~50 lines) and subsumption check in `handle_call`

## Why 99.8% instead of 100%

The 0.2% remaining time is the 336 engine steps needed to process the 66 compose attempts that actually discover the 32 answers. This is the irreducible minimum work for producing the correct results.

## Remaining opportunities

- **Answer tries for duplicate detection**: Currently answers are stored in Vec and deduped via HashSet. An answer trie would provide O(1) insertion-time dedup and enable prefix sharing across similar answers.
- **SCC-based scheduling for mutual recursion**: The current tabling handles single-relation recursion. Mutual recursion (A calls B which calls A) would benefit from SCC detection and coordinated fixpoint scheduling.
