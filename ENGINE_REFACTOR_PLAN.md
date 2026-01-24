# Engine Simplification Plan

Task list (check off as completed). This plan is deletion-first and does not allow parallel implementations.

## Phase 0: Ground Rules
- [ ] Confirm refactor invariants: no semantic changes, no parallel implementations, deletion-first.
- [ ] Gate all new changes behind existing feature flags only when already used (no new flags unless required).

## Phase 1: Consolidate Shared Utilities
- [ ] Create a single module for term/NF utilities (var collection, renaming, substitution over lists).
- [ ] Move all duplicate helpers into the new module and update every caller.
- [ ] Delete the old duplicate helpers in the same change set.
- [ ] Add focused tests only if utility behavior changes or coverage gaps are found.

## Phase 2: Single Join Engine
- [ ] Design a generic JoinWork for binary joins with a pluggable combine function.
- [ ] Replace ComposeWork with JoinWork (ordered composition).
- [ ] Replace MeetWork with JoinWork (commutative meet).
- [ ] Replace AndGroup/AndJoiner with JoinWork composition or a single multi-input joiner built on the same core.
- [ ] Delete ComposeWork/MeetWork/AndGroup/AndJoiner/JoinReceiverWork immediately once replaced.
- [ ] Update node/work stepping and blocked handling for the unified join path.

## Phase 3: Normalize Rel Once Upfront
- [ ] Add a Rel normalization pass (flatten And/Seq where safe, fuse adjacent Atom).
- [ ] Route rel_to_node through the normalization pass.
- [ ] Re-establish a runtime normalization invariant for PipeWork mid:
      - [ ] Fuse adjacent Atom factors when new factors are inserted (Or split / Fix / Call expansion).
      - [ ] Restore a minimal, localized adjacency scan for mid (no full normalization pass).
- [ ] Remove only the normalization logic that is proven redundant after the invariant holds.

## Phase 4: Scheduler and Blocking Simplification
- [ ] Introduce a single in-process scheduler for pending/blocked tasks.
- [ ] Replace queue/waker usage in join and table flows with the scheduler.
- [ ] Keep queue/waker only if strictly required for existing semantics; otherwise delete.

## Phase 5: Tabling Isolation
- [ ] Move Table/Tables/FixWork into a dedicated module.
- [ ] Share the same answer-buffer/dedup logic with the join engine.
- [ ] Remove redundant answer/pending/dedup implementations.

## Phase 6: Debug/Tracing Hygiene
- [ ] Gate engine/compose/table debug counters and eprintlns behind the tracing feature.
- [ ] Remove unconditional panics in hot paths; replace with debug-only asserts when appropriate.

## Phase 9: Test Semantics Alignment
- [ ] Add test guidance for semantic focus and proper placement in AGENTS.md.
- [ ] Fix list-matching helper to allow overlap after prior matches while enforcing disjointness upfront.
- [ ] Update meet tests to avoid var-id coupling in constraint assertions and align naming with matching.
- [ ] Clarify that "form" means internal representation coupling (not formatting), and keep formatting tests only for public output contracts.
- [ ] Move or rewrite tests that assert internal structure instead of behavior.
- [ ] Relocate table/repl-facing tests to their proper modules.
  - [ ] Drop pipework/fixwork structural tests and add engine-level semantic coverage.
  - [ ] Move table/tables tests into tabling module.
  - [ ] Add additional proptests for semantic laws (canonicalization/meet/identity).
- [ ] Enforce matching-only semantics in code/comments/tests (rename unification references to matching).
  - [ ] Remove engine size/layout tests; refocus REPL tests on semantic counts over output format.
  - [ ] Remove format/size/construction-only tests in parser/rel/metrics; keep CLI formatting tests where output format is part of the interface.
