# Investigation: Fuse Adjacent DropFresh Composition Chains

## Summary

Investigated whether DropFresh composition chains could be fused. DISCARD: the hypothesis was invalid — `DropFresh::compose()` is never called in production code. The compose/meet pipelines construct fresh DropFresh values from variable analysis instead of composing existing ones.

**No performance measurement needed** — the optimization target does not exist.

## Problem

The hypothesis was that compose_nf chains multiple DropFresh compositions (a.df ; intermediate_df ; b.df) and that fusing them into a single pass would eliminate intermediate allocations.

## Why It Failed

1. **DropFresh::compose is dead code in production.** All call sites are inside `#[cfg(test)]` in `src/drop_fresh.rs`. Zero production callers exist.

2. **compose_nf constructs fresh DropFresh values.** The compose pipeline matches a.build_pats against b.match_pats, applies substitutions, then calls `factor_tensor_with_subst()` which builds a brand new DropFresh from scratch via `build_factor_wiring()` — by analyzing variable flow in the final normalized LHS/RHS patterns.

3. **meet_nf uses the same pattern.** Both compose and meet pipelines construct DropFresh from final variable analysis, never by composing existing DropFresh maps.

4. **The backlog item "fuse adjacent DropFresh chains" has no foundation.** There are no chains to fuse because DropFresh composition is an algebraic operation that the kernel doesn't use — it constructs DropFresh values from the ground up.

## Files changed

None — investigation only, no code changes.

## Remaining opportunities

- DropFresh::compose could be removed as dead production code (it's only used in unit tests for DropFresh's algebraic properties)
- DropFresh backlog items #1 (packed bitsets), #2 (composition tables), #3 (canonical interner) are all moot since DropFresh is constructed fresh each time, not composed from existing values
- The only DropFresh optimization that would matter is speeding up `build_factor_wiring()` in factor_tensor_with_subst, which is already quite lightweight (SmallVec iteration over small maps)
