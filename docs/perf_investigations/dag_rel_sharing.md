# Investigation: Arc-Based Structural Sharing for Rel Tree

## Summary

Investigated whether Rel tree cloning could be replaced with Arc-based structural sharing. DISCARD: already fully implemented — Rel<C> already wraps every recursive child in Arc. Cloning is already O(1).

**No performance measurement needed** — the optimization target does not exist.

## Problem

The hypothesis was that when Or branches are created, the Rel tree is deep-cloned for each branch, and wrapping Rel nodes in Arc would enable structural sharing.

## Why It Failed

1. **Rel<C> already uses Arc everywhere.** The enum wraps every recursive child: `Or(Arc<Rel<C>>, Arc<Rel<C>>)`, `And(Arc<Rel<C>>, Arc<Rel<C>>)`, `Seq(Arc<[Arc<Rel<C>>]>)`, `Fix(RelId, Arc<Rel<C>>)`, `Atom(Arc<NF<C>>)`.

2. **Cloning Rel is already O(1)** — it bumps Arc refcounts, no deep copy.

3. **PipeWork::split_or cloning** already shares all Rel tree structure through Arc pointers.

4. **The backlog item (Work Graph #1) is stale** — this optimization was implemented as part of the Arc-wrapping work that also covered NF and Node.

## Files changed

None — investigation only, no code changes.

## Remaining opportunities

- Rel structural sharing is fully addressed. The backlog item should be marked as implemented.
- The remaining Work Graph items (#3 store fragments by ID, #5 bytecode plans, #6 subplan cache) remain uninvestigated.
