# Investigation: Apply Emit Chain Pre-seeding to MeetWork

## Summary

Investigated applying the shape_predict pre-seeding pattern to MeetWork. DISCARD: MeetWork is dead code in production — all conjunction goes through AndGroup/AndJoiner, not MeetWork/DiagonalJoin. Zero performance impact possible.

## Problem

shape_predict achieved 43.3% improvement by pre-seeding ComposeWork with leading Emit chain NFs at construction time. The hypothesis was that the same pattern would apply to MeetWork for And/Meet nodes.

## Why It Failed

1. **MeetWork::new() is only called in tests.** There are zero production call sites that construct MeetWork.

2. **All production And/Meet work goes through AndGroup** (`src/work/and_group.rs`), which uses AndJoiner (`src/join.rs`). AndJoiner is a completely separate implementation path using queue-based joins, not the DiagonalJoin that MeetWork wraps.

3. **rel_to_node handles Rel::And** by creating `Node::Work(Box::new(Work::AndGroup(AndGroup::new(nodes))))`, never `Work::Meet(MeetWork::new(...))`.

4. ComposeWork pre-seeding works because `ComposeWork::new_preseed()` is called from production pipe code (handle_call replay paths, wrap_compose_with_prefix_suffix). MeetWork has no equivalent production construction site.

## Files changed

None — no code changes needed.

## Remaining opportunities

- MeetWork itself may be a candidate for dead code removal (only used in tests)
- If pre-seeding the conjunction path is desired, it would need to target AndGroup/AndJoiner, not MeetWork
- AndJoiner uses a fundamentally different join mechanism (queue-based), so the DiagonalJoin Emit-chain pre-seeding pattern doesn't directly transfer
