# Investigation: Indexed Meet Pairs at DiagonalJoin Level

## Summary

Investigated Conjunction/Meet backlog item 4 — root-functor indexing at MeetStrategy's DiagonalJoin level to avoid generating incompatible meet pairs. DISCARD: U=66 on join_high_overlap, U=63 on join_low_overlap (not significant).

**Primary workload (join_high_overlap_64x64, 200 iters):**
**Baseline:** 592.6 us (median, all values: 593.883, 595.618, 592.287, 594.464, 581.201, 592.592, 568.354, 593.813, 587.988, 593.352)
**After:** 591.3 us (median, all values: 590.969, 589.600, 591.518, 590.254, 592.494, 568.513, 590.109, 593.256, 593.504, 592.072)
**U statistic:** 66/100 (not significant)

## Problem

The meet_fuse_reinv investigation added a root functor precheck inside meet_nf achieving 35% improvement. But all O(N×M) meet pairs are still generated before filtering. Hypothesis: indexing at the DiagonalJoin level (like indexed_diagonal_join for compose) could avoid generating incompatible pairs entirely.

## Why It Didn't Work

The existing `meet_root_functor_mismatch` precheck inside meet_nf is essentially free — it compares inline TermId values and returns `None` immediately. The cost of:
1. Computing and storing `(RootTag, RootTag)` per NF
2. Checking `tags_compatible()` twice per candidate pair in the loop

...is roughly equal to or greater than the cost of just calling meet_nf and having it bail out on the first line. Unlike compose (where the early rejection path has more overhead from substitution setup), meet's root functor precheck is already at absolute minimum cost.

## Measurements

- join_high_overlap: 4096 pairs, 50% compatible (2048 skipped by indexing) — U=66
- join_low_overlap: 4096 pairs, 98.4% incompatible (only 64 compatible) — U=63 despite massive pair reduction

## Files Changed

None merged (DISCARD).

## Insights

- This optimization path is dead. The meet_nf precheck is already at minimum possible rejection cost.
- Further meet improvements should focus on the successful meet path (e.g., 32 successes in high_overlap), not the failures which are already essentially free.
- The compose indexing (indexed_diagonal_join, 1.37% improvement) worked because compose_nf's rejection path is more expensive (substitution setup). Meet's simpler rejection path provides no room for call-avoidance savings.
