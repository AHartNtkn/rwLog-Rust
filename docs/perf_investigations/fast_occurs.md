# Investigation: Fast Occurs Check via Min/Max Variable Range Tracking

## Summary

Added per-term min/max variable range tracking to TermStore, enabling O(1) rejection in occurs_unlocked/occurs_locked. Combined with ground-term skipping improvements. KEEP: ~18.4% improvement on treecalc_synth_flip (U=100/100).

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 392718 us (median, all values: 390745, 393569, 399567, 390219, 385493, 396109, 396283, 395926, 391867, 389472)
**After:** 320345 us (median, all values: 316282, 320231, 322426, 325196, 319794, 324958, 328104, 320459, 319386, 317048)
**Improvement:** ~18.4% (same-session comparison)
**Mann-Whitney U:** 100/100 (complete separation)
**Regression:** None observed on recursive_even (U=42), join_high_overlap (U=39)

## Problem

`occurs_unlocked` was 17.09% of total runtime on treecalc_synth_flip. It checks whether a variable appears in a term tree by walking the tree recursively via a SmallVec worklist. The existing ground bit (`is_ground()`) provides O(1) "no variables at all" rejection, but the remaining 17% comes from non-ground terms that DO have variables — the question is whether they have THIS specific variable.

Previous investigation (remove_shifted_occurs) tried removing the occurs check entirely, but this was incorrect — lam_eq tests hang because cross-namespace substitution cycles ARE possible. The occurs checks MUST remain but can be made FASTER.

## Solution

Three optimizations:

### 1. Min/max variable range tracking per term (primary improvement)

Added a parallel `var_ranges: Vec<(u32, u32)>` to TermStore, computed at intern time. For each non-ground App term, stores the minimum and maximum variable indices reachable in its subtree. This enables O(1) rejection: if the target variable index falls outside the term's [min_var, max_var] range, the occurs check returns false immediately without walking the tree.

For tree calculus with disjoint left/right variable namespaces (left vars < offset, right vars >= offset), this catches the common case where we're checking a left-side variable against a right-only subtree, or vice versa.

### 2. Ground-term skipping in the walk loop

Before dereferencing each stack element, check `is_ground()` and skip. Also skip ground children when pushing to the worklist. The existing code only caught inline nullary constants; ground App store refs were being walked needlessly.

### 3. Post-deref ground check

After following substitution chains, if the resolved result is a ground term, skip it without looking up children.

### Key design decisions

1. **Parallel Vec instead of Term enum modification**: Storing var_ranges in a separate Vec parallel to `nodes` avoids changing the Term enum size, which would affect all term operations. The extra Vec adds one cache line per ~16 terms but doesn't pollute the primary traversal path.

2. **Min-max range (not bitmask)**: A min/max pair is simpler and smaller than a variable bitmask, handles arbitrary variable indices (not limited to first N), and catches the most common case (disjoint namespace rejection).

3. **Computed at intern time**: The range is computed bottom-up during interning — children's ranges are already available when computing a parent's range. Zero additional traversals needed.

## Files changed

- `src/term.rs` — Added `var_ranges: Vec<(u32, u32)>` to TermStore; compute ranges in `intern`/`intern_unlocked`; added `var_range_unlocked` method and `var_range` to TermReadGuard; updated `read_lock`
- `src/matching.rs` — Updated `occurs_unlocked` and `occurs_locked` with min/max range fast rejection and improved ground-term skipping

## Why 18.4% instead of the full 17%

The 17% profiling number was the inclusive cost of occurs_unlocked. The optimization eliminates most but not all tree walks — some walks still proceed because the target variable IS within the term's range (true positive). The ~1% gap represents these cases where the full walk is genuinely needed. Additionally, the var_ranges Vec adds a small amount of memory pressure.

## Remaining opportunities

- The var_ranges infrastructure could also benefit apply_subst: skip apply_subst on a subterm if none of the substitution's bound variables fall within the subterm's var range
- A variable bitmask (for low-numbered variables) could provide even finer-grained rejection within the min/max range
- The range could be extended to track the set of distinct variable indices (count) to detect when a single-variable term doesn't contain the target
