# Investigation: collect_apply_fuse

**Status:** KEEP
**Round:** 13
**Date:** 2025-02-09

## Hypothesis

`collect_vars_helper` (3.6% of runtime) and `apply_var_renaming` (3.0%) both traverse the same term tree. `renumber_vars()` calls them sequentially — two full traversals. A fused single-pass function that collects and renames variables in one traversal eliminates the second traversal entirely.

## Changes Made

- `src/nf.rs`: Rewrote `renumber_vars()` as a fused single-pass function using a `var_map: Vec<Option<u32>>` populated on-the-fly as variables are discovered. Added `renumber_vars_list()` for multi-term fusion. Updated `factor()` and `factor_tensor()` to use the fused versions.

## Measurement

### Primary: recursive_even_backward_first64
| Round | Baseline (us) | Optimized (us) |
|-------|--------------|----------------|
| 1 | 4956.3 | 4824.7 |
| 2 | 4955.2 | 4792.2 |
| 3 | 5009.1 | 4803.1 |
| 4 | 4923.7 | 4886.4 |
| 5 | 5159.6 | 4792.3 |
| 6 | 4905.0 | 4780.3 |
| 7 | 4893.2 | 4780.3 |
| 8 | 4896.7 | 4762.2 |
| 9 | 5103.5 | 4929.1 |
| 10 | 4973.3 | 4774.2 |

**U = 82/100 — KEEP (~3.3% improvement)**

### Secondary: treecalc_first16
U = 65/100 — PASS (~2.0% improvement, no regression)

## Analysis

The fused single-pass avoids the second tree traversal entirely. As variables are encountered for the first time during the DFS, they get assigned the next sequential index in `var_map`. Subsequent occurrences reuse the assigned index. The renamed term is built as part of the same traversal using the BuildApp pattern from apply_var_renaming.

The improvement is slightly below the theoretical 3.0% (half of the 6.6% combined) because collect_vars_helper was already efficient (bitset for vars <64, ground-bit skipping) and some of its work can't be eliminated (the variable ordering discovery is inherent to the traversal).

## Remaining Opportunities

- **Fuse collect_vars into collect_tensor:** The `collect_tensor` function also calls `collect_vars_ordered_list` then `apply_var_renaming`. A fused version was implemented for `factor_tensor` but there may be additional call sites.
- **Eliminate renumber_vars where possible:** Some callers may not need the full renumber — just need to know the variable count or mapping, without producing a renamed term.
