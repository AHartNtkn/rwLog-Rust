# Investigation: Compiled Match Programs for NF Pattern Matching

## Summary

Attempted to replace generic term matching with pre-compiled opcode sequences per NF pattern. DISCARD: U=27/100 (borderline regression, ~1.2% slower on treecalc_synth_flip).

**Primary workload (treecalc_synth_flip, 5 iters):**
**Baseline:** 400046 us (median, all values: 401693, 393715, 400768, 400963, 399324, 405422, 396765, 398368, 396889, 404672)
**After:** 404904 us (median, all values: 397409, 405062, 406408, 405608, 404745, 404314, 398296, 394437, 410565, 406008)
**U statistic:** 27/100 (borderline regression)

## Problem

The compose_nf success path calls `match_term_lists_shifted` on every compose attempt (~64K times on treecalc_synth_flip). The generic matcher walks the term tree recursively, dispatching on term kind at each node. Hypothesis: a pre-compiled opcode sequence (CheckFunctor, BindVar, Descend, CheckEq) would eliminate per-node dispatch overhead.

## Why It Didn't Work

1. **Compilation overhead exceeds savings**: Pre-compiling match patterns into CompiledMatch opcodes adds cost at every NF creation (factor_tensor, factor_tensor_with_subst). Since NFs are created frequently, this overhead accumulates.

2. **Variable-at-structural-position bailouts**: The compiled matcher must fall back to the generic matcher when input terms have variables at structural positions (can't descend into a variable's children). On treecalc_synth_flip, many compose attempts involve such patterns, reducing the compiled path's hit rate.

3. **Memory overhead**: Each NfInner carries an Option<CompiledMatch> with a SmallVec of opcodes, increasing NF size and allocation pressure.

4. **Generic matcher already well-optimized**: Inline term encoding (bit checks), fast tag extraction (get_unlocked), and root functor prechecks make the generic matcher quite efficient. The opcode sequence replaces one cheap dispatch (match on Term variant) with another (match on MatchOp variant).

## Files Changed

None merged (DISCARD).

## Insights

- The generic matcher's per-node dispatch is not the bottleneck — the pointer-chasing through TermStore (hash table probing, term tree walks) dominates.
- Compiled match programs would need to also compile the TermStore access pattern (pre-resolve term references) to beat the generic matcher. This approaches JIT compilation territory.
- The existing compiled_dispatch (root functor + depth-2 at Or-spine level) captures most of the benefit of pattern compilation without the per-NF overhead.
- This closes the matching compilation design space for treecalc_synth_flip. Deeper patterns on wide_match_512 might benefit, but those are already handled by depth-2 dispatch.
