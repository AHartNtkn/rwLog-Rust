# Investigation: Canonical Alpha-Renaming at Emission Boundary

## Summary

Investigated Dedup backlog item 3 — canonical alpha-renaming to improve duplicate collapse. DISCARD: NFs are already canonically alpha-renamed by construction. Zero opportunity.

## Analysis

All NF construction paths already produce canonical variable numbering:

1. **factor_tensor** (used by meet_nf, parser, NF::factor): `renumber_vars_list` renumbers LHS variables to 0..n-1 in order of first appearance. RHS variables ordered: shared vars in LHS order, then fresh vars consecutively.

2. **factor_tensor_with_subst** (used by compose_nf): Same canonical ordering via `renumber_vars_through_subst_list` and `build_factor_wiring`.

3. **NF::new** (direct construction): Used in work/mod.rs helpers and pipe.rs, all taking patterns from already-canonical NFs.

4. **dual_nf**: Calls collect_tensor then factor_tensor, re-canonicalizing.

The factor_tensor/factor_tensor_with_subst functions ARE the canonicalization step. Since TermIds are interned (same structure = same TermId), two alpha-equivalent NFs produced by factor_tensor have identical match_pats, build_pats, and drop_fresh, leading to identical hashes and equality.

## Files Changed

None (investigation only).

## Insights

- The factoring algorithm inherently produces canonical alpha-normal forms as a side effect of variable renumbering. This was built into the core design.
- This closes the design space for alpha-renaming optimizations: there is no opportunity.
- DiagonalJoin and Table dedup are already maximally effective given canonical NFs.
