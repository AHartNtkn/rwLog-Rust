use crate::term::{Term, TermId, TermStore};
use smallvec::SmallVec;

/// A substitution maps variable indices to terms.
/// Uses Vec<Option<TermId>> for dense local variables (0..n).
/// None means the variable is unbound (maps to itself).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Subst {
    bindings: Vec<Option<TermId>>,
}

impl Subst {
    /// Create an empty substitution.
    pub fn new() -> Self {
        Self {
            bindings: Vec::new(),
        }
    }

    /// Bind a variable to a term.
    /// Extends the substitution if needed.
    pub fn bind(&mut self, var: u32, term: TermId) {
        let idx = var as usize;
        if idx >= self.bindings.len() {
            self.bindings.resize(idx + 1, None);
        }
        self.bindings[idx] = Some(term);
    }

    /// Get the binding for a variable, if any.
    pub fn get(&self, var: u32) -> Option<TermId> {
        let idx = var as usize;
        if idx < self.bindings.len() {
            self.bindings[idx]
        } else {
            None
        }
    }

    /// Check if a variable is bound.
    #[cfg(test)]
    pub fn is_bound(&self, var: u32) -> bool {
        self.get(var).is_some()
    }

    /// Check if the substitution is empty (no bindings).
    pub fn is_empty(&self) -> bool {
        self.bindings.iter().all(|b| b.is_none())
    }

    /// Number of bound variables.
    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.bindings.iter().filter(|b| b.is_some()).count()
    }

    /// Iterator over (var_index, term_id) pairs for bound variables.
    pub fn iter(&self) -> impl Iterator<Item = (u32, TermId)> + '_ {
        self.bindings
            .iter()
            .enumerate()
            .filter_map(|(i, opt)| opt.map(|tid| (i as u32, tid)))
    }

    /// Compute the range of variable indices that have bindings: (min_bound, max_bound).
    /// Returns None if no variables are bound.
    #[inline]
    pub fn bound_var_range(&self) -> Option<(u32, u32)> {
        let mut min_bound = u32::MAX;
        let mut max_bound = 0u32;
        for (i, b) in self.bindings.iter().enumerate() {
            if b.is_some() {
                let idx = i as u32;
                min_bound = min_bound.min(idx);
                max_bound = max_bound.max(idx);
            }
        }
        if min_bound > max_bound {
            None
        } else {
            Some((min_bound, max_bound))
        }
    }
}

impl Default for Subst {
    fn default() -> Self {
        Self::new()
    }
}

/// Apply a substitution to a term, returning a new term.
/// Variables bound in the substitution are replaced by their bound terms.
/// Unbound variables remain as variables.
/// Variable chains are followed iteratively to avoid stack overflow on cycles.
///
/// Uses explicit stack to avoid recursion. Acquires read_lock in batches
/// to amortize lock overhead and avoids cloning children SmallVecs.
pub fn apply_subst(term: TermId, subst: &Subst, terms: &mut TermStore) -> TermId {
    // Fast path: empty substitution
    if subst.bindings.is_empty() {
        return term;
    }
    if term.is_ground() {
        return term;
    }
    apply_subst_core::<false>(term, subst, 0, &[], terms)
}

/// Apply a substitution to an unshifted term, virtually shifting variables by
/// `var_offset` before lookup. This combines shift_vars + apply_subst into a
/// single pass, avoiding the intermediate shifted term tree entirely.
///
/// `shifted_vars[j]` must equal `terms.var(j + var_offset)` for all variable
/// indices `j` that appear in `term`. These must be pre-created before calling
/// this function (to avoid deadlock with the read lock).
///
/// Terms from substitution bindings are in the shared namespace and are
/// traversed without further shifting.
pub fn apply_subst_shifted(
    term: TermId,
    subst: &Subst,
    var_offset: u32,
    shifted_vars: &[TermId],
    terms: &mut TermStore,
) -> TermId {
    // No shift needed: delegate to standard apply_subst.
    if var_offset == 0 || shifted_vars.is_empty() {
        return apply_subst(term, subst, terms);
    }
    if term.is_ground() {
        return term;
    }
    apply_subst_core::<true>(term, subst, var_offset, shifted_vars, terms)
}

/// Core substitution application with optional virtual variable shifting.
///
/// `SHIFTED` is a const generic: when false, the compiler generates a version
/// with no shifting overhead (all visits are non-raw, shifting branches are
/// eliminated). When true, the initial term is treated as "raw" (unshifted):
/// raw variables are looked up via `shifted_vars[j]` before substitution
/// resolution, and children of raw App nodes inherit raw-ness. Terms obtained
/// from substitution bindings are in the shared namespace and traversed without
/// shifting.
///
/// Uses lock-free access via `RwLock::get_mut()` since we have exclusive
/// (`&mut`) access to the TermStore. This eliminates all lock acquire/release
/// overhead in the traversal loop.
fn apply_subst_core<const SHIFTED: bool>(
    term: TermId,
    subst: &Subst,
    _var_offset: u32,
    shifted_vars: &[TermId],
    terms: &mut TermStore,
) -> TermId {
    use crate::symbol::FuncId;

    // Pre-compute the substitution's bound variable range once.
    let subst_range = subst.bound_var_range();

    // Visit(term, is_raw): `is_raw` means the term is from the unshifted namespace
    // and its variables need virtual shifting before substitution lookup.
    // When SHIFTED=false, raw is always false and the compiler eliminates the branches.
    enum Work {
        Visit(TermId, bool),
        BuildApp(TermId, FuncId, usize),
    }

    let mut work_stack: SmallVec<[Work; 16]> = SmallVec::new();
    let mut result_stack: SmallVec<[TermId; 16]> = SmallVec::new();

    work_stack.push(Work::Visit(term, SHIFTED));

    while let Some(item) = work_stack.pop() {
        match item {
            Work::BuildApp(orig_tid, func, n) => {
                let start = result_stack.len() - n;
                // Check if any child actually changed from the original.
                // If not, reuse the original TermId to skip hashcons lookup.
                // orig_tid is always a store ref (only non-leaf App nodes get BuildApp).
                let all_same = if orig_tid.is_store_ref() {
                    let nodes = terms.nodes.get_mut();
                    match nodes.get(orig_tid.index()) {
                        Some(Term::App(_, orig_children)) => {
                            orig_children.len() == n
                                && orig_children
                                    .iter()
                                    .zip(&result_stack[start..])
                                    .all(|(a, b)| *a == *b)
                        }
                        _ => false,
                    }
                } else {
                    false
                };
                if all_same {
                    result_stack.truncate(start);
                    result_stack.push(orig_tid);
                } else {
                    let new_term = terms.app_from_slice_unlocked(func, &result_stack[start..]);
                    result_stack.truncate(start);
                    result_stack.push(new_term);
                }
            }
            Work::Visit(tid, raw) => {
                if tid.is_ground() {
                    result_stack.push(tid);
                    continue;
                }

                // Fast path: inline variable - no store access needed.
                if tid.is_inline_var() {
                    let idx_val = tid.inline_var_index();
                    let start_tid = if SHIFTED && raw {
                        let j = idx_val as usize;
                        debug_assert!(
                            j < shifted_vars.len(),
                            "var index {} exceeds shifted_vars length {}",
                            j,
                            shifted_vars.len()
                        );
                        shifted_vars[j]
                    } else {
                        tid
                    };

                    let nodes = terms.nodes.get_mut();
                    let resolved = resolve_var_chain_unlocked(start_tid, subst, nodes);

                    // Check what resolved is:
                    if resolved.is_inline() {
                        // Inline var or inline nullary - push directly.
                        result_stack.push(resolved);
                    } else {
                        match nodes.get(resolved.index()) {
                            Some(Term::App(f, children)) if !children.is_empty() => {
                                let func = *f;
                                let n = children.len();
                                work_stack.push(Work::BuildApp(resolved, func, n));
                                for i in (0..n).rev() {
                                    work_stack.push(Work::Visit(children[i], false));
                                }
                            }
                            _ => {
                                result_stack.push(resolved);
                            }
                        }
                    }
                    continue;
                }

                // Store ref (non-ground, non-inline): check var_range for early skip.
                // If this subtree's variable range has no overlap with the subst's
                // bound range, the substitution cannot affect it — return unchanged.
                // Skip subtrees whose variable range doesn't overlap the subst.
                // CRITICAL: Only valid when raw=false (or SHIFTED=false).
                // When SHIFTED && raw, the term has unshifted variables that need
                // virtual shifting even if no substitution binding applies.
                // Skipping a raw subtree would return the unshifted term, which is wrong.
                if !SHIFTED || !raw {
                    if let Some((s_min, s_max)) = subst_range {
                        if let Some(&(t_min, t_max)) = terms.var_ranges.get_mut().get(tid.index()) {
                            if t_max < s_min || t_min > s_max {
                                result_stack.push(tid);
                                continue;
                            }
                        }
                    }
                }

                // Read the term.
                let nodes = terms.nodes.get_mut();

                match nodes.get(tid.index()) {
                    Some(Term::Var(idx)) => {
                        let idx_val = *idx;
                        let start_tid = if SHIFTED && raw {
                            let j = idx_val as usize;
                            debug_assert!(
                                j < shifted_vars.len(),
                                "var index {} exceeds shifted_vars length {}",
                                j,
                                shifted_vars.len()
                            );
                            shifted_vars[j]
                        } else {
                            tid
                        };

                        let resolved = resolve_var_chain_unlocked(start_tid, subst, nodes);

                        if resolved.is_inline() {
                            result_stack.push(resolved);
                        } else {
                            match nodes.get(resolved.index()) {
                                Some(Term::App(f, children)) if !children.is_empty() => {
                                    let func = *f;
                                    let n = children.len();
                                    work_stack.push(Work::BuildApp(resolved, func, n));
                                    for i in (0..n).rev() {
                                        work_stack.push(Work::Visit(children[i], false));
                                    }
                                }
                                _ => {
                                    result_stack.push(resolved);
                                }
                            }
                        }
                    }
                    Some(Term::App(_, children)) if children.is_empty() => {
                        result_stack.push(tid);
                    }
                    Some(Term::App(f, children)) => {
                        let func = *f;
                        let n = children.len();
                        work_stack.push(Work::BuildApp(tid, func, n));
                        for i in (0..n).rev() {
                            work_stack.push(Work::Visit(children[i], SHIFTED && raw));
                        }
                    }
                    None => {
                        result_stack.push(tid);
                    }
                }
            }
        }
    }

    debug_assert_eq!(result_stack.len(), 1);
    result_stack.pop().unwrap()
}

/// Follow a chain of variable substitutions using direct slice access.
/// Returns the final term in the chain.
///
/// Well-formed substitutions from matching do not contain cycles, so we use
/// a simple depth limit rather than tracking visited nodes.
#[inline]
pub(crate) fn resolve_var_chain_unlocked(start: TermId, subst: &Subst, nodes: &[Term]) -> TermId {
    let mut current = start;
    // Depth limit to handle malformed substitutions gracefully.
    // In practice, chains are very short (1-3 steps).
    let max_depth = subst.bindings.len();
    let mut depth = 0;
    loop {
        if depth >= max_depth {
            return current;
        }
        // Fast path: inline variable - no store lookup needed.
        if current.is_inline_var() {
            match subst.get(current.inline_var_index()) {
                Some(bound) if bound != current => {
                    current = bound;
                    depth += 1;
                }
                _ => return current,
            }
            continue;
        }
        // Inline nullary or ground store ref - not a variable, stop.
        if current.is_ground() {
            return current;
        }
        // Store ref - look up in nodes.
        match nodes.get(current.index()) {
            Some(Term::Var(idx)) => match subst.get(*idx) {
                Some(bound) if bound != current => {
                    current = bound;
                    depth += 1;
                }
                _ => return current,
            },
            _ => return current,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::setup;

    // ========== SUBST CONSTRUCTION TESTS ==========

    #[test]
    fn new_subst_is_empty() {
        let subst = Subst::new();
        assert!(subst.is_empty());
        assert_eq!(subst.len(), 0);
    }

    #[test]
    fn bind_single_variable() {
        let (_, terms) = setup();
        let v5 = terms.var(5);

        let mut subst = Subst::new();
        subst.bind(0, v5);

        assert!(!subst.is_empty());
        assert_eq!(subst.len(), 1);
        assert_eq!(subst.get(0), Some(v5));
    }

    #[test]
    fn bind_multiple_variables() {
        let (_, terms) = setup();
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let v2 = terms.var(2);

        let mut subst = Subst::new();
        subst.bind(0, v1);
        subst.bind(1, v2);
        subst.bind(2, v0);

        assert_eq!(subst.len(), 3);
        assert_eq!(subst.get(0), Some(v1));
        assert_eq!(subst.get(1), Some(v2));
        assert_eq!(subst.get(2), Some(v0));
    }

    #[test]
    fn bind_extends_automatically() {
        let (_, terms) = setup();
        let t = terms.var(99);

        let mut subst = Subst::new();
        subst.bind(100, t);

        assert_eq!(subst.get(100), Some(t));
        assert_eq!(subst.len(), 1);
    }

    #[test]
    fn bind_overwrites_previous() {
        let (_, terms) = setup();
        let v1 = terms.var(1);
        let v2 = terms.var(2);

        let mut subst = Subst::new();
        subst.bind(0, v1);
        subst.bind(0, v2);

        assert_eq!(subst.get(0), Some(v2));
        assert_eq!(subst.len(), 1);
    }

    #[test]
    fn get_unbound_returns_none() {
        let subst = Subst::new();
        assert_eq!(subst.get(0), None);
        assert_eq!(subst.get(100), None);
    }

    #[test]
    fn is_bound_correct() {
        let (_, terms) = setup();
        let t = terms.var(5);

        let mut subst = Subst::new();
        subst.bind(0, t);

        assert!(subst.is_bound(0));
        assert!(!subst.is_bound(1));
        assert!(!subst.is_bound(100));
    }

    #[test]
    fn iter_over_bindings() {
        let (_, terms) = setup();
        let v1 = terms.var(1);
        let v2 = terms.var(2);

        let mut subst = Subst::new();
        subst.bind(0, v1);
        subst.bind(2, v2); // skip index 1

        let bindings: Vec<_> = subst.iter().collect();
        assert_eq!(bindings.len(), 2);
        assert!(bindings.contains(&(0, v1)));
        assert!(bindings.contains(&(2, v2)));
    }

    // ========== APPLY_SUBST TESTS ==========

    #[test]
    fn apply_to_unbound_var_unchanged() {
        let (_, mut terms) = setup();
        let v0 = terms.var(0);
        let subst = Subst::new();

        let result = apply_subst(v0, &subst, &mut terms);
        assert_eq!(result, v0);
    }

    #[test]
    fn apply_to_bound_var_replaces() {
        let (symbols, mut terms) = setup();
        let nil = symbols.intern("Nil");
        let v0 = terms.var(0);
        let nil_term = terms.app0(nil);

        let mut subst = Subst::new();
        subst.bind(0, nil_term);

        let result = apply_subst(v0, &subst, &mut terms);
        assert_eq!(result, nil_term);
    }

    #[test]
    fn apply_to_ground_term_unchanged() {
        let (symbols, mut terms) = setup();
        let zero = symbols.intern("Zero");
        let succ = symbols.intern("Succ");
        let n0 = terms.app0(zero);
        let n1 = terms.app1(succ, n0);

        let mut subst = Subst::new();
        subst.bind(0, n0);

        let result = apply_subst(n1, &subst, &mut terms);
        assert_eq!(result, n1, "Ground term should be unchanged");
    }

    #[test]
    fn apply_replaces_in_nested_term() {
        let (symbols, mut terms) = setup();
        let f = symbols.intern("F");
        let g = symbols.intern("G");
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // F(x, G(y))
        let g_y = terms.app1(g, v1);
        let term = terms.app2(f, v0, g_y);

        // Substitute x -> G(y)
        let mut subst = Subst::new();
        subst.bind(0, g_y);

        let result = apply_subst(term, &subst, &mut terms);

        // Should be F(G(y), G(y))
        let expected = terms.app2(f, g_y, g_y);
        assert_eq!(result, expected);
    }

    #[test]
    fn apply_multiple_substitutions() {
        let (symbols, mut terms) = setup();
        let pair = symbols.intern("Pair");
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let v2 = terms.var(2);
        let v3 = terms.var(3);

        // Pair(x, y)
        let term = terms.app2(pair, v0, v1);

        // Substitute x -> z, y -> w
        let mut subst = Subst::new();
        subst.bind(0, v2);
        subst.bind(1, v3);

        let result = apply_subst(term, &subst, &mut terms);

        // Should be Pair(z, w)
        let expected = terms.app2(pair, v2, v3);
        assert_eq!(result, expected);
    }

    #[test]
    fn apply_deeply_nested() {
        let (symbols, mut terms) = setup();
        let f = symbols.intern("F");
        let a = symbols.intern("A");
        let v0 = terms.var(0);

        // F(F(F(F(x))))
        let f1 = terms.app1(f, v0);
        let f2 = terms.app1(f, f1);
        let f3 = terms.app1(f, f2);
        let f4 = terms.app1(f, f3);

        // Substitute x -> A
        let a_term = terms.app0(a);
        let mut subst = Subst::new();
        subst.bind(0, a_term);

        let result = apply_subst(f4, &subst, &mut terms);

        // Should be F(F(F(F(A))))
        let e1 = terms.app1(f, a_term);
        let e2 = terms.app1(f, e1);
        let e3 = terms.app1(f, e2);
        let expected = terms.app1(f, e3);
        assert_eq!(result, expected);
    }

    #[test]
    fn apply_chain_of_vars() {
        let (_, mut terms) = setup();
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let v2 = terms.var(2);

        // Substitute 0 -> 1, 1 -> 2
        let mut subst = Subst::new();
        subst.bind(0, v1);
        subst.bind(1, v2);

        // Apply to var(0) should follow the chain: 0 -> 1 -> 2
        let result = apply_subst(v0, &subst, &mut terms);
        assert_eq!(result, v2, "Should follow chain of substitutions");
    }

    #[test]
    fn apply_to_wide_term() {
        let (symbols, mut terms) = setup();
        let tuple = symbols.intern("Tuple");
        let a = symbols.intern("A");
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let v2 = terms.var(2);

        // Tuple(x, y, z)
        let children: SmallVec<[TermId; 4]> = smallvec::smallvec![v0, v1, v2];
        let term = terms.app(tuple, children);

        // Substitute all with A
        let a_term = terms.app0(a);
        let mut subst = Subst::new();
        subst.bind(0, a_term);
        subst.bind(1, a_term);
        subst.bind(2, a_term);

        let result = apply_subst(term, &subst, &mut terms);

        // Should be Tuple(A, A, A)
        let expected_children: SmallVec<[TermId; 4]> = smallvec::smallvec![a_term, a_term, a_term];
        let expected = terms.app(tuple, expected_children);
        assert_eq!(result, expected);
    }

    #[test]
    fn apply_preserves_structure() {
        let (symbols, mut terms) = setup();
        let cons = symbols.intern("Cons");
        let nil = symbols.intern("Nil");
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // Cons(x, Cons(y, Nil))
        let nil_term = terms.app0(nil);
        let inner = terms.app2(cons, v1, nil_term);
        let term = terms.app2(cons, v0, inner);

        // Empty substitution
        let subst = Subst::new();

        let result = apply_subst(term, &subst, &mut terms);
        assert_eq!(result, term, "Empty subst should preserve term exactly");
    }

    // ========== EDGE CASES ==========

    #[test]
    fn apply_subst_var_maps_to_itself() {
        let (_, mut terms) = setup();
        let v0 = terms.var(0);

        // Substitute 0 -> 0 (identity)
        let mut subst = Subst::new();
        subst.bind(0, v0);

        let result = apply_subst(v0, &subst, &mut terms);
        assert_eq!(result, v0);
    }

    #[test]
    fn apply_nullary_app() {
        let (symbols, mut terms) = setup();
        let zero = symbols.intern("Zero");
        let term = terms.app0(zero);

        let mut subst = Subst::new();
        subst.bind(0, terms.var(1));

        let result = apply_subst(term, &subst, &mut terms);
        assert_eq!(result, term, "Nullary app unchanged");
    }

    #[test]
    fn apply_sparse_binding() {
        let (symbols, mut terms) = setup();
        let f = symbols.intern("F");
        let a = symbols.intern("A");
        let v0 = terms.var(0);
        let v100 = terms.var(100);

        // F(x0, x100)
        let term = terms.app2(f, v0, v100);

        // Only bind var 100
        let a_term = terms.app0(a);
        let mut subst = Subst::new();
        subst.bind(100, a_term);

        let result = apply_subst(term, &subst, &mut terms);

        // Should be F(x0, A)
        let expected = terms.app2(f, v0, a_term);
        assert_eq!(result, expected);
    }

    // ========== HASHCONSING INTERACTION ==========

    #[test]
    fn apply_uses_hashconsing() {
        let (symbols, mut terms) = setup();
        let f = symbols.intern("F");
        let a = symbols.intern("A");
        let v0 = terms.var(0);

        // F(x) and F(x) separately
        let term1 = terms.app1(f, v0);
        let term2 = terms.app1(f, v0);
        assert_eq!(term1, term2, "Hashconsing should work");

        // Substitute x -> A
        let a_term = terms.app0(a);
        let mut subst = Subst::new();
        subst.bind(0, a_term);

        let result1 = apply_subst(term1, &subst, &mut terms);
        let result2 = apply_subst(term2, &subst, &mut terms);

        // Results should also be same via hashconsing
        assert_eq!(result1, result2);
    }
}
