use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::sync::Arc;

use crate::constraint::{ConstraintDisplay, ConstraintOps};
use crate::drop_fresh::DropFresh;
use crate::symbol::SymbolStore;
use crate::term::{format_term, Term, TermId, TermStore};
use smallvec::SmallVec;

/// Inner storage for NF fields, shared via Arc.
#[derive(Debug)]
pub struct NfInner<C> {
    /// Patterns for matching input terms (RwL).
    /// Variables in these patterns are numbered 0..n-1 in order of first appearance.
    pub match_pats: SmallVec<[TermId; 1]>,
    /// Variable routing between match and build.
    pub drop_fresh: DropFresh<C>,
    /// Patterns for building output terms (RwR).
    /// Variables in these patterns are numbered 0..m-1 with shared vars in LHS order,
    /// followed by RHS-only vars in RHS order.
    pub build_pats: SmallVec<[TermId; 1]>,
    /// Pre-computed hash of match_pats, drop_fresh, and build_pats.
    cached_hash: u64,
    /// Pre-computed rhs_map: maps build-side variable indices to direct-form
    /// variable indices. This is the same mapping that `collect_tensor` computes
    /// on every call, but cached here for reuse. Each entry `rhs_map[j]` gives
    /// the direct-form variable index for build-side variable `j`.
    ///
    /// For shared variables (those in the DropFresh map), `rhs_map[j] = i` where
    /// `(i, j)` is in the map. For fresh variables, indices continue from `in_arity`.
    pub cached_rhs_map: SmallVec<[u32; 4]>,
}

/// Normal Form representation of a rewrite rule.
///
/// A rule `Rw lhs rhs` is factored into:
///   RwL [match_pats] ; DropFresh ; RwR [build_pats]
///
/// Where:
/// - RwL (match_pats): patterns to decompose input, extracting variables
/// - DropFresh: variable routing between LHS vars and RHS vars
/// - RwR (build_pats): patterns to construct output from variables
///
/// The inner fields are shared via Arc, making clone O(1) (atomic ref count bump)
/// instead of copying ~48 bytes of data + 2 atomic bumps for DropFresh.
/// Fields are accessible via Deref to NfInner.
#[derive(Debug, Clone)]
pub struct NF<C> {
    inner: Arc<NfInner<C>>,
}

impl<C> Deref for NF<C> {
    type Target = NfInner<C>;

    #[inline(always)]
    fn deref(&self) -> &NfInner<C> {
        &self.inner
    }
}

impl<C: Hash> Hash for NF<C> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.cached_hash.hash(state);
    }
}

impl<C: PartialEq> PartialEq for NF<C> {
    fn eq(&self, other: &Self) -> bool {
        // Fast path: same Arc pointer means identical
        Arc::ptr_eq(&self.inner, &other.inner)
            || (self.inner.cached_hash == other.inner.cached_hash
                && self.inner.match_pats == other.inner.match_pats
                && self.inner.drop_fresh == other.inner.drop_fresh
                && self.inner.build_pats == other.inner.build_pats)
    }
}

impl<C: Eq> Eq for NF<C> {}

/// Direct tensor rewrite form (lists of patterns with constraint).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RwT<C> {
    pub lhs: SmallVec<[TermId; 1]>,
    pub rhs: SmallVec<[TermId; 1]>,
    pub constraint: C,
}

/// Compute the cached hash for NF content fields.
fn compute_nf_hash<C: Hash>(
    match_pats: &SmallVec<[TermId; 1]>,
    drop_fresh: &DropFresh<C>,
    build_pats: &SmallVec<[TermId; 1]>,
) -> u64 {
    let mut hasher = rustc_hash::FxHasher::default();
    match_pats.hash(&mut hasher);
    drop_fresh.hash(&mut hasher);
    build_pats.hash(&mut hasher);
    hasher.finish()
}

/// Compute the cached rhs_map from a DropFresh structure.
///
/// The rhs_map maps build-side variable indices (0..out_arity) to direct-form
/// variable indices. Shared variables map to their corresponding input positions,
/// and fresh variables get indices starting from in_arity.
fn compute_rhs_map<C>(drop_fresh: &DropFresh<C>) -> SmallVec<[u32; 4]> {
    let out_arity = drop_fresh.out_arity as usize;
    let in_arity = drop_fresh.in_arity;
    let mut rhs_map: SmallVec<[u32; 4]> = smallvec::smallvec![u32::MAX; out_arity];
    for &(i, j) in drop_fresh.map.iter() {
        if (j as usize) < out_arity {
            rhs_map[j as usize] = i;
        }
    }
    let mut next_var = in_arity;
    for slot in rhs_map.iter_mut() {
        if *slot == u32::MAX {
            *slot = next_var;
            next_var += 1;
        }
    }
    rhs_map
}

impl<C: Hash> NF<C> {
    /// Access the pre-computed hash value for this NF.
    ///
    /// This is the same value used by the `Hash` impl and is computed from
    /// all content fields (match_pats, drop_fresh, build_pats).
    pub fn hash_value(&self) -> u64 {
        self.inner.cached_hash
    }

    /// Create a new NF directly (assumes already normalized).
    pub fn new(
        match_pats: SmallVec<[TermId; 1]>,
        drop_fresh: DropFresh<C>,
        build_pats: SmallVec<[TermId; 1]>,
    ) -> Self {
        let cached_hash = compute_nf_hash(&match_pats, &drop_fresh, &build_pats);
        let cached_rhs_map = compute_rhs_map(&drop_fresh);
        Self {
            inner: Arc::new(NfInner {
                match_pats,
                drop_fresh,
                build_pats,
                cached_hash,
                cached_rhs_map,
            }),
        }
    }

    /// Create an identity NF (empty patterns, zero-arity DropFresh).
    ///
    /// This represents the identity relation that accepts any input
    /// and produces it unchanged.
    pub fn identity(constraint: C) -> Self {
        Self::new(
            SmallVec::new(),
            DropFresh::identity_with_constraint(0, constraint),
            SmallVec::new(),
        )
    }

    /// Maximum variable index in the direct-rule (RwT) form of this NF.
    ///
    /// After `collect_tensor`, match_pats use vars `0..in_arity-1` and
    /// build_pats use shared vars mapped to their LHS indices plus fresh
    /// vars starting at `in_arity`. This computes the overall max in O(1)
    /// from DropFresh metadata, avoiding term tree traversal.
    pub fn rwt_max_var(&self) -> Option<u32> {
        let num_fresh = self
            .inner
            .drop_fresh
            .out_arity
            .saturating_sub(self.inner.drop_fresh.map.len() as u32);
        let total = self.inner.drop_fresh.in_arity + num_fresh;
        if total > 0 {
            Some(total - 1)
        } else {
            None
        }
    }
}

impl<C: ConstraintOps> NF<C> {
    /// Factor a single-term rule (lhs -> rhs) into normal form.
    ///
    /// This extracts variables, renumbers them, and computes the DropFresh
    /// that connects LHS variables to RHS variables.
    pub fn factor(lhs: TermId, rhs: TermId, constraint: C, terms: &mut TermStore) -> Self {
        factor_tensor(smallvec::smallvec![lhs], smallvec::smallvec![rhs], constraint, terms)
    }
}

/// Collect a tensor NF into direct-rule form by pushing wiring into RHS vars.
pub fn collect_tensor<C: Clone>(nf: &NF<C>, terms: &mut TermStore) -> RwT<C> {
    let rhs_map = &nf.cached_rhs_map;
    let rhs_direct: SmallVec<[TermId; 1]> = nf
        .build_pats
        .iter()
        .map(|&t| {
            crate::matching::transform_vars(t, terms, |j| {
                TermId::inline_var(rhs_map[j])
            })
        })
        .collect();

    RwT {
        lhs: nf.match_pats.clone(),
        rhs: rhs_direct,
        constraint: nf.drop_fresh.constraint.clone(),
    }
}

/// Factor a tensor rewrite (lists of patterns) into NF.
pub fn factor_tensor<C: ConstraintOps>(
    lhs_pats: SmallVec<[TermId; 1]>,
    rhs_pats: SmallVec<[TermId; 1]>,
    constraint: C,
    terms: &mut TermStore,
) -> NF<C> {
    // Step 1: Fused collect + renumber LHS in a single pass per term.
    let (norm_lhs, lhs_vars) = renumber_vars_list(&lhs_pats, terms);

    // Step 2: Collect RHS variables (one pass, not two).
    let rhs_vars = collect_vars_ordered_list(&rhs_pats, terms);

    // Steps 3-5, 7: Build wiring (bitsets, rhs ordering, constraint renaming, DropFresh).
    let (rhs_old_to_new, drop_fresh) = build_factor_wiring(&lhs_vars, &rhs_vars, constraint, terms);

    // Step 6: Renumber RHS variables.
    let norm_rhs = if rhs_old_to_new.is_empty() {
        rhs_pats.clone()
    } else {
        apply_var_renaming_list(&rhs_pats, &rhs_old_to_new, terms)
    };

    NF::new(norm_lhs, drop_fresh, norm_rhs)
}

/// Build the RHS variable ordering, renaming map, and DropFresh from already-collected
/// LHS and RHS variable lists. This is the shared core of factor_tensor and
/// factor_tensor_with_subst (Steps 3-5, 7).
///
/// Returns (rhs_old_to_new, drop_fresh) where rhs_old_to_new maps original RHS
/// variable indices to their new consecutive positions.
fn build_factor_wiring<C: ConstraintOps>(
    lhs_vars: &[u32],
    rhs_vars: &[u32],
    constraint: C,
    terms: &mut TermStore,
) -> (Vec<Option<u32>>, DropFresh<C>) {
    let n = lhs_vars.len() as u32;

    // Build membership bitsets for O(1) lookups instead of HashSets.
    let mut lhs_bits: u64 = 0;
    let mut lhs_has_large = false;
    for &var in lhs_vars.iter() {
        if var < 64 {
            lhs_bits |= 1u64 << var;
        } else {
            lhs_has_large = true;
        }
    }
    let mut rhs_bits: u64 = 0;
    let mut rhs_has_large = false;
    for &var in rhs_vars.iter() {
        if var < 64 {
            rhs_bits |= 1u64 << var;
        } else {
            rhs_has_large = true;
        }
    }

    let lhs_contains = |var: u32| -> bool {
        if var < 64 {
            lhs_bits & (1u64 << var) != 0
        } else if lhs_has_large {
            lhs_vars.contains(&var)
        } else {
            false
        }
    };
    let rhs_contains = |var: u32| -> bool {
        if var < 64 {
            rhs_bits & (1u64 << var) != 0
        } else if rhs_has_large {
            rhs_vars.contains(&var)
        } else {
            false
        }
    };

    // Build RHS variable ordering: shared vars in LHS order, then RHS-only vars.
    let mut rhs_ordered: Vec<u32> = Vec::new();
    for &var in lhs_vars.iter() {
        if rhs_contains(var) {
            rhs_ordered.push(var);
        }
    }
    for &var in rhs_vars.iter() {
        if !lhs_contains(var) {
            rhs_ordered.push(var);
        }
    }

    let m = rhs_ordered.len() as u32;
    let rhs_old_to_new = build_var_map(&rhs_ordered);

    // Compute constraint renaming.
    let constraint = if !constraint.is_empty() {
        let mut constraint_vars = Vec::new();
        constraint.collect_vars(terms, &mut constraint_vars);
        constraint_vars.sort_unstable();
        constraint_vars.dedup();
        let constraint_map = combined_var_renaming_with_extra(lhs_vars, rhs_vars, &constraint_vars);
        constraint.remap_vars(&constraint_map, terms)
    } else {
        constraint
    };

    // Build DropFresh map.
    let mut drop_fresh_map: SmallVec<[(u32, u32); 4]> = SmallVec::new();
    for (i, &lhs_orig_var) in lhs_vars.iter().enumerate() {
        let idx = lhs_orig_var as usize;
        if idx < rhs_old_to_new.len() {
            if let Some(j) = rhs_old_to_new[idx] {
                drop_fresh_map.push((i as u32, j));
            }
        }
    }

    let drop_fresh = DropFresh {
        in_arity: n,
        out_arity: m,
        map: drop_fresh_map,
        constraint,
    };

    (rhs_old_to_new, drop_fresh)
}

/// Compute a renaming map for constraints using LHS vars, RHS-only vars,
/// then any extra vars (e.g., constraint-only vars).
fn combined_var_renaming_with_extra(
    lhs_vars: &[u32],
    rhs_vars: &[u32],
    extra_vars: &[u32],
) -> Vec<Option<u32>> {
    let mut ordered: Vec<u32> = Vec::new();
    let mut seen_bits: u64 = 0;
    let mut seen_large: Vec<u32> = Vec::new();
    for &var in lhs_vars.iter().chain(rhs_vars.iter()).chain(extra_vars.iter()) {
        if var < 64 {
            let bit = 1u64 << var;
            if seen_bits & bit == 0 {
                seen_bits |= bit;
                ordered.push(var);
            }
        } else if !seen_large.contains(&var) {
            seen_large.push(var);
            ordered.push(var);
        }
    }
    build_var_map(&ordered)
}

/// Build a variable renaming map from a list of original variable indices.
/// Maps old_idx -> new_idx where new_idx is the position in vars.
fn build_var_map(vars: &[u32]) -> Vec<Option<u32>> {
    if vars.is_empty() {
        return Vec::new();
    }
    let max_var = vars.iter().copied().max().unwrap_or(0) as usize;
    let mut old_to_new = vec![None; max_var + 1];
    for (new_idx, &old_idx) in vars.iter().enumerate() {
        old_to_new[old_idx as usize] = Some(new_idx as u32);
    }
    old_to_new
}

/// Collect variables from a term in order of first appearance.
/// Returns the list of original variable indices (unique).
pub(crate) fn collect_vars_ordered(term: TermId, terms: &TermStore) -> Vec<u32> {
    let mut vars = Vec::new();
    let mut seen = std::collections::HashSet::new();
    collect_vars_helper(term, terms, &mut vars, &mut seen);
    vars
}

/// Collect variables from a list of terms in order of first appearance.
fn collect_vars_ordered_list(terms_list: &[TermId], terms: &TermStore) -> Vec<u32> {
    let mut vars = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for &term in terms_list {
        collect_vars_helper(term, terms, &mut vars, &mut seen);
    }
    vars
}

fn collect_vars_helper(
    term: TermId,
    terms: &TermStore,
    vars: &mut Vec<u32>,
    seen: &mut std::collections::HashSet<u32>,
) {
    // Use read_lock once for the entire traversal (no per-node locking).
    let guard = terms.read_lock();
    let mut stack: SmallVec<[TermId; 16]> = SmallVec::new();
    // Use a bitset for small variable indices (0..64) to avoid HashSet overhead.
    // Variables >= 64 fall back to the HashSet.
    let mut seen_bits: u64 = 0;
    // Pre-populate seen_bits from any vars already in `seen` (from previous terms in a list).
    for &v in seen.iter() {
        if v < 64 {
            seen_bits |= 1u64 << v;
        }
    }
    stack.push(term);
    while let Some(tid) = stack.pop() {
        // Ground terms contain no variables — skip entire subtree.
        if tid.is_ground() {
            continue;
        }
        // Fast path: inline variable.
        if tid.is_inline_var() {
            let v = tid.inline_var_index();
            if v < 64 {
                let bit = 1u64 << v;
                if seen_bits & bit == 0 {
                    seen_bits |= bit;
                    seen.insert(v);
                    vars.push(v);
                }
            } else if seen.insert(v) {
                vars.push(v);
            }
            continue;
        }
        // Store ref (non-ground).
        match guard.get(tid) {
            Some(Term::Var(idx)) => {
                let v = *idx;
                if v < 64 {
                    let bit = 1u64 << v;
                    if seen_bits & bit == 0 {
                        seen_bits |= bit;
                        seen.insert(v);
                        vars.push(v);
                    }
                } else if seen.insert(v) {
                    vars.push(v);
                }
            }
            Some(Term::App(_, children)) => {
                for child in children.iter().rev() {
                    stack.push(*child);
                }
            }
            None => {}
        }
    }
}

/// Renumber variables in a list of terms to use consecutive indices starting at 0.
/// Variables are numbered in order of first appearance across all terms (left to right).
/// Returns the renumbered terms and the mapping from new index to old index.
///
/// This is a fused single-pass implementation that discovers variables and
/// renames them in one traversal per term.
fn renumber_vars_list(
    terms_list: &[TermId],
    terms: &mut TermStore,
) -> (SmallVec<[TermId; 1]>, Vec<u32>) {
    use crate::symbol::FuncId;

    let mut var_map: Vec<Option<u32>> = Vec::new();
    let mut vars: Vec<u32> = Vec::new();
    let mut next_var: u32 = 0;
    let mut is_identity = true;

    enum Work {
        Visit(TermId),
        BuildApp(TermId, FuncId, usize),
    }

    let mut work_stack: SmallVec<[Work; 16]> = SmallVec::new();
    let mut result_stack: SmallVec<[TermId; 16]> = SmallVec::new();
    let mut result_terms: SmallVec<[TermId; 1]> = SmallVec::new();

    for &term in terms_list {
        if term.is_ground() {
            result_terms.push(term);
            continue;
        }

        work_stack.clear();
        result_stack.clear();
        work_stack.push(Work::Visit(term));

        while let Some(item) = work_stack.pop() {
            match item {
                Work::BuildApp(orig_tid, func, n) => {
                    let start = result_stack.len() - n;
                    let all_same = match terms.get_unlocked(orig_tid) {
                        Some(Term::App(_, orig_children)) => {
                            orig_children.len() == n
                                && orig_children
                                    .iter()
                                    .zip(&result_stack[start..])
                                    .all(|(a, b)| *a == *b)
                        }
                        _ => false,
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
                Work::Visit(tid) => {
                    if tid.is_ground() {
                        result_stack.push(tid);
                        continue;
                    }
                    // Inline var fast path: no store lookup needed.
                    if tid.is_inline_var() {
                        let old_idx = tid.inline_var_index();
                        let old_usize = old_idx as usize;
                        if old_usize >= var_map.len() {
                            var_map.resize(old_usize + 1, None);
                        }
                        let new_idx = match var_map[old_usize] {
                            Some(already) => already,
                            None => {
                                let assigned = next_var;
                                next_var += 1;
                                var_map[old_usize] = Some(assigned);
                                vars.push(old_idx);
                                if assigned != old_idx {
                                    is_identity = false;
                                }
                                assigned
                            }
                        };
                        result_stack.push(TermId::inline_var(new_idx));
                        continue;
                    }
                    // Inline nullary fast path: no variables, push directly.
                    if tid.is_inline_nullary() {
                        result_stack.push(tid);
                        continue;
                    }
                    let var_action: Option<u32> = match terms.get_unlocked(tid) {
                        Some(Term::Var(idx)) => {
                            let old_idx = *idx;
                            let old_usize = old_idx as usize;
                            if old_usize >= var_map.len() {
                                var_map.resize(old_usize + 1, None);
                            }
                            let new_idx = match var_map[old_usize] {
                                Some(already) => already,
                                None => {
                                    let assigned = next_var;
                                    next_var += 1;
                                    var_map[old_usize] = Some(assigned);
                                    vars.push(old_idx);
                                    if assigned != old_idx {
                                        is_identity = false;
                                    }
                                    assigned
                                }
                            };
                            Some(new_idx)
                        }
                        Some(Term::App(_, children)) if children.is_empty() => {
                            result_stack.push(tid);
                            None
                        }
                        Some(Term::App(f, children)) => {
                            let func = *f;
                            let n = children.len();
                            work_stack.push(Work::BuildApp(tid, func, n));
                            for i in (0..n).rev() {
                                work_stack.push(Work::Visit(children[i]));
                            }
                            None
                        }
                        None => {
                            result_stack.push(tid);
                            None
                        }
                    };
                    if let Some(new_idx) = var_action {
                        result_stack.push(TermId::inline_var(new_idx));
                    }
                }
            }
        }

        debug_assert_eq!(result_stack.len(), 1);
        result_terms.push(result_stack.pop().unwrap());
    }

    if is_identity {
        return (terms_list.iter().copied().collect(), vars);
    }

    (result_terms, vars)
}

/// Walk a list of terms through substitution chains and rebuild with remapped variables.
///
/// This is the shared core of `renumber_vars_through_subst_list` and
/// `apply_subst_and_renumber_list`. Each final variable index (after resolution
/// through substitutions) is passed to `var_action`, which returns the output
/// variable index for the rebuilt term.
fn traverse_subst_and_remap(
    terms_list: &[TermId],
    params: &SubstParams<'_>,
    terms: &mut TermStore,
    mut var_action: impl FnMut(u32) -> u32,
) -> SmallVec<[TermId; 1]> {
    use crate::subst::resolve_var_chain_unlocked;
    use crate::symbol::FuncId;

    enum Work {
        Visit(TermId, bool),
        BuildApp(FuncId, usize),
    }

    let mut work_stack: SmallVec<[Work; 16]> = SmallVec::new();
    let mut result_stack: SmallVec<[TermId; 16]> = SmallVec::new();
    let mut result_terms: SmallVec<[TermId; 1]> = SmallVec::new();

    for &term in terms_list {
        if term.is_ground() {
            result_terms.push(term);
            continue;
        }

        work_stack.clear();
        result_stack.clear();
        work_stack.push(Work::Visit(term, params.shifted));

        while let Some(item) = work_stack.pop() {
            match item {
                Work::BuildApp(func, n) => {
                    let start = result_stack.len() - n;
                    let new_term = terms.app_from_slice_unlocked(func, &result_stack[start..]);
                    result_stack.truncate(start);
                    result_stack.push(new_term);
                }
                Work::Visit(tid, raw) => {
                    if tid.is_ground() {
                        result_stack.push(tid);
                        continue;
                    }
                    if tid.is_inline_nullary() {
                        result_stack.push(tid);
                        continue;
                    }

                    // Extract variable index. For app terms, push children and continue.
                    let var_idx = if tid.is_inline_var() {
                        tid.inline_var_index()
                    } else {
                        match terms.get_unlocked(tid) {
                            Some(Term::Var(idx)) => *idx,
                            Some(Term::App(_, children)) if children.is_empty() => {
                                result_stack.push(tid);
                                continue;
                            }
                            Some(Term::App(f, children)) => {
                                let func = *f;
                                let n = children.len();
                                work_stack.push(Work::BuildApp(func, n));
                                for i in (0..n).rev() {
                                    work_stack.push(Work::Visit(children[i], raw));
                                }
                                continue;
                            }
                            None => {
                                debug_assert!(false, "TermStore missing entry for {:?}", tid);
                                result_stack.push(tid);
                                continue;
                            }
                        }
                    };

                    // Resolve through substitution chain.
                    let start_tid = if raw {
                        let j = var_idx as usize;
                        debug_assert!(j < params.shifted_vars.len());
                        params.shifted_vars[j]
                    } else {
                        tid
                    };
                    let mut resolved = resolve_var_chain_unlocked(start_tid, params.subst);
                    if let Some(s2) = params.subst2 {
                        resolved = resolve_var_chain_unlocked(resolved, s2);
                    }

                    // Classify the resolved term and act.
                    if resolved.is_inline_var() {
                        let new_idx = var_action(resolved.inline_var_index());
                        result_stack.push(TermId::inline_var(new_idx));
                    } else if resolved.is_inline_nullary() || resolved.is_ground() {
                        result_stack.push(resolved);
                    } else {
                        match terms.get_unlocked(resolved) {
                            Some(Term::Var(final_idx)) => {
                                let new_idx = var_action(*final_idx);
                                result_stack.push(TermId::inline_var(new_idx));
                            }
                            Some(Term::App(_, children)) if children.is_empty() => {
                                result_stack.push(resolved);
                            }
                            Some(Term::App(f, children)) => {
                                let func = *f;
                                let child_ids: SmallVec<[TermId; 8]> =
                                    children.iter().copied().collect();
                                let n = child_ids.len();
                                work_stack.push(Work::BuildApp(func, n));
                                for i in (0..n).rev() {
                                    work_stack.push(Work::Visit(child_ids[i], false));
                                }
                            }
                            None => {
                                debug_assert!(
                                    false,
                                    "TermStore missing resolved entry for {:?}",
                                    resolved
                                );
                                result_stack.push(resolved);
                            }
                        }
                    }
                }
            }
        }

        debug_assert_eq!(result_stack.len(), 1);
        result_terms.push(result_stack.pop().unwrap());
    }

    result_terms
}

/// Fused apply_subst + renumber_vars_list: walks original patterns, resolves
/// variables through substitutions, and renumbers to consecutive indices.
fn renumber_vars_through_subst_list(
    terms_list: &[TermId],
    params: &SubstParams<'_>,
    terms: &mut TermStore,
) -> (SmallVec<[TermId; 1]>, Vec<u32>) {
    let mut var_map: Vec<Option<u32>> = Vec::new();
    let mut vars: Vec<u32> = Vec::new();
    let mut next_var: u32 = 0;

    let result = traverse_subst_and_remap(terms_list, params, terms, |old_idx| {
        let old_usize = old_idx as usize;
        if old_usize >= var_map.len() {
            var_map.resize(old_usize + 1, None);
        }
        match var_map[old_usize] {
            Some(already) => already,
            None => {
                let assigned = next_var;
                next_var += 1;
                var_map[old_usize] = Some(assigned);
                vars.push(old_idx);
                assigned
            }
        }
    });

    (result, vars)
}

/// Collect variables from a list of terms by walking through one or two substitutions
/// (optionally with virtual shifting). Discovers variable indices using the shared
/// traversal — rebuilt terms are discarded.
fn collect_vars_through_subst_list(
    terms_list: &[TermId],
    params: &SubstParams<'_>,
    terms: &mut TermStore,
) -> Vec<u32> {
    let mut vars = Vec::new();
    let mut seen_bits: u64 = 0;
    let mut seen_large: std::collections::HashSet<u32> = std::collections::HashSet::new();

    let _ = traverse_subst_and_remap(terms_list, params, terms, |final_idx| {
        if final_idx < 64 {
            let bit = 1u64 << final_idx;
            if seen_bits & bit == 0 {
                seen_bits |= bit;
                vars.push(final_idx);
            }
        } else if seen_large.insert(final_idx) {
            vars.push(final_idx);
        }
        final_idx
    });

    vars
}

/// Bundled substitution parameters for fused factor operations.
/// Groups a primary substitution, optional secondary substitution, and optional
/// virtual shifting info to keep function signatures manageable.
pub(crate) struct SubstParams<'a> {
    /// Primary substitution.
    pub subst: &'a crate::subst::Subst,
    /// Optional secondary substitution (e.g., from constraint normalization).
    pub subst2: Option<&'a crate::subst::Subst>,
    /// Whether variables need virtual shifting before substitution lookup.
    pub shifted: bool,
    /// Pre-created shifted variable TermIds (only used when shifted=true).
    pub shifted_vars: &'a [TermId],
}

/// Factor a tensor rewrite into NF using pre-computed substitutions instead of
/// pre-substituted patterns. This eliminates intermediate term creation by
/// resolving substitutions during the collect-vars and renumber passes.
pub(crate) fn factor_tensor_with_subst<C: ConstraintOps>(
    lhs_pats: &[TermId],
    lhs_params: &SubstParams<'_>,
    rhs_pats: &[TermId],
    rhs_params: &SubstParams<'_>,
    constraint: C,
    terms: &mut TermStore,
) -> NF<C> {
    // Step 1: Fused apply_subst + renumber on LHS (single traversal).
    let (norm_lhs, lhs_vars) = renumber_vars_through_subst_list(lhs_pats, lhs_params, terms);

    // Step 2: Collect RHS variables through substitution (read-only, no term creation).
    let rhs_vars = collect_vars_through_subst_list(rhs_pats, rhs_params, terms);

    // Steps 3-5, 7: Build wiring (bitsets, rhs ordering, constraint renaming, DropFresh).
    let (rhs_old_to_new, drop_fresh) = build_factor_wiring(&lhs_vars, &rhs_vars, constraint, terms);

    // Step 6: Apply subst + renumber on RHS in a single traversal.
    // We always apply the substitution even when rhs_old_to_new is empty because
    // variables may have been bound to ground terms by the substitution.
    let norm_rhs = apply_subst_and_renumber_list(rhs_pats, rhs_params, &rhs_old_to_new, terms);

    NF::new(norm_lhs, drop_fresh, norm_rhs)
}

/// Fused apply_subst + apply_var_renaming: resolves variables through substitutions
/// then applies a renaming map to final variable indices in a single traversal.
fn apply_subst_and_renumber_list(
    terms_list: &[TermId],
    params: &SubstParams<'_>,
    renaming: &[Option<u32>],
    terms: &mut TermStore,
) -> SmallVec<[TermId; 1]> {
    traverse_subst_and_remap(terms_list, params, terms, |final_idx| {
        let old_idx = final_idx as usize;
        if old_idx < renaming.len() {
            renaming[old_idx].unwrap_or(final_idx)
        } else {
            final_idx
        }
    })
}

/// Renumber variables according to a sparse mapping (old index → new index).
/// Entries with `None` or indices beyond the mapping keep their original value.
pub fn apply_var_renaming(
    term: TermId,
    old_to_new: &[Option<u32>],
    terms: &mut TermStore,
) -> TermId {
    // Fast path: identity mapping has no effect.
    let is_identity = old_to_new
        .iter()
        .enumerate()
        .all(|(i, v)| *v == Some(i as u32) || v.is_none());
    if is_identity {
        return term;
    }
    crate::matching::transform_vars(term, terms, |j| {
        if j < old_to_new.len() {
            old_to_new[j].map_or(TermId::inline_var(j as u32), TermId::inline_var)
        } else {
            TermId::inline_var(j as u32)
        }
    })
}

fn apply_var_renaming_list(
    terms_list: &[TermId],
    old_to_new: &[Option<u32>],
    terms: &mut TermStore,
) -> SmallVec<[TermId; 1]> {
    terms_list
        .iter()
        .map(|&term| apply_var_renaming(term, old_to_new, terms))
        .collect()
}

pub fn direct_rule_terms<C: Clone>(nf: &NF<C>, terms: &mut TermStore) -> Option<(TermId, TermId)> {
    if nf.match_pats.len() != 1 || nf.build_pats.len() != 1 {
        return None;
    }

    let lhs = nf.match_pats[0];
    let rhs = nf.build_pats[0];
    let rhs_map = &nf.cached_rhs_map;

    let rhs_direct = crate::matching::transform_vars(rhs, terms, |j| {
        TermId::inline_var(rhs_map[j])
    });
    Some((lhs, rhs_direct))
}

pub fn format_nf<C: Clone + ConstraintDisplay>(
    nf: &NF<C>,
    terms: &mut TermStore,
    symbols: &SymbolStore,
) -> Result<String, String> {
    if nf.match_pats.is_empty() && nf.build_pats.is_empty() {
        return Ok("$0 -> $0".to_string());
    }

    let (lhs, rhs) = direct_rule_terms(nf, terms)
        .ok_or_else(|| "Cannot render non-unary relation".to_string())?;
    let lhs_str = format_term(lhs, terms, symbols)?;
    let rhs_str = format_term(rhs, terms, symbols)?;
    let constraint_str = nf.drop_fresh.constraint.fmt_constraints(terms, symbols)?;
    if let Some(cs) = constraint_str {
        Ok(format!("{} {{ {} }} -> {}", lhs_str, cs, rhs_str))
    } else {
        Ok(format!("{} -> {}", lhs_str, rhs_str))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::setup;

    /// Helper: renumber variables in a single term (delegates to list version).
    fn renumber_vars(term: TermId, terms: &mut TermStore) -> (TermId, Vec<u32>) {
        let (mut result, vars) = renumber_vars_list(&[term], terms);
        (result.pop().unwrap_or(term), vars)
    }

    // ========== COLLECT VARS TESTS ==========

    #[test]
    fn collect_vars_from_single_var() {
        let (_, terms) = setup();
        let v0 = terms.var(0);
        let vars = collect_vars_ordered(v0, &terms);
        assert_eq!(vars, vec![0], "Single var should collect its index");
    }

    #[test]
    fn collect_vars_from_multiple_vars() {
        let (symbols, terms) = setup();
        let pair = symbols.intern("Pair");
        let v2 = terms.var(2);
        let v0 = terms.var(0);
        let t = terms.app2(pair, v2, v0);
        let vars = collect_vars_ordered(t, &terms);
        assert_eq!(
            vars,
            vec![2, 0],
            "Vars collected in order of first appearance"
        );
    }

    #[test]
    fn collect_vars_no_duplicates() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        // F(v0, v0) - same var twice
        let t = terms.app2(f, v0, v0);
        let vars = collect_vars_ordered(t, &terms);
        assert_eq!(vars, vec![0], "Duplicate vars should appear once");
    }

    #[test]
    fn collect_vars_nested() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let g = symbols.intern("G");
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let v2 = terms.var(2);
        // F(G(v1, v0), v2)
        let inner = terms.app2(g, v1, v0);
        let outer = terms.app2(f, inner, v2);
        let vars = collect_vars_ordered(outer, &terms);
        assert_eq!(
            vars,
            vec![1, 0, 2],
            "Nested vars in order of first appearance"
        );
    }

    #[test]
    fn collect_vars_from_ground_term() {
        let (symbols, terms) = setup();
        let zero = symbols.intern("Zero");
        let succ = symbols.intern("Succ");
        let n0 = terms.app0(zero);
        let n1 = terms.app1(succ, n0);
        let vars = collect_vars_ordered(n1, &terms);
        assert!(vars.is_empty(), "Ground term has no variables");
    }

    // ========== RENUMBER VARS TESTS ==========

    #[test]
    fn renumber_single_var() {
        let (_, mut terms) = setup();
        let v5 = terms.var(5);
        let (renumbered, mapping) = renumber_vars(v5, &mut terms);

        // Should become var(0), mapping [5]
        assert_eq!(terms.is_var(renumbered), Some(0));
        assert_eq!(mapping, vec![5]);
    }

    #[test]
    fn renumber_multiple_vars() {
        let (symbols, mut terms) = setup();
        let pair = symbols.intern("Pair");
        let v7 = terms.var(7);
        let v3 = terms.var(3);
        let t = terms.app2(pair, v7, v3);

        let (renumbered, mapping) = renumber_vars(t, &mut terms);

        // Should become Pair(var(0), var(1)), mapping [7, 3]
        let (f, children) = terms.is_app(renumbered).unwrap();
        assert_eq!(symbols.resolve(f), Some("Pair"));
        assert_eq!(terms.is_var(children[0]), Some(0));
        assert_eq!(terms.is_var(children[1]), Some(1));
        assert_eq!(mapping, vec![7, 3]);
    }

    #[test]
    fn renumber_with_repeated_vars() {
        let (symbols, mut terms) = setup();
        let f = symbols.intern("F");
        let v5 = terms.var(5);
        // F(v5, v5)
        let t = terms.app2(f, v5, v5);

        let (renumbered, mapping) = renumber_vars(t, &mut terms);

        // Should become F(var(0), var(0)), mapping [5]
        let (_, children) = terms.is_app(renumbered).unwrap();
        let c0 = terms.is_var(children[0]).unwrap();
        let c1 = terms.is_var(children[1]).unwrap();
        assert_eq!(c0, 0);
        assert_eq!(c1, 0);
        assert_eq!(mapping, vec![5]);
    }

    #[test]
    fn renumber_ground_term_unchanged() {
        let (symbols, mut terms) = setup();
        let nil = symbols.intern("Nil");
        let t = terms.app0(nil);

        let (renumbered, mapping) = renumber_vars(t, &mut terms);

        // Ground term unchanged, empty mapping
        assert_eq!(renumbered, t);
        assert!(mapping.is_empty());
    }

    // ========== APPLY VAR RENAMING TESTS ==========

    #[test]
    fn apply_renaming_single_var() {
        let (_, mut terms) = setup();
        let v0 = terms.var(0);
        // Map var 0 -> var 5
        let mapping = vec![Some(5), None, None];
        let result = apply_var_renaming(v0, &mapping, &mut terms);
        assert_eq!(terms.is_var(result), Some(5));
    }

    #[test]
    fn apply_renaming_nested() {
        let (symbols, mut terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let t = terms.app2(f, v0, v1);

        // Map var 0 -> 2, var 1 -> 3
        let mapping = vec![Some(2), Some(3)];
        let result = apply_var_renaming(t, &mapping, &mut terms);

        let (_, children) = terms.is_app(result).unwrap();
        assert_eq!(terms.is_var(children[0]), Some(2));
        assert_eq!(terms.is_var(children[1]), Some(3));
    }

    #[test]
    fn apply_renaming_preserves_ground() {
        let (symbols, mut terms) = setup();
        let nil = symbols.intern("Nil");
        let t = terms.app0(nil);

        let mapping = vec![Some(99)]; // irrelevant
        let result = apply_var_renaming(t, &mapping, &mut terms);

        assert_eq!(result, t, "Ground term unchanged by renaming");
    }

    // ========== NF FACTOR TESTS ==========

    #[test]
    fn factor_identity_rule() {
        let (_, mut terms) = setup();
        let v0 = terms.var(0);
        // Rule: x -> x (identity)
        let nf: NF<()> = NF::factor(v0, v0, (), &mut terms);

        // match_pats should be [var(0)]
        assert_eq!(nf.match_pats.len(), 1);
        assert_eq!(terms.is_var(nf.match_pats[0]), Some(0));

        // build_pats should be [var(0)]
        assert_eq!(nf.build_pats.len(), 1);
        assert_eq!(terms.is_var(nf.build_pats[0]), Some(0));

        // DropFresh should be identity on 1
        assert!(nf.drop_fresh.is_identity());
        assert_eq!(nf.drop_fresh.in_arity, 1);
    }

    #[test]
    fn factor_swap_rule() {
        let (symbols, mut terms) = setup();
        let pair = symbols.intern("Pair");
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // Rule: Pair(x, y) -> Pair(y, x)
        let lhs = terms.app2(pair, v0, v1);
        let rhs = terms.app2(pair, v1, v0);
        let nf: NF<()> = NF::factor(lhs, rhs, (), &mut terms);

        // LHS vars: [0, 1] -> normalized to [0, 1]
        // RHS vars: [1, 0] -> normalized to [0, 1] where 0 maps to original 1, 1 maps to original 0

        // match_pats: Pair(var(0), var(1))
        assert_eq!(nf.match_pats.len(), 1);
        let (f, children) = terms.is_app(nf.match_pats[0]).unwrap();
        assert_eq!(symbols.resolve(f), Some("Pair"));
        assert_eq!(terms.is_var(children[0]), Some(0));
        assert_eq!(terms.is_var(children[1]), Some(1));

        assert_eq!(nf.build_pats.len(), 1);

        // Swap: both vars are shared. The RHS var ordering puts shared vars in
        // LHS order, so rhsOrdered = [0, 1] (both shared, LHS order preserved).
        // This means normRhs = Pair(var(1), var(0)) — the swap is encoded in the
        // RHS pattern, while the DropFresh remains identity.
        assert_eq!(nf.drop_fresh.in_arity, 2);
        assert_eq!(nf.drop_fresh.out_arity, 2);
        assert!(nf.drop_fresh.is_identity(), "Swap is in patterns, not DropFresh");

        // Verify the build pattern encodes the swap
        let (bf, bchildren) = terms.is_app(nf.build_pats[0]).unwrap();
        assert_eq!(symbols.resolve(bf), Some("Pair"));
        assert_eq!(terms.is_var(bchildren[0]), Some(1));
        assert_eq!(terms.is_var(bchildren[1]), Some(0));
    }

    #[test]
    fn factor_drop_var() {
        let (symbols, mut terms) = setup();
        let pair = symbols.intern("Pair");
        let fst = symbols.intern("Fst");
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // Rule: Pair(x, y) -> Fst(x) (drops y)
        let lhs = terms.app2(pair, v0, v1);
        let rhs = terms.app1(fst, v0);
        let nf: NF<()> = NF::factor(lhs, rhs, (), &mut terms);

        // LHS has 2 vars, RHS has 1 var (shared with LHS)
        assert_eq!(nf.drop_fresh.in_arity, 2);
        assert_eq!(nf.drop_fresh.out_arity, 1);

        // DropFresh should map LHS position 0 to RHS position 0
        assert_eq!(nf.drop_fresh.map.as_slice(), &[(0, 0)]);
    }

    #[test]
    fn factor_fresh_var() {
        let (symbols, mut terms) = setup();
        let unit = symbols.intern("Unit");
        let pair = symbols.intern("Pair");
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // Rule: Unit -> Pair(x, y) (introduces fresh vars)
        let lhs = terms.app0(unit);
        let rhs = terms.app2(pair, v0, v1);
        let nf: NF<()> = NF::factor(lhs, rhs, (), &mut terms);

        // LHS has 0 vars, RHS has 2 fresh vars
        assert_eq!(nf.drop_fresh.in_arity, 0);
        assert_eq!(nf.drop_fresh.out_arity, 2);

        // DropFresh is disconnect (no shared vars)
        assert!(nf.drop_fresh.is_disconnect());
    }

    #[test]
    fn factor_nested_pattern() {
        let (symbols, mut terms) = setup();
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // Rule: B(A(x), y) -> B(x, y) (peels off A)
        let a_x = terms.app1(a, v0);
        let lhs = terms.app2(b, a_x, v1);
        let rhs = terms.app2(b, v0, v1);

        let nf: NF<()> = NF::factor(lhs, rhs, (), &mut terms);

        // Both sides have vars [0, 1], all shared
        assert_eq!(nf.drop_fresh.in_arity, 2);
        assert_eq!(nf.drop_fresh.out_arity, 2);
        assert!(nf.drop_fresh.is_identity());
    }

    #[test]
    fn factor_ground_to_ground() {
        let (symbols, mut terms) = setup();
        let true_sym = symbols.intern("True");
        let false_sym = symbols.intern("False");

        // Rule: True -> False (no vars)
        let lhs = terms.app0(true_sym);
        let rhs = terms.app0(false_sym);
        let nf: NF<()> = NF::factor(lhs, rhs, (), &mut terms);

        // No vars on either side
        assert_eq!(nf.drop_fresh.in_arity, 0);
        assert_eq!(nf.drop_fresh.out_arity, 0);
        assert!(nf.drop_fresh.is_identity()); // identity on 0 elements
    }

    // ========== NF CONSTRUCTION TESTS ==========

    #[test]
    fn nf_new_creates_valid_nf() {
        let (_, terms) = setup();
        let v0 = terms.var(0);
        let drop_fresh: DropFresh<()> = DropFresh::identity(1);

        let nf = NF::new(smallvec::smallvec![v0], drop_fresh, smallvec::smallvec![v0]);

        assert_eq!(nf.match_pats.len(), 1);
        assert_eq!(nf.build_pats.len(), 1);
        assert!(nf.drop_fresh.is_identity());
    }

    // ========== EDGE CASES ==========

    #[test]
    fn collect_vars_deeply_nested() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");

        // Build F(F(F(F(v0))))
        let v0 = terms.var(0);
        let f1 = terms.app1(f, v0);
        let f2 = terms.app1(f, f1);
        let f3 = terms.app1(f, f2);
        let f4 = terms.app1(f, f3);

        let vars = collect_vars_ordered(f4, &terms);
        assert_eq!(vars, vec![0]);
    }

    #[test]
    fn collect_vars_wide_term() {
        let (symbols, terms) = setup();
        let tuple = symbols.intern("Tuple");

        // Build Tuple(v3, v1, v4, v1, v5, v9)
        let children: SmallVec<[TermId; 4]> = [3, 1, 4, 1, 5, 9]
            .into_iter()
            .map(|i| terms.var(i))
            .collect();
        let t = terms.app(tuple, children);

        let vars = collect_vars_ordered(t, &terms);
        assert_eq!(
            vars,
            vec![3, 1, 4, 5, 9],
            "Unique vars in order of first appearance"
        );
    }
}
