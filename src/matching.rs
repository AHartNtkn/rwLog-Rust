use crate::subst::{apply_subst, Subst};
use crate::symbol::FuncId;
use crate::term::{Term, TermId, TermReadGuard, TermStore};
use hashbrown::HashMap;
use smallvec::SmallVec;
use std::cell::RefCell;

#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};

/// Thread-local memoization cache for `shift_term` results.
///
/// Keyed by a packed u64 encoding `(TermId, offset)`. Invalidated when the
/// TermStore generation changes (indicating a new engine run with a fresh store).
struct ShiftCache {
    generation: u64,
    entries: HashMap<u64, TermId>,
}

impl ShiftCache {
    fn new() -> Self {
        Self {
            generation: u64::MAX,
            entries: HashMap::new(),
        }
    }

    /// Pack a (TermId, offset) pair into a single u64 cache key.
    #[inline(always)]
    fn pack_key(term: TermId, offset: u32) -> u64 {
        (term.raw() as u64) << 32 | offset as u64
    }
}

thread_local! {
    static SHIFT_CACHE: RefCell<ShiftCache> = RefCell::new(ShiftCache::new());
}

/// Extend an existing substitution by unifying `t1` and `t2` under the read
/// guard. Returns `true` on success, `false` if the terms are incompatible
/// (functor mismatch, arity mismatch, or occurs-check failure).
///
/// Uses an explicit worklist to avoid recursion.
pub(crate) fn unify_into(
    subst: &mut Subst,
    t1: TermId,
    t2: TermId,
    guard: &TermReadGuard<'_>,
) -> bool {
    let mut worklist: SmallVec<[(TermId, TermId); 32]> = SmallVec::new();
    worklist.push((t1, t2));

    while let Some((a, b)) = worklist.pop() {
        let a_deref = deref_locked(a, subst, guard);
        let b_deref = deref_locked(b, subst, guard);

        if a_deref == b_deref {
            continue;
        }

        enum TermKind {
            Var(u32),
            App(FuncId),
            InlineNullary(u32),
            Invalid,
        }

        let classify = |tid: TermId| -> TermKind {
            if tid.is_inline_var() {
                return TermKind::Var(tid.inline_var_index());
            }
            if tid.is_inline_nullary() {
                return TermKind::InlineNullary(tid.inline_nullary_func_raw());
            }
            match guard.get(tid) {
                Some(Term::Var(idx)) => TermKind::Var(*idx),
                Some(Term::App(f, _)) => TermKind::App(*f),
                None => TermKind::Invalid,
            }
        };
        let a_kind = classify(a_deref);
        let b_kind = classify(b_deref);

        match (a_kind, b_kind) {
            (TermKind::Var(idx_a), TermKind::Var(idx_b)) => {
                if idx_a < idx_b {
                    subst.bind(idx_b, a_deref);
                } else {
                    subst.bind(idx_a, b_deref);
                }
            }
            (TermKind::Var(idx), TermKind::App(_) | TermKind::InlineNullary(_)) => {
                if occurs_locked(idx, b_deref, subst, guard) {
                    #[cfg(feature = "tracing")]
                    trace!(var = idx, "unify_occurs_check_failed");
                    return false;
                }
                subst.bind(idx, b_deref);
            }
            (TermKind::App(_) | TermKind::InlineNullary(_), TermKind::Var(idx)) => {
                if occurs_locked(idx, a_deref, subst, guard) {
                    #[cfg(feature = "tracing")]
                    trace!(var = idx, "unify_occurs_check_failed");
                    return false;
                }
                subst.bind(idx, a_deref);
            }
            (TermKind::InlineNullary(f1), TermKind::InlineNullary(f2)) => {
                if f1 != f2 {
                    #[cfg(feature = "tracing")]
                    trace!("unify_functor_mismatch");
                    return false;
                }
            }
            (TermKind::App(f1), TermKind::App(f2)) => {
                if f1 != f2 {
                    #[cfg(feature = "tracing")]
                    trace!("unify_functor_mismatch");
                    return false;
                }
                if let (Some(Term::App(_, ac)), Some(Term::App(_, bc))) =
                    (guard.get(a_deref), guard.get(b_deref))
                {
                    if ac.len() != bc.len() {
                        #[cfg(feature = "tracing")]
                        trace!("unify_arity_mismatch");
                        return false;
                    }
                    for (c1, c2) in ac.iter().zip(bc.iter()) {
                        worklist.push((*c1, *c2));
                    }
                }
            }
            (TermKind::InlineNullary(_), TermKind::App(..))
            | (TermKind::App(..), TermKind::InlineNullary(_)) => {
                #[cfg(feature = "tracing")]
                trace!("unify_arity_mismatch");
                return false;
            }
            _ => {
                #[cfg(feature = "tracing")]
                trace!("unify_invalid_term");
                return false;
            }
        }
    }

    true
}

/// Match two terms in a shared namespace, returning a most general matching
/// substitution if successful. Returns None if the terms cannot match.
///
/// This computes a combined substitution over the shared namespace; callers
/// that need per-side substitutions should split and resolve it.
pub(crate) fn match_terms_combined(t1: TermId, t2: TermId, terms: &TermStore) -> Option<Subst> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!("match_terms", ?t1, ?t2).entered();

    let guard = terms.read_lock();
    let mut subst = Subst::new();
    if unify_into(&mut subst, t1, t2, &guard) {
        #[cfg(feature = "tracing")]
        trace!(bindings = subst.len(), "match_success");
        Some(subst)
    } else {
        None
    }
}

/// Match two terms where the right-side (`t2`) variables are virtually shifted.
///
/// `shifted_vars[j]` must be the TermId for `Var(j + offset)` for every variable
/// index `j` that appears in `t2`. These are pre-created by the caller.
///
/// This function avoids the full tree walk that `apply_subst_shifted` would
/// perform to produce a shifted copy of `t2`. Instead, it traverses `t2`
/// directly, shifting variables on-the-fly using `shifted_vars`. For App
/// nodes, children that contain variables are shifted lazily only when needed
/// (i.e., when a left-side variable would be bound to a right-side subtree).
///
/// Requires `&mut TermStore` because materializing shifted App subtrees may
/// need to intern new terms.
///
/// When `shifted_vars` is empty, behaves identically to `match_terms_combined`.
pub(crate) fn match_terms_combined_shifted(
    t1: TermId,
    t2: TermId,
    shifted_vars: &[TermId],
    terms: &mut TermStore,
) -> Option<Subst> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!("match_terms", ?t1, ?t2).entered();

    if shifted_vars.is_empty() {
        return match_terms_combined(t1, t2, terms);
    }

    let mut subst = Subst::new();
    // Worklist entries: (left_term, right_term, right_is_raw).
    // `right_is_raw` is true when the right term is from the unshifted
    // namespace and its variables need virtual shifting.
    let mut worklist: SmallVec<[(TermId, TermId, bool); 32]> = SmallVec::new();
    worklist.push((t1, t2, true));

    while let Some((a, b, b_raw)) = worklist.pop() {
        // Dereference left side through the substitution.
        let a_deref = deref_unlocked(a, &subst, terms);

        // Dereference right side: if raw, virtually shift the variable first.
        let b_deref = if b_raw {
            deref_shifted_unlocked(b, shifted_vars, &subst, terms)
        } else {
            deref_unlocked(b, &subst, terms)
        };

        // Fast equality check: skip if both sides resolve to the same TermId.
        // When b_raw is true and b was an App (deref_shifted returns Apps as-is),
        // b_deref == a_deref does NOT mean they are semantically equal because
        // the right-side's children still need shifting. Only skip when:
        // - b_raw is false (right side already in shared namespace), OR
        // - b_raw is true but b_deref was obtained by shifting a Var (b_deref != b,
        //   meaning deref went through shifted_vars and then subst), OR
        // - both terms are ground (shifting doesn't affect ground terms).
        if a_deref == b_deref && (!b_raw || b_deref != b || a_deref.is_ground()) {
            continue;
        }

        // Classify both terms without cloning children.
        // Handle inline TermIds directly.
        enum TermKind {
            Var(u32),
            App(FuncId),
            InlineNullary(u32),
            Invalid,
        }

        let classify_unlocked = |tid: TermId, terms_ref: &mut TermStore| -> TermKind {
            if tid.is_inline_var() {
                return TermKind::Var(tid.inline_var_index());
            }
            if tid.is_inline_nullary() {
                return TermKind::InlineNullary(tid.inline_nullary_func_raw());
            }
            match terms_ref.get_unlocked(tid) {
                Some(Term::Var(idx)) => TermKind::Var(*idx),
                Some(Term::App(f, _)) => TermKind::App(*f),
                None => TermKind::Invalid,
            }
        };
        let a_kind = classify_unlocked(a_deref, terms);
        let b_kind = classify_unlocked(b_deref, terms);

        match (a_kind, b_kind) {
            (TermKind::Var(idx_a), TermKind::Var(idx_b)) => {
                if idx_a < idx_b {
                    subst.bind(idx_b, a_deref);
                } else {
                    subst.bind(idx_a, b_deref);
                }
            }
            (TermKind::Var(idx), TermKind::App(_) | TermKind::InlineNullary(_)) => {
                // When binding a left-side Var to a right-side subtree,
                // materialize the shifted version if the subtree is raw.
                let b_shifted = if b_raw && b_deref == b && !b_deref.is_inline_nullary() {
                    shift_term(b, shifted_vars, terms)
                } else {
                    b_deref
                };
                if occurs_unlocked(idx, b_shifted, &subst, terms) {
                    return None;
                }
                subst.bind(idx, b_shifted);
            }
            (TermKind::App(_) | TermKind::InlineNullary(_), TermKind::Var(idx)) => {
                if occurs_unlocked(idx, a_deref, &subst, terms) {
                    return None;
                }
                subst.bind(idx, a_deref);
            }
            (TermKind::InlineNullary(f1), TermKind::InlineNullary(f2)) => {
                if f1 != f2 {
                    #[cfg(feature = "tracing")]
                    trace!("match_functor_mismatch");
                    return None;
                }
            }
            (TermKind::App(f1), TermKind::App(f2)) => {
                if f1 != f2 {
                    #[cfg(feature = "tracing")]
                    trace!("match_functor_mismatch");
                    return None;
                }
                let children_raw = b_raw && b_deref == b;
                let (ac, bc) = {
                    let nodes = terms.nodes.get_mut();
                    let a_children = match nodes.get(a_deref.index()) {
                        Some(Term::App(_, c)) => c.clone(),
                        _ => return None,
                    };
                    let b_children = match nodes.get(b_deref.index()) {
                        Some(Term::App(_, c)) => c.clone(),
                        _ => return None,
                    };
                    (a_children, b_children)
                };
                if ac.len() != bc.len() {
                    #[cfg(feature = "tracing")]
                    trace!("match_arity_mismatch");
                    return None;
                }
                for (c1, c2) in ac.iter().zip(bc.iter()) {
                    worklist.push((*c1, *c2, children_raw));
                }
            }
            (TermKind::InlineNullary(_), TermKind::App(..))
            | (TermKind::App(..), TermKind::InlineNullary(_)) => {
                #[cfg(feature = "tracing")]
                trace!("match_arity_mismatch");
                return None;
            }
            _ => {
                #[cfg(feature = "tracing")]
                trace!("match_invalid_term");
                return None;
            }
        }
    }

    #[cfg(feature = "tracing")]
    trace!(bindings = subst.len(), "match_success");

    Some(subst)
}

/// Match two terms where left-side variables are renamed via `left_rhs_map`
/// and right-side variables are virtually shifted via `shifted_vars`.
///
/// This is used in compose_nf to avoid eagerly applying `apply_var_renaming_list`
/// to the a-side build patterns. Instead, the renaming is applied inline during
/// matching: when encountering `Var(idx)` on the left, it is treated as
/// `Var(left_rhs_map[idx])`.
///
/// This function is only called on the fast path where subst starts empty and
/// left/right variables are in disjoint namespaces after renaming.
pub(crate) fn match_terms_combined_shifted_with_left_renaming(
    t1: TermId,
    t2: TermId,
    left_rhs_map: &[u32],
    shifted_vars: &[TermId],
    terms: &mut TermStore,
) -> Option<Subst> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!("match_terms_left_rename", ?t1, ?t2).entered();

    let mut subst = Subst::new();
    // Worklist entries: (left_term, right_term, left_is_raw, right_is_raw).
    // `left_is_raw` means the left term's variables need renaming via left_rhs_map.
    // `right_is_raw` means the right term's variables need shifting via shifted_vars.
    let mut worklist: SmallVec<[(TermId, TermId, bool, bool); 32]> = SmallVec::new();
    let use_right_shift = !shifted_vars.is_empty();
    worklist.push((t1, t2, true, use_right_shift));

    while let Some((a, b, a_raw, b_raw)) = worklist.pop() {
        // Dereference left side: if raw, rename the variable first.
        let a_deref = if a_raw {
            deref_left_renamed_unlocked(a, left_rhs_map, &subst, terms)
        } else {
            deref_unlocked(a, &subst, terms)
        };

        // Dereference right side: if raw, virtually shift the variable first.
        let b_deref = if b_raw {
            deref_shifted_unlocked(b, shifted_vars, &subst, terms)
        } else {
            deref_unlocked(b, &subst, terms)
        };

        // Fast equality check (same logic as match_terms_combined_shifted).
        // For left raw: if a_deref != a, the var was renamed and dereffed through subst,
        // so equality is valid. If a_deref == a and it's an App, children still need
        // renaming, so we can't skip.
        let skip_left = !a_raw || a_deref != a || a_deref.is_ground();
        let skip_right = !b_raw || b_deref != b || b_deref.is_ground();
        if a_deref == b_deref && skip_left && skip_right {
            continue;
        }

        // Classify both terms without cloning children.
        // Handle inline TermIds directly.
        enum TermKind {
            Var(u32),
            App(FuncId),
            InlineNullary(u32),
            Invalid,
        }

        let classify_unlocked2 = |tid: TermId, terms_ref: &mut TermStore| -> TermKind {
            if tid.is_inline_var() {
                return TermKind::Var(tid.inline_var_index());
            }
            if tid.is_inline_nullary() {
                return TermKind::InlineNullary(tid.inline_nullary_func_raw());
            }
            match terms_ref.get_unlocked(tid) {
                Some(Term::Var(idx)) => TermKind::Var(*idx),
                Some(Term::App(f, _)) => TermKind::App(*f),
                None => TermKind::Invalid,
            }
        };
        let a_kind = classify_unlocked2(a_deref, terms);
        let b_kind = classify_unlocked2(b_deref, terms);

        match (a_kind, b_kind) {
            (TermKind::Var(idx_a), TermKind::Var(idx_b)) => {
                if idx_a < idx_b {
                    subst.bind(idx_b, a_deref);
                } else {
                    subst.bind(idx_a, b_deref);
                }
            }
            (TermKind::Var(idx), TermKind::App(_) | TermKind::InlineNullary(_)) => {
                let b_shifted = if b_raw && b_deref == b && !b_deref.is_inline_nullary() {
                    shift_term(b, shifted_vars, terms)
                } else {
                    b_deref
                };
                if occurs_unlocked(idx, b_shifted, &subst, terms) {
                    return None;
                }
                subst.bind(idx, b_shifted);
            }
            (TermKind::App(_) | TermKind::InlineNullary(_), TermKind::Var(idx)) => {
                let a_renamed = if a_raw && a_deref == a && !a_deref.is_inline_nullary() {
                    rename_term(a, left_rhs_map, terms)
                } else {
                    a_deref
                };
                if occurs_unlocked(idx, a_renamed, &subst, terms) {
                    return None;
                }
                subst.bind(idx, a_renamed);
            }
            (TermKind::InlineNullary(f1), TermKind::InlineNullary(f2)) => {
                if f1 != f2 {
                    #[cfg(feature = "tracing")]
                    trace!("match_functor_mismatch");
                    return None;
                }
            }
            (TermKind::App(f1), TermKind::App(f2)) => {
                if f1 != f2 {
                    #[cfg(feature = "tracing")]
                    trace!("match_functor_mismatch");
                    return None;
                }
                let children_a_raw = a_raw && a_deref == a;
                let children_b_raw = b_raw && b_deref == b;
                let (ac, bc) = {
                    let nodes = terms.nodes.get_mut();
                    let a_children = match nodes.get(a_deref.index()) {
                        Some(Term::App(_, c)) => c.clone(),
                        _ => return None,
                    };
                    let b_children = match nodes.get(b_deref.index()) {
                        Some(Term::App(_, c)) => c.clone(),
                        _ => return None,
                    };
                    (a_children, b_children)
                };
                if ac.len() != bc.len() {
                    #[cfg(feature = "tracing")]
                    trace!("match_arity_mismatch");
                    return None;
                }
                for (c1, c2) in ac.iter().zip(bc.iter()) {
                    worklist.push((*c1, *c2, children_a_raw, children_b_raw));
                }
            }
            (TermKind::InlineNullary(_), TermKind::App(..))
            | (TermKind::App(..), TermKind::InlineNullary(_)) => {
                #[cfg(feature = "tracing")]
                trace!("match_arity_mismatch");
                return None;
            }
            _ => {
                #[cfg(feature = "tracing")]
                trace!("match_invalid_term");
                return None;
            }
        }
    }

    #[cfg(feature = "tracing")]
    trace!(bindings = subst.len(), "match_success");

    Some(subst)
}

/// Dereference a "raw" (unrenamed) left-side term through variable renaming
/// and then through the substitution, using lock-free access.
///
/// If the term is `Var(j)`, maps it to `Var(left_rhs_map[j])` before looking
/// up in the substitution. If the term is an App, returns it as-is (children
/// will be processed with left_raw=true in the worklist).
#[inline]
fn deref_left_renamed_unlocked(
    term: TermId,
    left_rhs_map: &[u32],
    subst: &Subst,
    terms: &mut TermStore,
) -> TermId {
    // Extract variable index: check inline var first, then store ref.
    let idx = if term.is_inline_var() {
        term.inline_var_index()
    } else if term.is_inline_nullary() {
        return term; // Nullary constant: return as-is.
    } else {
        // Store ref: check if it's a variable.
        let nodes = terms.nodes.get_mut();
        match nodes.get(term.index()) {
            Some(Term::Var(idx)) => *idx,
            _ => return term, // App or invalid: return as-is
        }
    };

    let j = idx as usize;
    debug_assert!(
        j < left_rhs_map.len(),
        "var index {} exceeds left_rhs_map length {}",
        j,
        left_rhs_map.len()
    );
    let renamed_idx = left_rhs_map[j];

    // Check if the subst has a binding for this renamed index.
    match subst.get(renamed_idx) {
        Some(bound) => {
            // Follow substitution chain from the bound term.
            let nodes = terms.nodes.get_mut();
            let mut current = bound;
            loop {
                if current.is_inline_var() {
                    match subst.get(current.inline_var_index()) {
                        Some(next) => current = next,
                        None => return current,
                    }
                    continue;
                }
                if current.is_inline() {
                    return current;
                }
                match nodes.get(current.index()) {
                    Some(Term::Var(vidx)) => match subst.get(*vidx) {
                        Some(next) => current = next,
                        None => return current,
                    },
                    _ => return current,
                }
            }
        }
        None => {
            // Not bound — create a TermId for Var(renamed_idx).
            terms.var_unlocked(renamed_idx)
        }
    }
}

/// Rename all variables in a term using the left_rhs_map.
/// This is the materialization counterpart of deref_left_renamed_unlocked,
/// called only when binding a right-side variable to a left-side subtree.
fn rename_term(term: TermId, left_rhs_map: &[u32], terms: &mut TermStore) -> TermId {
    if term.is_ground() {
        return term;
    }

    enum Work {
        Visit(TermId),
        BuildApp(TermId, FuncId, usize),
    }

    let mut work_stack: SmallVec<[Work; 16]> = SmallVec::new();
    let mut result_stack: SmallVec<[TermId; 16]> = SmallVec::new();

    work_stack.push(Work::Visit(term));

    while let Some(item) = work_stack.pop() {
        match item {
            Work::BuildApp(orig_tid, func, n) => {
                let start = result_stack.len() - n;
                let all_same = {
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
                // Fast path: inline variable.
                if tid.is_inline_var() {
                    let j = tid.inline_var_index() as usize;
                    debug_assert!(j < left_rhs_map.len());
                    result_stack.push(terms.var_unlocked(left_rhs_map[j]));
                    continue;
                }
                // Store ref (non-ground).
                let var_action: Option<u32> = {
                    let nodes = terms.nodes.get_mut();
                    match nodes.get(tid.index()) {
                        Some(Term::Var(idx)) => {
                            let j = *idx as usize;
                            debug_assert!(j < left_rhs_map.len());
                            Some(left_rhs_map[j])
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
                    }
                };
                if let Some(renamed_idx) = var_action {
                    result_stack.push(terms.var_unlocked(renamed_idx));
                }
            }
        }
    }

    debug_assert_eq!(result_stack.len(), 1);
    result_stack.pop().unwrap()
}

/// Split a combined substitution into (left, right) parts, resolving each
/// binding through the combined substitution so that applying each part
/// independently yields equal terms.
pub(crate) fn split_match_subst(
    combined: &Subst,
    right_offset: u32,
    terms: &mut TermStore,
) -> (Subst, Subst) {
    let mut left = Subst::new();
    let mut right = Subst::new();
    for (var, _term) in combined.iter() {
        let resolved = apply_subst(terms.var(var), combined, terms);
        if resolved == terms.var(var) {
            continue;
        }
        if var < right_offset {
            left.bind(var, resolved);
        } else {
            right.bind(var, resolved);
        }
    }
    (left, right)
}

/// Match two terms whose variable namespaces are disjoint.
/// `right_offset` must be greater than any variable index on the left side.
pub fn match_terms_disjoint(
    left: TermId,
    right: TermId,
    right_offset: u32,
    terms: &mut TermStore,
) -> Option<(Subst, Subst)> {
    let combined = match_terms_combined(left, right, terms)?;
    Some(split_match_subst(&combined, right_offset, terms))
}

/// Dereference a term through the substitution using a pre-acquired read lock.
#[inline]
fn deref_locked(term: TermId, subst: &Subst, guard: &TermReadGuard<'_>) -> TermId {
    let mut current = term;
    loop {
        if current.is_inline_var() {
            match subst.get(current.inline_var_index()) {
                Some(bound) => current = bound,
                None => return current,
            }
            continue;
        }
        // Inline nullary or non-inline: try guard
        match guard.get(current) {
            Some(Term::Var(idx)) => match subst.get(*idx) {
                Some(bound) => current = bound,
                None => return current,
            },
            _ => return current,
        }
    }
}

/// Dereference a term through the substitution using lock-free access.
/// Requires exclusive (`&mut`) access to the TermStore.
#[inline]
fn deref_unlocked(term: TermId, subst: &Subst, terms: &mut TermStore) -> TermId {
    let nodes = terms.nodes.get_mut();
    let mut current = term;
    loop {
        if current.is_inline_var() {
            match subst.get(current.inline_var_index()) {
                Some(bound) => current = bound,
                None => return current,
            }
            continue;
        }
        if current.is_inline() {
            // Inline nullary - not a variable, stop.
            return current;
        }
        match nodes.get(current.index()) {
            Some(Term::Var(idx)) => match subst.get(*idx) {
                Some(bound) => current = bound,
                None => return current,
            },
            _ => return current,
        }
    }
}

/// Dereference a "raw" (unshifted) right-side term through virtual shifting
/// and then through the substitution, using lock-free access.
///
/// If the term is `Var(j)`, maps it to `shifted_vars[j]` (i.e., `Var(j + offset)`)
/// before looking up in the substitution. If the term is an App, returns it as-is
/// (children will be processed with raw=true in the worklist).
#[inline]
fn deref_shifted_unlocked(
    term: TermId,
    shifted_vars: &[TermId],
    subst: &Subst,
    terms: &mut TermStore,
) -> TermId {
    // Check for inline var first (most common case for raw terms).
    if term.is_inline_var() {
        let j = term.inline_var_index() as usize;
        debug_assert!(
            j < shifted_vars.len(),
            "var index {} exceeds shifted_vars length {}",
            j,
            shifted_vars.len()
        );
        let shifted = shifted_vars[j];
        // Now dereference through the substitution from the shifted var.
        let nodes = terms.nodes.get_mut();
        let mut current = shifted;
        loop {
            if current.is_inline_var() {
                match subst.get(current.inline_var_index()) {
                    Some(bound) => current = bound,
                    None => return current,
                }
                continue;
            }
            if current.is_inline() {
                return current;
            }
            match nodes.get(current.index()) {
                Some(Term::Var(vidx)) => match subst.get(*vidx) {
                    Some(bound) => current = bound,
                    None => return current,
                },
                _ => return current,
            }
        }
    }
    // Inline nullary: return as-is (not a variable).
    if term.is_inline_nullary() {
        return term;
    }
    // Store ref: check if it's a variable.
    let nodes = terms.nodes.get_mut();
    match nodes.get(term.index()) {
        Some(Term::Var(idx)) => {
            let j = *idx as usize;
            debug_assert!(
                j < shifted_vars.len(),
                "var index {} exceeds shifted_vars length {}",
                j,
                shifted_vars.len()
            );
            let shifted = shifted_vars[j];
            let mut current = shifted;
            loop {
                if current.is_inline_var() {
                    match subst.get(current.inline_var_index()) {
                        Some(bound) => current = bound,
                        None => return current,
                    }
                    continue;
                }
                if current.is_inline() {
                    return current;
                }
                match nodes.get(current.index()) {
                    Some(Term::Var(vidx)) => match subst.get(*vidx) {
                        Some(bound) => current = bound,
                        None => return current,
                    },
                    _ => return current,
                }
            }
        }
        _ => term,
    }
}

/// Shift all variables in a term using the pre-created shifted_vars mapping.
/// This is equivalent to `apply_subst_shifted(term, &empty_subst, offset, shifted_vars, terms)`
/// but called only when we actually need the shifted version (i.e., when binding
/// a left-side variable to a right-side subtree).
///
/// Results for compound (non-inline, non-ground) terms are memoized in a
/// thread-local cache keyed by `(TermId, offset)`, invalidated by TermStore
/// generation. This avoids redundant tree walks and interning when the same
/// compound term is shifted by the same offset repeatedly.
fn shift_term(term: TermId, shifted_vars: &[TermId], terms: &mut TermStore) -> TermId {
    if term.is_ground() {
        return term;
    }

    // Inline vars are O(1) — just a lookup, no need to cache.
    if term.is_inline_var() {
        let j = term.inline_var_index() as usize;
        debug_assert!(
            j < shifted_vars.len(),
            "var index {} exceeds shifted_vars length {}",
            j,
            shifted_vars.len()
        );
        return shifted_vars[j];
    }

    // Derive the offset from shifted_vars[0] = Var(0 + offset).
    // shifted_vars is always non-empty here (callers guard on is_empty).
    let offset = shifted_vars[0].inline_var_index();
    let gen = terms.generation();
    let cache_key = ShiftCache::pack_key(term, offset);

    // Check the thread-local cache.
    let cached = SHIFT_CACHE.with(|c| {
        let cache = c.borrow();
        if cache.generation == gen {
            cache.entries.get(&cache_key).copied()
        } else {
            None
        }
    });
    if let Some(result) = cached {
        return result;
    }

    let result = shift_term_uncached(term, shifted_vars, terms);

    // Store in cache (only for non-trivial shifts where the result differs).
    if result != term {
        SHIFT_CACHE.with(|c| {
            let mut cache = c.borrow_mut();
            if cache.generation != gen {
                cache.entries.clear();
                cache.generation = gen;
            }
            cache.entries.insert(cache_key, result);
        });
    }

    result
}

/// Inner implementation of shift_term without caching. Performs the actual
/// stack-based tree walk and variable substitution.
fn shift_term_uncached(term: TermId, shifted_vars: &[TermId], terms: &mut TermStore) -> TermId {
    // Use a stack-based approach similar to apply_subst_core.
    enum Work {
        Visit(TermId),
        BuildApp(TermId, FuncId, usize),
    }

    let mut work_stack: SmallVec<[Work; 16]> = SmallVec::new();
    let mut result_stack: SmallVec<[TermId; 16]> = SmallVec::new();

    work_stack.push(Work::Visit(term));

    while let Some(item) = work_stack.pop() {
        match item {
            Work::BuildApp(orig_tid, func, n) => {
                let start = result_stack.len() - n;
                let all_same = {
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
                // Fast path: inline variable.
                if tid.is_inline_var() {
                    let j = tid.inline_var_index() as usize;
                    debug_assert!(
                        j < shifted_vars.len(),
                        "var index {} exceeds shifted_vars length {}",
                        j,
                        shifted_vars.len()
                    );
                    result_stack.push(shifted_vars[j]);
                    continue;
                }
                // Store ref (non-ground).
                let nodes = terms.nodes.get_mut();
                match nodes.get(tid.index()) {
                    Some(Term::Var(idx)) => {
                        let j = *idx as usize;
                        debug_assert!(
                            j < shifted_vars.len(),
                            "var index {} exceeds shifted_vars length {}",
                            j,
                            shifted_vars.len()
                        );
                        result_stack.push(shifted_vars[j]);
                    }
                    Some(Term::App(_, children)) if children.is_empty() => {
                        result_stack.push(tid);
                    }
                    Some(Term::App(f, children)) => {
                        let func = *f;
                        let n = children.len();
                        work_stack.push(Work::BuildApp(tid, func, n));
                        for i in (0..n).rev() {
                            work_stack.push(Work::Visit(children[i]));
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

/// Generate an occurs-check function parameterized by term access method.
///
/// Both `occurs_locked` (read-lock guard) and `occurs_unlocked` (exclusive
/// `&mut TermStore`) share identical logic. The only differences are:
/// - how to query the variable range of a store-ref term
/// - how to dereference a variable through the substitution
/// - how to look up a TermId in the store
///
/// This macro emits a monomorphic function for each variant with zero
/// abstraction overhead. The `$var_range`, `$deref`, and `$get_term`
/// parameters are expression fragments that are spliced directly into the
/// generated code, avoiding closure borrow conflicts.
macro_rules! occurs_check_impl {
    (
        $fn_name:ident ( $store_param:ident : $store_ty:ty ),
        var_range($vr_tid:ident) => $var_range:expr,
        deref($d_tid:ident, $d_subst:ident) => $deref:expr,
        get_term($g_tid:ident) => $get_term:expr $(,)?
    ) => {
        fn $fn_name(var: u32, term: TermId, subst: &Subst, $store_param: $store_ty) -> bool {
            // Fast rejection: if the initial term is ground, var cannot appear.
            if term.is_ground() {
                return false;
            }
            // Fast rejection: if the initial term is a non-ground store ref,
            // check its variable range. If var is outside the structural range
            // AND no variable in the structural range is bound in subst,
            // then var cannot appear even after substitution.
            if term.is_store_ref() {
                let $vr_tid = term;
                if let Some((min_v, max_v)) = $var_range {
                    if var < min_v || var > max_v {
                        let range_size = max_v.saturating_sub(min_v);
                        if range_size <= 64 {
                            let mut reachable = false;
                            for v in min_v..=max_v {
                                if subst.get(v).is_some() {
                                    reachable = true;
                                    break;
                                }
                            }
                            if !reachable {
                                return false;
                            }
                        }
                    }
                }
            }

            let mut stack: SmallVec<[TermId; 16]> = SmallVec::new();
            stack.push(term);

            while let Some(t) = stack.pop() {
                // Skip ground terms without even dereferencing.
                if t.is_ground() {
                    continue;
                }
                let ($d_tid, $d_subst) = (t, subst);
                let t_deref = $deref;
                if t_deref.is_inline_var() {
                    if t_deref.inline_var_index() == var {
                        return true;
                    }
                    continue;
                }
                // After deref, if result is ground, skip.
                if t_deref.is_ground() {
                    continue;
                }
                if t_deref.is_inline_nullary() {
                    continue;
                }
                let $g_tid = t_deref;
                match $get_term {
                    Some(Term::Var(idx)) => {
                        if *idx == var {
                            return true;
                        }
                    }
                    Some(Term::App(_, children)) => {
                        for child in children.iter() {
                            if !child.is_ground() {
                                stack.push(*child);
                            }
                        }
                    }
                    None => {}
                }
            }

            false
        }
    };
}

occurs_check_impl!(
    occurs_unlocked(terms: &mut TermStore),
    var_range(tid) => terms.var_range_unlocked(tid),
    deref(t, s) => deref_unlocked(t, s, terms),
    get_term(tid) => terms.get_unlocked(tid),
);

occurs_check_impl!(
    occurs_locked(guard: &TermReadGuard<'_>),
    var_range(tid) => guard.var_range(tid),
    deref(t, s) => deref_locked(t, s, guard),
    get_term(tid) => guard.get(tid),
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::setup;

    // ========== HAPPY PATH: IDENTICAL TERMS ==========

    #[test]
    fn match_same_var() {
        let (_, terms) = setup();
        let v0 = terms.var(0);

        let result = match_terms_combined(v0, v0, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert!(subst.is_empty(), "Same var should produce empty subst");
    }

    #[test]
    fn match_same_ground_term() {
        let (symbols, terms) = setup();
        let zero = symbols.intern("Zero");
        let t = terms.app0(zero);

        let result = match_terms_combined(t, t, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert!(subst.is_empty(), "Same term should produce empty subst");
    }

    #[test]
    fn match_same_complex_term() {
        let (symbols, terms) = setup();
        let cons = symbols.intern("Cons");
        let nil = symbols.intern("Nil");
        let v0 = terms.var(0);
        let nil_term = terms.app0(nil);
        let t = terms.app2(cons, v0, nil_term);

        let result = match_terms_combined(t, t, &terms);
        assert!(result.is_some());
    }

    // ========== HAPPY PATH: VAR vs TERM ==========

    #[test]
    fn match_var_with_ground() {
        let (symbols, terms) = setup();
        let zero = symbols.intern("Zero");
        let v0 = terms.var(0);
        let zero_term = terms.app0(zero);

        let result = match_terms_combined(v0, zero_term, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(zero_term));
    }

    #[test]
    fn match_ground_with_var() {
        let (symbols, terms) = setup();
        let zero = symbols.intern("Zero");
        let v0 = terms.var(0);
        let zero_term = terms.app0(zero);

        let result = match_terms_combined(zero_term, v0, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(zero_term));
    }

    #[test]
    fn match_var_with_var() {
        let (_, terms) = setup();
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        let result = match_terms_combined(v0, v1, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        // One should be bound to the other
        assert!(subst.is_bound(0) || subst.is_bound(1));
        assert_eq!(subst.len(), 1);
    }

    #[test]
    fn match_var_with_nested_var() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let f_v1 = terms.app1(f, v1);

        let result = match_terms_combined(v0, f_v1, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(f_v1));
    }

    // ========== HAPPY PATH: COMPATIBLE CONSTRUCTORS ==========

    #[test]
    fn match_nullary_same_functor() {
        let (symbols, terms) = setup();
        let nil = symbols.intern("Nil");
        let t1 = terms.app0(nil);
        let t2 = terms.app0(nil);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(result.is_some());
    }

    #[test]
    fn match_compatible_apps() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        let a = symbols.intern("A");
        let a_term = terms.app0(a);

        // F(x) vs F(A)
        let t1 = terms.app1(f, v0);
        let t2 = terms.app1(f, a_term);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(a_term));
    }

    #[test]
    fn match_nested_compatible() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let g = symbols.intern("G");
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let a_term = terms.app0(a);
        let b_term = terms.app0(b);

        // F(G(x), y) vs F(G(A), B)
        let g_x = terms.app1(g, v0);
        let t1 = terms.app2(f, g_x, v1);

        let g_a = terms.app1(g, a_term);
        let t2 = terms.app2(f, g_a, b_term);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(a_term));
        assert_eq!(subst.get(1), Some(b_term));
    }

    #[test]
    fn match_both_sides_have_vars() {
        let (symbols, terms) = setup();
        let pair = symbols.intern("Pair");
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let a = symbols.intern("A");
        let a_term = terms.app0(a);

        // Pair(x, A) vs Pair(A, y)
        let t1 = terms.app2(pair, v0, a_term);
        let t2 = terms.app2(pair, a_term, v1);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(a_term));
        assert_eq!(subst.get(1), Some(a_term));
    }

    #[test]
    fn match_shared_var() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);

        // F(x, x) vs F(A, A) should work
        let a = symbols.intern("A");
        let a_term = terms.app0(a);
        let t1 = terms.app2(f, v0, v0);
        let t2 = terms.app2(f, a_term, a_term);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(a_term));
    }

    // ========== UNHAPPY PATH: INCOMPATIBLE CONSTRUCTORS ==========

    #[test]
    fn match_different_nullary_fails() {
        let (symbols, terms) = setup();
        let nil = symbols.intern("Nil");
        let zero = symbols.intern("Zero");
        let t1 = terms.app0(nil);
        let t2 = terms.app0(zero);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(result.is_none(), "Different functors should fail");
    }

    #[test]
    fn match_different_functors_fails() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let g = symbols.intern("G");
        let a = symbols.intern("A");
        let a_term = terms.app0(a);

        let t1 = terms.app1(f, a_term);
        let t2 = terms.app1(g, a_term);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(result.is_none(), "Different functors should fail");
    }

    #[test]
    fn match_different_arity_fails() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let a = symbols.intern("A");
        let a_term = terms.app0(a);

        let t1 = terms.app1(f, a_term);
        let t2 = terms.app2(f, a_term, a_term);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(result.is_none(), "Different arities should fail");
    }

    #[test]
    fn match_nested_conflict_fails() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let a_term = terms.app0(a);
        let b_term = terms.app0(b);

        // F(A) vs F(B)
        let t1 = terms.app1(f, a_term);
        let t2 = terms.app1(f, b_term);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(result.is_none(), "Nested conflict should fail");
    }

    #[test]
    fn match_shared_var_conflict_fails() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let a_term = terms.app0(a);
        let b_term = terms.app0(b);

        // F(x, x) vs F(A, B) should fail because x can't be both A and B
        let t1 = terms.app2(f, v0, v0);
        let t2 = terms.app2(f, a_term, b_term);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(
            result.is_none(),
            "Shared var with different values should fail"
        );
    }

    // ========== OCCURS CHECK ==========

    #[test]
    fn match_occurs_check_simple() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        let f_v0 = terms.app1(f, v0);

        // x vs F(x) should fail - infinite term
        let result = match_terms_combined(v0, f_v0, &terms);
        assert!(
            result.is_none(),
            "Occurs check should prevent infinite term"
        );
    }

    #[test]
    fn match_occurs_check_nested() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let g = symbols.intern("G");
        let v0 = terms.var(0);

        // x vs G(F(x))
        let f_v0 = terms.app1(f, v0);
        let g_f_v0 = terms.app1(g, f_v0);

        let result = match_terms_combined(v0, g_f_v0, &terms);
        assert!(
            result.is_none(),
            "Nested occurs check should prevent infinite term"
        );
    }

    #[test]
    fn match_occurs_check_through_substitution() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // F(x, y) vs F(y, F(x)) - should fail
        // After matching x=y, we'd have y vs F(y) which fails occurs check
        let f_x = terms.app1(f, v0);
        let t1 = terms.app2(f, v0, v1);
        let t2 = terms.app2(f, v1, f_x);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(result.is_none(), "Occurs check through subst should fail");
    }

    // ========== COMPLEX CASES ==========

    #[test]
    fn match_list_pattern() {
        let (symbols, terms) = setup();
        let cons = symbols.intern("Cons");
        let nil = symbols.intern("Nil");
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let a_term = terms.app0(a);
        let b_term = terms.app0(b);

        // Cons(x, Cons(y, Nil)) vs Cons(A, Cons(B, Nil))
        let nil_term = terms.app0(nil);
        let inner1 = terms.app2(cons, v1, nil_term);
        let t1 = terms.app2(cons, v0, inner1);

        let inner2 = terms.app2(cons, b_term, nil_term);
        let t2 = terms.app2(cons, a_term, inner2);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(a_term));
        assert_eq!(subst.get(1), Some(b_term));
    }

    #[test]
    fn match_vars_in_both_terms() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let v2 = terms.var(2);

        // F(x, y) vs F(z, z)
        // Should match with x=z, y=z (or equivalent)
        let t1 = terms.app2(f, v0, v1);
        let t2 = terms.app2(f, v2, v2);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(result.is_some());
        // The exact substitution depends on order, but both x and y should
        // ultimately equal z (or be equal to each other)
    }

    #[test]
    fn match_symmetric() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        let a = symbols.intern("A");
        let a_term = terms.app0(a);

        let t1 = terms.app1(f, v0);
        let t2 = terms.app1(f, a_term);

        // match_terms_combined(t1, t2) and match_terms_combined(t2, t1) should both succeed with same binding
        let result1 = match_terms_combined(t1, t2, &terms);
        let result2 = match_terms_combined(t2, t1, &terms);

        assert!(result1.is_some());
        assert!(result2.is_some());
        // Both should bind var 0 to a_term
        assert_eq!(result1.unwrap().get(0), Some(a_term));
        assert_eq!(result2.unwrap().get(0), Some(a_term));
    }

    #[test]
    fn match_deep_nesting() {
        let (symbols, terms) = setup();
        let s = symbols.intern("S");
        let z = symbols.intern("Z");
        let v0 = terms.var(0);

        // Build S(S(S(S(Z)))) and S(S(S(S(x))))
        let z_term = terms.app0(z);
        let s1 = terms.app1(s, z_term);
        let s2 = terms.app1(s, s1);
        let s3 = terms.app1(s, s2);
        let s4_z = terms.app1(s, s3);

        let sv1 = terms.app1(s, v0);
        let sv2 = terms.app1(s, sv1);
        let sv3 = terms.app1(s, sv2);
        let sv4 = terms.app1(s, sv3);

        let result = match_terms_combined(sv4, s4_z, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(z_term));
    }

    // ========== EDGE CASES ==========

    #[test]
    fn match_many_vars() {
        let (symbols, terms) = setup();
        let tuple = symbols.intern("Tuple");

        // Build Tuple(v0, v1, v2, v3, v4) and Tuple(a, a, a, a, a)
        let a = symbols.intern("A");
        let a_term = terms.app0(a);

        let vars: SmallVec<[TermId; 4]> = (0..5).map(|i| terms.var(i)).collect();
        let t1 = terms.app(tuple, vars);

        let as_terms: SmallVec<[TermId; 4]> = (0..5).map(|_| a_term).collect();
        let t2 = terms.app(tuple, as_terms);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        for i in 0..5 {
            assert_eq!(subst.get(i), Some(a_term));
        }
    }

    #[test]
    fn match_empty_app_terms() {
        let (symbols, terms) = setup();
        let empty = symbols.intern("Empty");
        let t1 = terms.app0(empty);
        let t2 = terms.app0(empty);

        let result = match_terms_combined(t1, t2, &terms);
        assert!(result.is_some());
        assert!(result.unwrap().is_empty());
    }
}
