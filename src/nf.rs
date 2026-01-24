use crate::constraint::{ConstraintDisplay, ConstraintOps};
use crate::drop_fresh::DropFresh;
use crate::symbol::SymbolStore;
use crate::term::{format_term, Term, TermId, TermStore};
use smallvec::SmallVec;

/// Normal Form representation of a rewrite rule.
///
/// A rule `Rw lhs rhs` is factored into:
///   RwL [match_pats] ; DropFresh ; RwR [build_pats]
///
/// Where:
/// - RwL (match_pats): patterns to decompose input, extracting variables
/// - DropFresh: variable routing between LHS vars and RHS vars
/// - RwR (build_pats): patterns to construct output from variables
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NF<C> {
    /// Patterns for matching input terms (RwL).
    /// Variables in these patterns are numbered 0..n-1 in order of first appearance.
    pub match_pats: SmallVec<[TermId; 1]>,
    /// Variable routing between match and build.
    pub drop_fresh: DropFresh<C>,
    /// Patterns for building output terms (RwR).
    /// Variables in these patterns are numbered 0..m-1 with shared vars in LHS order,
    /// followed by RHS-only vars in RHS order.
    pub build_pats: SmallVec<[TermId; 1]>,
}

/// Direct tensor rewrite form (lists of patterns with constraint).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RwT<C> {
    pub lhs: SmallVec<[TermId; 1]>,
    pub rhs: SmallVec<[TermId; 1]>,
    pub constraint: C,
}

impl<C> NF<C> {
    /// Create a new NF directly (assumes already normalized).
    pub fn new(
        match_pats: SmallVec<[TermId; 1]>,
        drop_fresh: DropFresh<C>,
        build_pats: SmallVec<[TermId; 1]>,
    ) -> Self {
        Self {
            match_pats,
            drop_fresh,
            build_pats,
        }
    }

    /// Create an identity NF (empty patterns, zero-arity DropFresh).
    ///
    /// This represents the identity relation that accepts any input
    /// and produces it unchanged.
    pub fn identity(constraint: C) -> Self {
        Self {
            match_pats: SmallVec::new(),
            drop_fresh: DropFresh::identity_with_constraint(0, constraint),
            build_pats: SmallVec::new(),
        }
    }
}

impl<C: ConstraintOps> NF<C> {
    /// Factor a single-term rule (lhs -> rhs) into normal form.
    ///
    /// This extracts variables, renumbers them, and computes the DropFresh
    /// that connects LHS variables to RHS variables.
    pub fn factor(lhs: TermId, rhs: TermId, constraint: C, terms: &mut TermStore) -> Self {
        // Step 1: Collect variables from each side
        let lhs_vars = collect_vars_ordered(lhs, terms);
        let rhs_vars = collect_vars_ordered(rhs, terms);

        let n = lhs_vars.len() as u32;
        let lhs_old_to_new = build_var_map(&lhs_vars);

        // Step 2: Renumber LHS
        let norm_lhs = if lhs_vars.is_empty() {
            lhs
        } else {
            apply_var_renaming(lhs, &lhs_old_to_new, terms)
        };

        // Step 3: Establish RHS variable order:
        // - shared vars in LHS order (preserves monotone routing)
        // - fresh vars appended in RHS order
        let rhs_set: std::collections::HashSet<u32> = rhs_vars.iter().copied().collect();
        let lhs_set: std::collections::HashSet<u32> = lhs_vars.iter().copied().collect();

        // Build constraint variable ordering
        let mut constraint_ordered: Vec<u32> = lhs_vars.clone();
        for &var in rhs_vars.iter() {
            if !lhs_set.contains(&var) {
                constraint_ordered.push(var);
            }
        }
        let mut seen: std::collections::HashSet<u32> = constraint_ordered.iter().copied().collect();
        let mut constraint_vars = Vec::new();
        constraint.collect_vars(terms, &mut constraint_vars);
        constraint_vars.sort_unstable();
        constraint_vars.dedup();
        for var in constraint_vars {
            if seen.insert(var) {
                constraint_ordered.push(var);
            }
        }
        let constraint_map = build_var_map(&constraint_ordered);
        let constraint = constraint.remap_vars(&constraint_map, terms);

        // Build RHS variable ordering
        let mut rhs_ordered: Vec<u32> = Vec::new();
        for &var in lhs_vars.iter() {
            if rhs_set.contains(&var) {
                rhs_ordered.push(var);
            }
        }
        for &var in rhs_vars.iter() {
            if !lhs_set.contains(&var) {
                rhs_ordered.push(var);
            }
        }

        let m = rhs_ordered.len() as u32;
        let rhs_old_to_new = build_var_map(&rhs_ordered);

        // Step 4: Renumber RHS
        let norm_rhs = if rhs_ordered.is_empty() {
            rhs
        } else {
            apply_var_renaming(rhs, &rhs_old_to_new, terms)
        };

        // Step 7: Build DropFresh by finding shared variables
        // For each LHS var position i, find if the original var appears in RHS
        // and at what position j in rhs_ordered. DropFresh connects (i, j) for shared vars.
        let mut rhs_pos: std::collections::HashMap<u32, u32> = std::collections::HashMap::new();
        for (pos, &var) in rhs_ordered.iter().enumerate() {
            rhs_pos.insert(var, pos as u32);
        }
        let mut drop_fresh_map: SmallVec<[(u32, u32); 4]> = SmallVec::new();

        for (i, &lhs_orig_var) in lhs_vars.iter().enumerate() {
            if let Some(&j) = rhs_pos.get(&lhs_orig_var) {
                drop_fresh_map.push((i as u32, j));
            }
        }

        let drop_fresh = DropFresh {
            in_arity: n,
            out_arity: m,
            map: drop_fresh_map,
            constraint,
        };

        Self {
            match_pats: smallvec::smallvec![norm_lhs],
            drop_fresh,
            build_pats: smallvec::smallvec![norm_rhs],
        }
    }
}

/// Collect a tensor NF into direct-rule form by pushing wiring into RHS vars.
pub fn collect_tensor<C: Clone>(nf: &NF<C>, terms: &mut TermStore) -> RwT<C> {
    let out_arity = nf.drop_fresh.out_arity as usize;
    let in_arity = nf.drop_fresh.in_arity;

    let mut rhs_map: Vec<Option<u32>> = vec![None; out_arity];
    for (i, j) in nf.drop_fresh.map.iter().copied() {
        if let Some(slot) = rhs_map.get_mut(j as usize) {
            *slot = Some(i);
        }
    }

    let mut next_var = in_arity;
    for slot in rhs_map.iter_mut() {
        if slot.is_none() {
            *slot = Some(next_var);
            next_var += 1;
        }
    }

    let rhs_direct = apply_var_renaming_list(&nf.build_pats, &rhs_map, terms);

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
    let constraint_map = constraint_var_renaming(&lhs_pats, &rhs_pats, &constraint, terms);
    let constraint = constraint.remap_vars(&constraint_map, terms);

    let lhs_vars = collect_vars_ordered_list(&lhs_pats, terms);
    let rhs_vars = collect_vars_ordered_list(&rhs_pats, terms);

    let n = lhs_vars.len() as u32;
    let lhs_old_to_new = build_var_map(&lhs_vars);

    let norm_lhs = if lhs_vars.is_empty() {
        lhs_pats.clone()
    } else {
        apply_var_renaming_list(&lhs_pats, &lhs_old_to_new, terms)
    };

    let rhs_set: std::collections::HashSet<u32> = rhs_vars.iter().copied().collect();
    let lhs_set: std::collections::HashSet<u32> = lhs_vars.iter().copied().collect();

    // Build RHS variable ordering: shared vars in LHS order, then RHS-only vars
    let mut rhs_ordered: Vec<u32> = Vec::new();
    for &var in lhs_vars.iter() {
        if rhs_set.contains(&var) {
            rhs_ordered.push(var);
        }
    }
    for &var in rhs_vars.iter() {
        if !lhs_set.contains(&var) {
            rhs_ordered.push(var);
        }
    }

    let m = rhs_ordered.len() as u32;
    let rhs_old_to_new = build_var_map(&rhs_ordered);

    let norm_rhs = if rhs_ordered.is_empty() {
        rhs_pats.clone()
    } else {
        apply_var_renaming_list(&rhs_pats, &rhs_old_to_new, terms)
    };

    // Build DropFresh by finding shared variables
    let mut rhs_pos: std::collections::HashMap<u32, u32> = std::collections::HashMap::new();
    for (pos, &var) in rhs_ordered.iter().enumerate() {
        rhs_pos.insert(var, pos as u32);
    }

    let mut drop_fresh_map: SmallVec<[(u32, u32); 4]> = SmallVec::new();
    for (i, &lhs_orig_var) in lhs_vars.iter().enumerate() {
        if let Some(&j) = rhs_pos.get(&lhs_orig_var) {
            drop_fresh_map.push((i as u32, j));
        }
    }

    let drop_fresh = DropFresh {
        in_arity: n,
        out_arity: m,
        map: drop_fresh_map,
        constraint,
    };

    NF {
        match_pats: norm_lhs,
        drop_fresh,
        build_pats: norm_rhs,
    }
}

/// Compute a renaming map for constraints based on direct-rule variable ordering:
/// LHS variables first (order of appearance), then RHS-only variables.
pub fn constraint_var_renaming<C: ConstraintOps>(
    lhs_pats: &[TermId],
    rhs_pats: &[TermId],
    constraint: &C,
    terms: &TermStore,
) -> Vec<Option<u32>> {
    let lhs_vars = collect_vars_ordered_list(lhs_pats, terms);
    let rhs_vars = collect_vars_ordered_list(rhs_pats, terms);
    let mut constraint_vars = Vec::new();
    constraint.collect_vars(terms, &mut constraint_vars);
    constraint_vars.sort_unstable();
    constraint_vars.dedup();
    combined_var_renaming_with_extra(&lhs_vars, &rhs_vars, &constraint_vars)
}

/// Compute a renaming map for constraints based on combined variable order:
/// LHS variables first (order of appearance), then RHS-only variables.
pub fn combined_var_renaming(lhs_vars: &[u32], rhs_vars: &[u32]) -> Vec<Option<u32>> {
    combined_var_renaming_with_extra(lhs_vars, rhs_vars, &[])
}

/// Compute a renaming map for constraints using LHS vars, RHS-only vars,
/// then any extra vars (e.g., constraint-only vars).
pub fn combined_var_renaming_with_extra(
    lhs_vars: &[u32],
    rhs_vars: &[u32],
    extra_vars: &[u32],
) -> Vec<Option<u32>> {
    let mut ordered: Vec<u32> = Vec::new();
    let mut seen: std::collections::HashSet<u32> = std::collections::HashSet::new();
    for &var in lhs_vars.iter() {
        if seen.insert(var) {
            ordered.push(var);
        }
    }
    for &var in rhs_vars.iter() {
        if seen.insert(var) {
            ordered.push(var);
        }
    }
    for &var in extra_vars.iter() {
        if seen.insert(var) {
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
pub fn collect_vars_ordered(term: TermId, terms: &TermStore) -> Vec<u32> {
    let mut vars = Vec::new();
    let mut seen = std::collections::HashSet::new();
    collect_vars_helper(term, terms, &mut vars, &mut seen);
    vars
}

/// Collect variables from a list of terms in order of first appearance.
pub fn collect_vars_ordered_list(terms_list: &[TermId], terms: &TermStore) -> Vec<u32> {
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
    match terms.resolve(term) {
        Some(Term::Var(idx)) => {
            if seen.insert(idx) {
                vars.push(idx);
            }
        }
        Some(Term::App(_, children)) => {
            for child in children {
                collect_vars_helper(child, terms, vars, seen);
            }
        }
        None => {}
    }
}

/// Renumber variables in a term to use consecutive indices starting at 0.
/// Returns the renumbered term and the mapping from new index to old index.
pub fn renumber_vars(term: TermId, terms: &mut TermStore) -> (TermId, Vec<u32>) {
    let vars = collect_vars_ordered(term, terms);

    if vars.is_empty() {
        return (term, vec![]);
    }

    // Build old_to_new mapping
    let max_var = vars.iter().copied().max().unwrap() as usize;
    let mut old_to_new = vec![None; max_var + 1];
    for (new_idx, &old_idx) in vars.iter().enumerate() {
        old_to_new[old_idx as usize] = Some(new_idx as u32);
    }

    let renumbered = apply_var_renaming(term, &old_to_new, terms);
    (renumbered, vars)
}

/// Renumber variables according to a given mapping.
/// The mapping maps old variable index to new variable index.
pub fn apply_var_renaming(
    term: TermId,
    old_to_new: &[Option<u32>],
    terms: &mut TermStore,
) -> TermId {
    match terms.resolve(term) {
        Some(Term::Var(idx)) => {
            let idx_usize = idx as usize;
            if idx_usize < old_to_new.len() {
                if let Some(new_idx) = old_to_new[idx_usize] {
                    return terms.var(new_idx);
                }
            }
            // Variable not in mapping - keep as is
            term
        }
        Some(Term::App(func, children)) => {
            let new_children: SmallVec<[TermId; 4]> = children
                .iter()
                .map(|&child| apply_var_renaming(child, old_to_new, terms))
                .collect();
            terms.app(func, new_children)
        }
        None => term,
    }
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
    let out_arity = nf.drop_fresh.out_arity as usize;
    let in_arity = nf.drop_fresh.in_arity;

    let mut rhs_map: Vec<Option<u32>> = vec![None; out_arity];
    for (i, j) in nf.drop_fresh.map.iter().copied() {
        if let Some(slot) = rhs_map.get_mut(j as usize) {
            *slot = Some(i);
        }
    }

    let mut next_var = in_arity;
    for slot in rhs_map.iter_mut() {
        if slot.is_none() {
            *slot = Some(next_var);
            next_var += 1;
        }
    }

    let rhs_direct = apply_var_renaming(rhs, &rhs_map, terms);
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
#[path = "tests/nf.rs"]
mod tests;
