//! Goals for demand-driven evaluation.
//!
//! A Goal specifies boundary constraints that an NF must satisfy.
//! Goals are used to filter table answers and propagate demands.
//!
//! Key operations:
//! - `goal_matches`: Check if an NF is compatible with a goal
//! - `canon_goal`: Canonicalize a goal for deduplication

use crate::constraint::ConstraintOps;
use crate::matching::match_pairs_disjoint;
use crate::nf::{max_var_in_nf, shift_nf_vars, Boundary, NF};
use crate::term::{TermId, TermStore};
use smallvec::SmallVec;

/// A goal is a pair of optional boundary constraints.
///
/// An NF is compatible with a goal if:
/// - If `match_bound` is Some, the NF's match_boundary must be matchable with it
/// - If `build_bound` is Some, the NF's build_boundary must be matchable with it
///
/// Both constraints must be satisfiable simultaneously (under disjoint variable scopes).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Goal {
    /// Optional constraint on match boundary.
    pub match_bound: Option<Boundary>,
    /// Optional constraint on build boundary.
    pub build_bound: Option<Boundary>,
}

impl Goal {
    /// Create an unconstrained goal (matches any NF).
    pub fn unconstrained() -> Self {
        Self {
            match_bound: None,
            build_bound: None,
        }
    }

    /// Create a goal with only match constraint.
    pub fn match_only(boundary: Boundary) -> Self {
        Self {
            match_bound: Some(boundary),
            build_bound: None,
        }
    }

    /// Create a goal with only build constraint.
    pub fn build_only(boundary: Boundary) -> Self {
        Self {
            match_bound: None,
            build_bound: Some(boundary),
        }
    }

    /// Create a goal with both constraints.
    pub fn both(match_bound: Boundary, build_bound: Boundary) -> Self {
        Self {
            match_bound: Some(match_bound),
            build_bound: Some(build_bound),
        }
    }

    /// Create a goal from optional boundaries.
    pub fn from_options(match_bound: Option<Boundary>, build_bound: Option<Boundary>) -> Self {
        Self {
            match_bound,
            build_bound,
        }
    }

    /// Check if this goal has any constraints.
    pub fn is_unconstrained(&self) -> bool {
        self.match_bound.is_none() && self.build_bound.is_none()
    }
}

/// Check if an NF is compatible with a goal.
///
/// Compatibility is defined by matching with disjoint variable scopes:
/// - If `goal.match_bound` is Some, check if `nf.match_boundary` matches it
/// - If `goal.build_bound` is Some, check if `nf.build_boundary` matches it
///
/// The NF and goal are renamed to disjoint namespaces before matching.
/// This ensures that non-ground answers (like `Rw [(cons z $0)] [$0]`)
/// can satisfy specific goals (like `match = cons z z`).
pub fn goal_matches<C: ConstraintOps>(goal: &Goal, nf: &NF<C>, terms: &mut TermStore) -> bool {
    // Fast path: unconstrained goal matches everything
    if goal.is_unconstrained() {
        return true;
    }

    // Fast path: check arity compatibility
    if let Some(ref match_bound) = goal.match_bound {
        if match_bound.len() != nf.match_arity() {
            return false;
        }
    }
    if let Some(ref build_bound) = goal.build_bound {
        if build_bound.len() != nf.build_arity() {
            return false;
        }
    }

    // Rename NF to disjoint namespace (starting at variable 0)
    let nf_max = max_var_in_nf(nf, terms).unwrap_or(0);
    let nf_offset = 0u32;
    let goal_offset = nf_max + 1;

    // Shift NF to start at nf_offset (in this case, it stays at 0)
    let nf_shifted = if nf_offset == 0 {
        nf.clone()
    } else {
        shift_nf_vars(nf, nf_offset, terms)
    };

    // Build pairs to match
    let mut pairs: SmallVec<[(TermId, TermId); 8]> = SmallVec::new();

    // Match boundary check
    if let Some(ref match_bound) = goal.match_bound {
        let shifted_goal_match = shift_boundary(match_bound, goal_offset, terms);
        for (nf_term, goal_term) in nf_shifted.match_boundary.iter().zip(shifted_goal_match.iter())
        {
            pairs.push((*nf_term, *goal_term));
        }
    }

    // Build boundary check
    if let Some(ref build_bound) = goal.build_bound {
        let shifted_goal_build = shift_boundary(build_bound, goal_offset, terms);
        for (nf_term, goal_term) in nf_shifted.build_boundary.iter().zip(shifted_goal_build.iter())
        {
            pairs.push((*nf_term, *goal_term));
        }
    }

    // Attempt matching
    match_pairs_disjoint(&pairs, terms).is_some()
}

/// Shift all variables in a boundary by an offset.
fn shift_boundary(boundary: &Boundary, offset: u32, terms: &mut TermStore) -> Boundary {
    crate::nf::shift_vars_list(boundary, offset, terms)
}

/// Check if a boundary is compatible with a goal's boundary constraint.
///
/// This is a simpler version of goal_matches that only checks one boundary.
/// Used for filtering outputs before synthesizing goals from them.
pub fn goal_matches_boundary(
    goal_bound: Option<&Boundary>,
    actual_bound: &Boundary,
    terms: &mut TermStore,
) -> bool {
    let goal_bound = match goal_bound {
        None => return true, // No constraint means compatible
        Some(b) => b,
    };

    // Arity check
    if goal_bound.len() != actual_bound.len() {
        return false;
    }

    // Find max variable in actual boundary to compute offset
    let max_var = crate::nf::max_var_in_boundary(actual_bound, terms).unwrap_or(0);
    let goal_offset = max_var + 1;

    // Shift goal boundary to disjoint namespace
    let shifted_goal = shift_boundary(goal_bound, goal_offset, terms);

    // Build pairs to match
    let pairs: SmallVec<[(TermId, TermId); 8]> = actual_bound
        .iter()
        .zip(shifted_goal.iter())
        .map(|(&a, &g)| (a, g))
        .collect();

    // Attempt matching
    match_pairs_disjoint(&pairs, terms).is_some()
}

/// Canonicalize a goal by renumbering variables.
///
/// Variables are assigned indices 0, 1, 2, ... in order of first occurrence,
/// scanning match_bound first, then build_bound.
pub fn canon_goal(goal: &Goal, terms: &mut TermStore) -> Goal {
    if goal.is_unconstrained() {
        return goal.clone();
    }

    // Collect variables in order of first occurrence
    let mut ordered: Vec<u32> = Vec::new();
    let mut seen: std::collections::HashSet<u32> = std::collections::HashSet::new();

    if let Some(ref match_bound) = goal.match_bound {
        for &term in match_bound.iter() {
            collect_vars_term(term, terms, &mut ordered, &mut seen);
        }
    }
    if let Some(ref build_bound) = goal.build_bound {
        for &term in build_bound.iter() {
            collect_vars_term(term, terms, &mut ordered, &mut seen);
        }
    }

    if ordered.is_empty() {
        return goal.clone();
    }

    // Build renaming map: old_var -> new_var (0, 1, 2, ...)
    let mut rename_map: Vec<Option<u32>> = Vec::new();
    for (new_idx, old_var) in ordered.iter().enumerate() {
        let idx = *old_var as usize;
        if idx >= rename_map.len() {
            rename_map.resize(idx + 1, None);
        }
        rename_map[idx] = Some(new_idx as u32);
    }

    // Apply renaming
    let match_bound = goal
        .match_bound
        .as_ref()
        .map(|b| apply_renaming_to_boundary(b, &rename_map, terms));
    let build_bound = goal
        .build_bound
        .as_ref()
        .map(|b| apply_renaming_to_boundary(b, &rename_map, terms));

    Goal {
        match_bound,
        build_bound,
    }
}

/// Collect variables from a term in first-occurrence order.
fn collect_vars_term(
    term: TermId,
    terms: &TermStore,
    ordered: &mut Vec<u32>,
    seen: &mut std::collections::HashSet<u32>,
) {
    use crate::term::Term;
    match terms.resolve(term) {
        Some(Term::Var(idx)) => {
            if seen.insert(idx) {
                ordered.push(idx);
            }
        }
        Some(Term::App(_, children)) => {
            for &child in children.iter() {
                collect_vars_term(child, terms, ordered, seen);
            }
        }
        None => {}
    }
}

/// Apply a variable renaming to a boundary.
fn apply_renaming_to_boundary(
    boundary: &Boundary,
    rename_map: &[Option<u32>],
    terms: &mut TermStore,
) -> Boundary {
    boundary
        .iter()
        .map(|&term| crate::nf::apply_var_renaming(term, rename_map, terms))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::SymbolStore;
    use smallvec::smallvec;

    fn setup() -> (SymbolStore, TermStore) {
        (SymbolStore::new(), TermStore::new())
    }

    // ========================================================================
    // GOAL CONSTRUCTION TESTS
    // ========================================================================

    #[test]
    fn goal_unconstrained_has_no_bounds() {
        let goal = Goal::unconstrained();
        assert!(goal.match_bound.is_none());
        assert!(goal.build_bound.is_none());
        assert!(goal.is_unconstrained());
    }

    #[test]
    fn goal_match_only_has_match_bound() {
        let (_, terms) = setup();
        let v0 = terms.var(0);
        let goal = Goal::match_only(smallvec![v0]);
        assert!(goal.match_bound.is_some());
        assert!(goal.build_bound.is_none());
        assert!(!goal.is_unconstrained());
    }

    #[test]
    fn goal_build_only_has_build_bound() {
        let (_, terms) = setup();
        let v0 = terms.var(0);
        let goal = Goal::build_only(smallvec![v0]);
        assert!(goal.match_bound.is_none());
        assert!(goal.build_bound.is_some());
        assert!(!goal.is_unconstrained());
    }

    #[test]
    fn goal_both_has_both_bounds() {
        let (_, terms) = setup();
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let goal = Goal::both(smallvec![v0], smallvec![v1]);
        assert!(goal.match_bound.is_some());
        assert!(goal.build_bound.is_some());
        assert!(!goal.is_unconstrained());
    }

    // ========================================================================
    // GOAL MATCHING TESTS
    // ========================================================================

    #[test]
    fn unconstrained_goal_matches_any_nf() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);

        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        let goal = Goal::unconstrained();
        assert!(goal_matches(&goal, &nf, &mut terms));
    }

    #[test]
    fn ground_match_goal_matches_compatible_nf() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);

        // NF: z -> z
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        // Goal: match = z
        let goal = Goal::match_only(smallvec![z_term]);
        assert!(goal_matches(&goal, &nf, &mut terms));
    }

    #[test]
    fn ground_match_goal_rejects_incompatible_nf() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let s = symbols.intern("s");
        let z_term = terms.app0(z);
        let s_z = terms.app1(s, z_term);

        // NF: (s z) -> z
        let nf: NF<()> = NF::new(smallvec![s_z], smallvec![z_term]);

        // Goal: match = z (not s z)
        let goal = Goal::match_only(smallvec![z_term]);
        assert!(!goal_matches(&goal, &nf, &mut terms));
    }

    #[test]
    fn variable_nf_matches_ground_goal() {
        // This is the critical non-groundness test from the design doc:
        // NF: Rw [(cons z $x)] [$x] should match goal: match = (cons z z)
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let cons = symbols.intern("cons");
        let z_term = terms.app0(z);
        let v0 = terms.var(0);

        // NF: (cons z $0) -> $0
        let cons_z_x = terms.app2(cons, z_term, v0);
        let nf: NF<()> = NF::new(smallvec![cons_z_x], smallvec![v0]);

        // Goal: match = (cons z z)
        let cons_z_z = terms.app2(cons, z_term, z_term);
        let goal = Goal::match_only(smallvec![cons_z_z]);

        // Should match because there's a substitution {$0 -> z} that makes it work
        assert!(goal_matches(&goal, &nf, &mut terms));
    }

    #[test]
    fn goal_with_both_bounds_requires_both_match() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let s = symbols.intern("s");
        let z_term = terms.app0(z);
        let s_z = terms.app1(s, z_term);

        // NF: z -> (s z)
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![s_z]);

        // Goal: match = z, build = (s z) - should match
        let goal_ok = Goal::both(smallvec![z_term], smallvec![s_z]);
        assert!(goal_matches(&goal_ok, &nf, &mut terms));

        // Goal: match = z, build = z - should NOT match
        let goal_fail = Goal::both(smallvec![z_term], smallvec![z_term]);
        assert!(!goal_matches(&goal_fail, &nf, &mut terms));
    }

    #[test]
    fn arity_mismatch_rejects_goal() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);

        // NF: z -> z (arity 1)
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        // Goal with arity 2
        let goal = Goal::match_only(smallvec![z_term, z_term]);
        assert!(!goal_matches(&goal, &nf, &mut terms));
    }

    #[test]
    fn variable_goal_matches_any_nf() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);
        let v0 = terms.var(0);

        // NF: z -> z
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        // Goal: match = $0 (variable) - should match anything
        let goal = Goal::match_only(smallvec![v0]);
        assert!(goal_matches(&goal, &nf, &mut terms));
    }

    // ========================================================================
    // GOAL CANONICALIZATION TESTS
    // ========================================================================

    #[test]
    fn canon_goal_unconstrained_unchanged() {
        let (_, mut terms) = setup();
        let goal = Goal::unconstrained();
        let canon = canon_goal(&goal, &mut terms);
        assert!(canon.is_unconstrained());
    }

    #[test]
    fn canon_goal_renumbers_variables() {
        let (_, mut terms) = setup();
        // Goal with non-canonical variable indices: $5 -> $3
        let v5 = terms.var(5);
        let v3 = terms.var(3);
        let goal = Goal::both(smallvec![v5], smallvec![v3]);

        let canon = canon_goal(&goal, &mut terms);

        // After canonicalization: $0 -> $1
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        assert_eq!(canon.match_bound.as_ref().unwrap()[0], v0);
        assert_eq!(canon.build_bound.as_ref().unwrap()[0], v1);
    }

    #[test]
    fn canon_goal_preserves_shared_variables() {
        let (symbols, mut terms) = setup();
        let f = symbols.intern("f");
        let v2 = terms.var(2);
        let v7 = terms.var(7);

        // Goal: f($2, $7) -> $2 (same variable appears twice)
        let f_term = terms.app2(f, v2, v7);
        let goal = Goal::both(smallvec![f_term], smallvec![v2]);

        let canon = canon_goal(&goal, &mut terms);

        // After canonicalization: f($0, $1) -> $0
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let f_canon = terms.app2(f, v0, v1);
        assert_eq!(canon.match_bound.as_ref().unwrap()[0], f_canon);
        assert_eq!(canon.build_bound.as_ref().unwrap()[0], v0);
    }

    #[test]
    fn canon_goal_ground_unchanged() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);

        let goal = Goal::match_only(smallvec![z_term]);
        let canon = canon_goal(&goal, &mut terms);

        assert_eq!(canon.match_bound.as_ref().unwrap()[0], z_term);
    }

    // ========================================================================
    // GOAL HASH/EQUALITY TESTS (for deduplication)
    // ========================================================================

    #[test]
    fn canonicalized_goals_are_equal() {
        let (_, mut terms) = setup();

        // Two goals with different variable names but same structure
        let v1 = terms.var(1);
        let v5 = terms.var(5);
        let goal1 = Goal::match_only(smallvec![v1]);
        let goal2 = Goal::match_only(smallvec![v5]);

        let canon1 = canon_goal(&goal1, &mut terms);
        let canon2 = canon_goal(&goal2, &mut terms);

        // After canonicalization, both should map to $0
        assert_eq!(canon1, canon2);
    }

    #[test]
    fn different_structure_goals_not_equal() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let s = symbols.intern("s");
        let z_term = terms.app0(z);
        let s_z = terms.app1(s, z_term);

        let goal1 = Goal::match_only(smallvec![z_term]);
        let goal2 = Goal::match_only(smallvec![s_z]);

        let canon1 = canon_goal(&goal1, &mut terms);
        let canon2 = canon_goal(&goal2, &mut terms);

        assert_ne!(canon1, canon2);
    }
}
