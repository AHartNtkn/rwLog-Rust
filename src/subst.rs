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

    /// Create a substitution with capacity for n variables.
    pub fn with_capacity(n: usize) -> Self {
        Self {
            bindings: vec![None; n],
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
    pub fn is_bound(&self, var: u32) -> bool {
        self.get(var).is_some()
    }

    /// Check if the substitution is empty (no bindings).
    pub fn is_empty(&self) -> bool {
        self.bindings.iter().all(|b| b.is_none())
    }

    /// Number of bound variables.
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
/// Uses explicit stack to avoid recursion.
pub fn apply_subst(term: TermId, subst: &Subst, terms: &mut TermStore) -> TermId {
    // Use a worklist to process terms depth-first
    // Stack contains (original term, children_processed)
    // Result stack collects processed terms

    let mut work_stack: Vec<(TermId, bool)> = vec![(term, false)];
    let mut result_stack: Vec<TermId> = Vec::new();
    let mut children_counts: Vec<usize> = Vec::new();

    while let Some((tid, children_done)) = work_stack.pop() {
        if children_done {
            // Children have been processed, now build the result
            let original = terms.resolve(tid);
            match original {
                Some(Term::App(func, children)) => {
                    let n = children.len();
                    let count = children_counts.pop().unwrap();
                    assert_eq!(n, count);

                    // Pop n results from result_stack
                    let new_children: SmallVec<[TermId; 4]> =
                        result_stack.drain(result_stack.len() - n..).collect();

                    let new_term = terms.app(func, new_children);
                    result_stack.push(new_term);
                }
                _ => {
                    // Var or None case already handled in first pass
                    unreachable!("Only App terms should have children_done=true");
                }
            }
        } else {
            // First visit to this term
            match terms.resolve(tid) {
                Some(Term::Var(_)) => {
                    // Follow variable chain iteratively
                    let resolved = resolve_var_chain(tid, subst, terms);
                    match terms.resolve(resolved) {
                        Some(Term::Var(_)) => {
                            // Ended at a variable (unbound or cycle)
                            result_stack.push(resolved);
                        }
                        Some(Term::App(_, children)) => {
                            if children.is_empty() {
                                result_stack.push(resolved);
                            } else {
                                // Need to process this App term
                                work_stack.push((resolved, true));
                                children_counts.push(children.len());
                                for child in children.iter().rev() {
                                    work_stack.push((*child, false));
                                }
                            }
                        }
                        None => {
                            result_stack.push(resolved);
                        }
                    }
                }
                Some(Term::App(_, children)) => {
                    if children.is_empty() {
                        // Nullary app - no children to process
                        result_stack.push(tid);
                    } else {
                        // Push back with children_done=true for later processing
                        work_stack.push((tid, true));
                        children_counts.push(children.len());
                        // Push children (in reverse order so leftmost processed first)
                        for child in children.iter().rev() {
                            work_stack.push((*child, false));
                        }
                    }
                }
                None => {
                    // Invalid term - just keep it
                    result_stack.push(tid);
                }
            }
        }
    }

    assert_eq!(result_stack.len(), 1);
    result_stack.pop().unwrap()
}

/// Follow a chain of variable substitutions until we hit a non-variable
/// or detect a cycle. Returns the final term in the chain.
fn resolve_var_chain(start: TermId, subst: &Subst, terms: &TermStore) -> TermId {
    let mut current = start;
    let mut visited = smallvec::SmallVec::<[u32; 8]>::new();

    loop {
        match terms.resolve(current) {
            Some(Term::Var(idx)) => {
                // Check for cycle
                if visited.contains(&idx) {
                    // Cycle detected - return current variable
                    return current;
                }
                visited.push(idx);

                // Check if bound
                if let Some(bound) = subst.get(idx) {
                    current = bound;
                } else {
                    // Unbound variable - end of chain
                    return current;
                }
            }
            Some(Term::App(_, _)) => {
                // Hit a non-variable term
                return current;
            }
            None => {
                return current;
            }
        }
    }
}


#[cfg(test)]
mod tests;
