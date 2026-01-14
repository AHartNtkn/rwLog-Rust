use crate::subst::Subst;
use crate::term::{Term, TermId, TermStore};
use smallvec::SmallVec;

#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};

/// Unify two terms, returning a most general unifier (MGU) if successful.
/// Returns None if the terms cannot be unified.
///
/// Uses an explicit worklist to avoid recursion.
/// Implements occurs-check to prevent infinite terms.
pub fn unify(t1: TermId, t2: TermId, terms: &TermStore) -> Option<Subst> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!("unify", ?t1, ?t2).entered();

    let mut subst = Subst::new();
    let mut worklist: SmallVec<[(TermId, TermId); 32]> = SmallVec::new();
    worklist.push((t1, t2));

    while let Some((a, b)) = worklist.pop() {
        // Dereference variables through the substitution
        let a_deref = deref(a, &subst, terms);
        let b_deref = deref(b, &subst, terms);

        if a_deref == b_deref {
            // Same term - already unified
            continue;
        }

        match (terms.resolve(a_deref), terms.resolve(b_deref)) {
            (Some(Term::Var(idx_a)), Some(Term::Var(idx_b))) => {
                // Both variables - bind one to the other
                // Prefer binding higher-indexed to lower-indexed for consistency
                if idx_a < idx_b {
                    subst.bind(idx_b, a_deref);
                } else {
                    subst.bind(idx_a, b_deref);
                }
            }
            (Some(Term::Var(idx)), Some(Term::App(_, _))) => {
                // Variable vs App - occurs check then bind
                if occurs(idx, b_deref, &subst, terms) {
                    #[cfg(feature = "tracing")]
                    trace!(var = idx, "unify_occurs_check_failed");
                    return None; // Occurs check failed
                }
                subst.bind(idx, b_deref);
            }
            (Some(Term::App(_, _)), Some(Term::Var(idx))) => {
                // App vs Variable - occurs check then bind
                if occurs(idx, a_deref, &subst, terms) {
                    #[cfg(feature = "tracing")]
                    trace!(var = idx, "unify_occurs_check_failed");
                    return None; // Occurs check failed
                }
                subst.bind(idx, a_deref);
            }
            (Some(Term::App(f1, children1)), Some(Term::App(f2, children2))) => {
                // Both Apps - must have same functor and arity
                if f1 != f2 {
                    #[cfg(feature = "tracing")]
                    trace!("unify_functor_mismatch");
                    return None; // Different functors
                }
                if children1.len() != children2.len() {
                    #[cfg(feature = "tracing")]
                    trace!("unify_arity_mismatch");
                    return None; // Different arities
                }
                // Add children pairs to worklist
                for (c1, c2) in children1.iter().zip(children2.iter()) {
                    worklist.push((*c1, *c2));
                }
            }
            _ => {
                // One or both terms are invalid
                #[cfg(feature = "tracing")]
                trace!("unify_invalid_term");
                return None;
            }
        }
    }

    #[cfg(feature = "tracing")]
    trace!(bindings = subst.len(), "unify_success");

    Some(subst)
}

/// Dereference a term through the substitution.
/// If the term is a variable bound in the substitution, follow the chain.
fn deref(term: TermId, subst: &Subst, terms: &TermStore) -> TermId {
    let mut current = term;
    loop {
        match terms.resolve(current) {
            Some(Term::Var(idx)) => {
                if let Some(bound) = subst.get(idx) {
                    current = bound;
                } else {
                    return current;
                }
            }
            _ => return current,
        }
    }
}

/// Occurs check: does variable `var` occur in term `term`?
/// Used to prevent creating infinite (cyclic) terms.
fn occurs(var: u32, term: TermId, subst: &Subst, terms: &TermStore) -> bool {
    let mut stack: SmallVec<[TermId; 16]> = SmallVec::new();
    stack.push(term);

    while let Some(t) = stack.pop() {
        let t_deref = deref(t, subst, terms);
        match terms.resolve(t_deref) {
            Some(Term::Var(idx)) => {
                if idx == var {
                    return true;
                }
            }
            Some(Term::App(_, children)) => {
                for child in children.iter() {
                    stack.push(*child);
                }
            }
            None => {}
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::SymbolStore;

    fn setup() -> (SymbolStore, TermStore) {
        (SymbolStore::new(), TermStore::new())
    }

    // ========== HAPPY PATH: IDENTICAL TERMS ==========

    #[test]
    fn unify_same_var() {
        let (_, terms) = setup();
        let v0 = terms.var(0);

        let result = unify(v0, v0, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert!(subst.is_empty(), "Same var should produce empty subst");
    }

    #[test]
    fn unify_same_ground_term() {
        let (symbols, terms) = setup();
        let zero = symbols.intern("Zero");
        let t = terms.app0(zero);

        let result = unify(t, t, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert!(subst.is_empty(), "Same term should produce empty subst");
    }

    #[test]
    fn unify_same_complex_term() {
        let (symbols, terms) = setup();
        let cons = symbols.intern("Cons");
        let nil = symbols.intern("Nil");
        let v0 = terms.var(0);
        let nil_term = terms.app0(nil);
        let t = terms.app2(cons, v0, nil_term);

        let result = unify(t, t, &terms);
        assert!(result.is_some());
    }

    // ========== HAPPY PATH: VAR vs TERM ==========

    #[test]
    fn unify_var_with_ground() {
        let (symbols, terms) = setup();
        let zero = symbols.intern("Zero");
        let v0 = terms.var(0);
        let zero_term = terms.app0(zero);

        let result = unify(v0, zero_term, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(zero_term));
    }

    #[test]
    fn unify_ground_with_var() {
        let (symbols, terms) = setup();
        let zero = symbols.intern("Zero");
        let v0 = terms.var(0);
        let zero_term = terms.app0(zero);

        let result = unify(zero_term, v0, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(zero_term));
    }

    #[test]
    fn unify_var_with_var() {
        let (_, terms) = setup();
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        let result = unify(v0, v1, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        // One should be bound to the other
        assert!(subst.is_bound(0) || subst.is_bound(1));
        assert_eq!(subst.len(), 1);
    }

    #[test]
    fn unify_var_with_nested_var() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let f_v1 = terms.app1(f, v1);

        let result = unify(v0, f_v1, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(f_v1));
    }

    // ========== HAPPY PATH: COMPATIBLE CONSTRUCTORS ==========

    #[test]
    fn unify_nullary_same_functor() {
        let (symbols, terms) = setup();
        let nil = symbols.intern("Nil");
        let t1 = terms.app0(nil);
        let t2 = terms.app0(nil);

        let result = unify(t1, t2, &terms);
        assert!(result.is_some());
    }

    #[test]
    fn unify_compatible_apps() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        let a = symbols.intern("A");
        let a_term = terms.app0(a);

        // F(x) vs F(A)
        let t1 = terms.app1(f, v0);
        let t2 = terms.app1(f, a_term);

        let result = unify(t1, t2, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(a_term));
    }

    #[test]
    fn unify_nested_compatible() {
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

        let result = unify(t1, t2, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(a_term));
        assert_eq!(subst.get(1), Some(b_term));
    }

    #[test]
    fn unify_both_sides_have_vars() {
        let (symbols, terms) = setup();
        let pair = symbols.intern("Pair");
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let a = symbols.intern("A");
        let a_term = terms.app0(a);

        // Pair(x, A) vs Pair(A, y)
        let t1 = terms.app2(pair, v0, a_term);
        let t2 = terms.app2(pair, a_term, v1);

        let result = unify(t1, t2, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(a_term));
        assert_eq!(subst.get(1), Some(a_term));
    }

    #[test]
    fn unify_shared_var() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);

        // F(x, x) vs F(A, A) should work
        let a = symbols.intern("A");
        let a_term = terms.app0(a);
        let t1 = terms.app2(f, v0, v0);
        let t2 = terms.app2(f, a_term, a_term);

        let result = unify(t1, t2, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(a_term));
    }

    // ========== UNHAPPY PATH: INCOMPATIBLE CONSTRUCTORS ==========

    #[test]
    fn unify_different_nullary_fails() {
        let (symbols, terms) = setup();
        let nil = symbols.intern("Nil");
        let zero = symbols.intern("Zero");
        let t1 = terms.app0(nil);
        let t2 = terms.app0(zero);

        let result = unify(t1, t2, &terms);
        assert!(result.is_none(), "Different functors should fail");
    }

    #[test]
    fn unify_different_functors_fails() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let g = symbols.intern("G");
        let a = symbols.intern("A");
        let a_term = terms.app0(a);

        let t1 = terms.app1(f, a_term);
        let t2 = terms.app1(g, a_term);

        let result = unify(t1, t2, &terms);
        assert!(result.is_none(), "Different functors should fail");
    }

    #[test]
    fn unify_different_arity_fails() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let a = symbols.intern("A");
        let a_term = terms.app0(a);

        let t1 = terms.app1(f, a_term);
        let t2 = terms.app2(f, a_term, a_term);

        let result = unify(t1, t2, &terms);
        assert!(result.is_none(), "Different arities should fail");
    }

    #[test]
    fn unify_nested_conflict_fails() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let a_term = terms.app0(a);
        let b_term = terms.app0(b);

        // F(A) vs F(B)
        let t1 = terms.app1(f, a_term);
        let t2 = terms.app1(f, b_term);

        let result = unify(t1, t2, &terms);
        assert!(result.is_none(), "Nested conflict should fail");
    }

    #[test]
    fn unify_shared_var_conflict_fails() {
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

        let result = unify(t1, t2, &terms);
        assert!(result.is_none(), "Shared var with different values should fail");
    }

    // ========== OCCURS CHECK ==========

    #[test]
    fn unify_occurs_check_simple() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        let f_v0 = terms.app1(f, v0);

        // x vs F(x) should fail - infinite term
        let result = unify(v0, f_v0, &terms);
        assert!(result.is_none(), "Occurs check should prevent infinite term");
    }

    #[test]
    fn unify_occurs_check_nested() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let g = symbols.intern("G");
        let v0 = terms.var(0);

        // x vs G(F(x))
        let f_v0 = terms.app1(f, v0);
        let g_f_v0 = terms.app1(g, f_v0);

        let result = unify(v0, g_f_v0, &terms);
        assert!(result.is_none(), "Nested occurs check should prevent infinite term");
    }

    #[test]
    fn unify_occurs_check_through_substitution() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // F(x, y) vs F(y, F(x)) - should fail
        // After unifying x=y, we'd have y vs F(y) which fails occurs check
        let f_x = terms.app1(f, v0);
        let t1 = terms.app2(f, v0, v1);
        let t2 = terms.app2(f, v1, f_x);

        let result = unify(t1, t2, &terms);
        assert!(result.is_none(), "Occurs check through subst should fail");
    }

    // ========== COMPLEX CASES ==========

    #[test]
    fn unify_list_pattern() {
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

        let result = unify(t1, t2, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(a_term));
        assert_eq!(subst.get(1), Some(b_term));
    }

    #[test]
    fn unify_vars_in_both_terms() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let v2 = terms.var(2);

        // F(x, y) vs F(z, z)
        // Should unify with x=z, y=z (or equivalent)
        let t1 = terms.app2(f, v0, v1);
        let t2 = terms.app2(f, v2, v2);

        let result = unify(t1, t2, &terms);
        assert!(result.is_some());
        // The exact substitution depends on order, but both x and y should
        // ultimately equal z (or be equal to each other)
    }

    #[test]
    fn unify_symmetric() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);
        let a = symbols.intern("A");
        let a_term = terms.app0(a);

        let t1 = terms.app1(f, v0);
        let t2 = terms.app1(f, a_term);

        // unify(t1, t2) and unify(t2, t1) should both succeed with same binding
        let result1 = unify(t1, t2, &terms);
        let result2 = unify(t2, t1, &terms);

        assert!(result1.is_some());
        assert!(result2.is_some());
        // Both should bind var 0 to a_term
        assert_eq!(result1.unwrap().get(0), Some(a_term));
        assert_eq!(result2.unwrap().get(0), Some(a_term));
    }

    #[test]
    fn unify_deep_nesting() {
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

        let result = unify(sv4, s4_z, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(z_term));
    }

    // ========== EDGE CASES ==========

    #[test]
    fn unify_many_vars() {
        let (symbols, terms) = setup();
        let tuple = symbols.intern("Tuple");

        // Build Tuple(v0, v1, v2, v3, v4) and Tuple(a, a, a, a, a)
        let a = symbols.intern("A");
        let a_term = terms.app0(a);

        let vars: SmallVec<[TermId; 4]> = (0..5).map(|i| terms.var(i)).collect();
        let t1 = terms.app(tuple, vars);

        let as_terms: SmallVec<[TermId; 4]> = (0..5).map(|_| a_term).collect();
        let t2 = terms.app(tuple, as_terms);

        let result = unify(t1, t2, &terms);
        assert!(result.is_some());
        let subst = result.unwrap();
        for i in 0..5 {
            assert_eq!(subst.get(i), Some(a_term));
        }
    }

    #[test]
    fn unify_empty_app_terms() {
        let (symbols, terms) = setup();
        let empty = symbols.intern("Empty");
        let t1 = terms.app0(empty);
        let t2 = terms.app0(empty);

        let result = unify(t1, t2, &terms);
        assert!(result.is_some());
        assert!(result.unwrap().is_empty());
    }
}
