//! The store a problem starts from (`sorts::start`) and its canonical store
//! (`sorts::normal`), against the folded store (`FoldOf` of
//! `lean/RwLog/Sorts/FoldRaw.lean`) of `Prob.norm` of the specification
//! (`lean/RwLog/Sorts/Norm.lean`) as written on trees
//! (`common::sorts::normal`).
//!
//! A problem is a pattern, equations, sorts of patterns and exclusions.
//! `start` solves the equations, numbers the variables left in the order
//! they first occur in the pattern, the sorted patterns and the exclusions,
//! and brings the sorts down to the variables: one entry for each variable,
//! also for the hidden ones, which occur in the sorted patterns or the
//! exclusions and not in the pattern. `normal` replaces each variable whose
//! sorts have one member, drops the hidden variables with the exclusions
//! whose solved forms mention them, writes out each variable an exclusion
//! mentions whose values have one root, numbers what is left again, solves
//! its exclusions and drops the ones another covers, and folds each
//! outermost free subterm of the pattern into one variable. A hidden
//! variable is never replaced by a root applied to new variables. Every sort
//! of a problem is declared.

mod common;

use common::decls::*;
use common::sorts::*;
use common::{ap, get, get_list, spent, v, T};
use rwlog_core::sorts::{normal, start};
use rwlog_core::store::{Node, Tbl, TermId};

/// The parts of a problem in the store: pattern, equations, sorted patterns
/// (each the application of the name to the pattern) and exclusions.
fn put_prob(f: &mut Fx, p: &Prob) -> (TermId, TermId, TermId, TermId) {
    let t = put_pat(&mut f.s, &p.t);
    let e = put_eqns(&mut f.s, &p.e);
    let mut a = f.s.alloc(Node::Nil);
    for (n, q) in p.a.iter().rev() {
        let n = f.s.alloc(Node::Sym(*n));
        let q = put_pat(&mut f.s, q);
        let h = f.s.alloc(Node::App(n, q));
        a = f.s.alloc(Node::App(h, a));
    }
    let x = put_excls(&mut f.s, &p.x);
    (t, e, a, x)
}

fn get_lists(f: &mut Fx, mut p: TermId) -> Vec<Vec<T>> {
    let mut out = Vec::new();
    loop {
        match f.s.read(p) {
            Node::Nil => return out,
            Node::App(h, rest) => {
                out.push(get_list(&mut f.s, h));
                p = rest;
            }
            _ => panic!("a term where a list was expected"),
        }
    }
}

/// Tables with entries and flags left by earlier work.
fn dirty(f: &mut Fx) {
    let n = f.s.alloc(Node::Nil);
    let m = f.s.alloc(Node::App(n, n));
    f.s.set(Tbl::A, n, m);
    f.s.set(Tbl::B, n, m);
    f.s.set(Tbl::A, m, n);
    f.s.set_flag(Tbl::B, m, true);
    f.s.set(Tbl::A, f.decls, n);
    f.s.set(Tbl::B, f.names, m);
}

/// What `start` returns, read back: the pattern, the exclusions, the entries
/// and the next variable.
type Started = (T, Vec<Vec<T>>, Entries, T);

fn run_start(p: &Prob, soiled: bool) -> Option<Started> {
    let mut f = fixture(wf());
    let (t, e, a, x) = put_prob(&mut f, p);
    if soiled {
        dirty(&mut f);
    }
    let got = start(&mut f.s, f.decls, f.names, t, e, a, x);
    f.empty_stack();
    got.map(|(t0, x0, es0, next0)| {
        let t1 = get(&mut f.s, t0);
        let x0 = get_lists(&mut f, x0);
        let es = f.read_entries(es0);
        let next = get(&mut f.s, next0);
        (t1, x0, es, next)
    })
}

/// `start` gives the pattern `t` itself, the exclusions `x`, an entry with
/// the conjunction `ents[i]` for each variable `i` below `n` in order, and
/// `n` as the next variable.
fn start_is(p: &Prob, t: &P, n: usize, x: &[Vec<(P, P)>], ents: &[Vec<Name>]) {
    let order = fixture(wf()).order;
    let (gt, gx, ges, gnext) = run_start(p, false).expect("a store");
    assert_eq!(gt, t.tree(), "the pattern of {p:?}");
    let wx: Vec<Vec<T>> =
        x.iter().map(|e| e.iter().map(|(l, r)| ap(l.tree(), r.tree())).collect()).collect();
    assert_eq!(gx, wx, "the exclusions of {p:?}");
    assert_eq!(ents.len(), n, "one entry for each variable");
    let wes: Entries = ents
        .iter()
        .enumerate()
        .map(|(i, c)| (i, canon(&order, &c.iter().copied().collect())))
        .collect();
    assert_eq!(ges, wes, "the entries of {p:?}");
    assert_eq!(gnext, v(n as u128), "the next variable of {p:?}");
}

fn start_none(p: &Prob) {
    assert!(run_start(p, false).is_none(), "{p:?} has a store");
}

fn start_dirty(p: &Prob) {
    let clean = run_start(p, false);
    assert!(clean.is_some());
    assert_eq!(run_start(p, true), clean);
}

/// A normal store as `normal` gives it: the pattern, the conjunction of
/// each variable as a sorted list, and the exclusions, each the list of the
/// values of the variables, as a sorted list of their printed forms.
type Shape = (T, Vec<Vec<Name>>, Vec<String>);

fn sorted<X: Ord>(mut l: Vec<X>) -> Vec<X> {
    l.sort();
    l
}

fn shape(r: &Raw) -> Shape {
    let k = r.c.len();
    let x = r
        .x
        .iter()
        .map(|b| {
            let vals: Vec<T> = (0..k)
                .map(|i| b.iter().find(|(y, _)| *y == i).map_or(pv(i), |(_, q)| q.clone()).tree())
                .collect();
            format!("{vals:?}")
        })
        .collect();
    (r.t.tree(), r.c.iter().map(|c| c.iter().copied().collect()).collect(), sorted(x))
}

fn run_normal(defs: Vec<(Name, Def)>, p: &Prob, soiled: bool) -> Option<Shape> {
    let mut f = fixture(defs);
    let (t, e, a, x) = put_prob(&mut f, p);
    if soiled {
        dirty(&mut f);
    }
    let got = normal(&mut f.s, f.decls, f.names, t, e, a, x);
    f.empty_stack();
    got.map(|r| {
        let t1 = get(&mut f.s, r.t);
        let cs = get_conjs(&mut f.s, r.c).into_iter().map(sorted).collect();
        let xs = get_lists(&mut f, r.x).iter().map(|l| format!("{l:?}")).collect();
        (t1, cs, sorted(xs))
    })
}

/// `normal` gives the normal store of the reference, and there is one.
fn normal_same(defs: Vec<(Name, Def)>, p: &Prob) {
    let want = common::sorts::normal(&Sorts::new(defs.clone()), p);
    assert!(want.is_some(), "the reference has no store for {p:?}");
    assert_eq!(run_normal(defs, p, false), want.as_ref().map(shape), "{p:?}");
}

/// Neither `normal` nor the reference has a store.
fn normal_none(defs: Vec<(Name, Def)>, p: &Prob) {
    assert!(common::sorts::normal(&Sorts::new(defs.clone()), p).is_none(), "the reference has a store for {p:?}");
    assert!(run_normal(defs, p, false).is_none(), "{p:?} has a store");
}

/// `normal` gives the normal store of the reference, with this pattern.
fn normal_pattern(p: &Prob, t: &P) {
    normal_same(wf(), p);
    let got = run_normal(wf(), p, false).expect("a store");
    assert_eq!(got.0, t.tree(), "the pattern of {p:?}");
}

fn normal_dirty(p: &Prob) {
    let clean = run_normal(wf(), p, false);
    assert!(clean.is_some());
    assert_eq!(run_normal(wf(), p, true), clean);
}

#[test]
fn start_bare_variable_has_one_unsorted_entry() {
    start_is(&Prob { t: pv(0), e: vec![], a: vec![], x: vec![] }, &pv(0), 1, &[], &[vec![]]);
}

#[test]
fn start_ground_pattern_has_no_entries_and_next_zero() {
    start_is(&Prob { t: su(z()), e: vec![], a: vec![], x: vec![] }, &su(z()), 0, &[], &[]);
}

#[test]
fn start_renames_variables_by_first_occurrence_in_pattern() {
    start_is(&Prob { t: f2(pv(5), pv(2)), e: vec![], a: vec![], x: vec![] }, &f2(pv(0), pv(1)), 2, &[], &[vec![], vec![]]);
}

#[test]
fn start_repeated_variable_gets_one_entry() {
    start_is(&Prob { t: pf(F, vec![pv(3), pv(3), pv(1)]), e: vec![], a: vec![], x: vec![] }, &pf(F, vec![pv(0), pv(0), pv(1)]), 2, &[], &[vec![], vec![]]);
}

#[test]
fn start_applies_equation_binding_to_pattern() {
    start_is(&Prob { t: f2(pv(0), pv(1)), e: vec![(pv(0), su(pv(1)))], a: vec![], x: vec![] }, &f2(su(pv(0)), pv(0)), 1, &[], &[vec![]]);
}

#[test]
fn start_alias_equation_merges_two_variables() {
    start_is(&Prob { t: f2(pv(0), pv(1)), e: vec![(pv(0), pv(1))], a: vec![], x: vec![] }, &f2(pv(0), pv(0)), 1, &[], &[vec![]]);
}

#[test]
fn start_equation_chain_grounds_pattern() {
    start_is(&Prob { t: pf(F, vec![pv(0), pv(1), pv(2)]), e: vec![(pv(0), pv(1)), (pv(1), pv(2)), (pv(2), z())], a: vec![], x: vec![] }, &pf(F, vec![z(), z(), z()]), 0, &[], &[]);
}

#[test]
fn start_symbol_clash_in_equations_is_none() {
    start_none(&Prob { t: pv(0), e: vec![(z(), su(pv(0)))], a: vec![], x: vec![] });
}

#[test]
fn start_occurs_check_failure_is_none() {
    start_none(&Prob { t: pv(0), e: vec![(pv(0), su(pv(0)))], a: vec![], x: vec![] });
}

#[test]
fn start_trivial_equations_change_nothing() {
    start_is(&Prob { t: f2(pv(0), pv(1)), e: vec![(pv(0), pv(0)), (z(), z())], a: vec![], x: vec![] }, &f2(pv(0), pv(1)), 2, &[], &[vec![], vec![]]);
}

#[test]
fn start_equation_variables_outside_pattern_get_no_entry() {
    start_is(&Prob { t: pv(0), e: vec![(pv(7), su(pv(8)))], a: vec![], x: vec![] }, &pv(0), 1, &[], &[vec![]]);
}

#[test]
fn start_sort_on_variable_lands_in_its_entry() {
    start_is(&Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0))], x: vec![] }, &pv(0), 1, &[], &[vec![NAT]]);
}

#[test]
fn start_sort_on_compound_is_pushed_to_variables_in_pattern_order() {
    start_is(&Prob { t: f2(pv(1), pv(0)), e: vec![], a: vec![(PAIR, pr(pv(0), pv(1)))], x: vec![] }, &f2(pv(0), pv(1)), 2, &[], &[vec![NAT], vec![NAT]]);
}

#[test]
fn start_two_sorts_on_one_variable_are_conjoined() {
    start_is(&Prob { t: pv(0), e: vec![], a: vec![(SUC, pv(0)), (NAT, pv(0))], x: vec![] }, &pv(0), 1, &[], &[vec![NAT, SUC]]);
}

#[test]
fn start_sorts_through_different_patterns_are_conjoined() {
    start_is(&Prob { t: pv(0), e: vec![], a: vec![(PAIR, pr(pv(0), pv(0))), (SUC, pv(0))], x: vec![] }, &pv(0), 1, &[], &[vec![NAT, SUC]]);
}

#[test]
fn start_sort_rejecting_root_symbol_is_none() {
    start_none(&Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![(NAT, pr(pv(0), pv(1)))], x: vec![] });
}

#[test]
fn start_sort_rejecting_arity_is_none() {
    start_none(&Prob { t: pv(0), e: vec![], a: vec![(UNIT, pf(Z, vec![pv(0)]))], x: vec![] });
}

#[test]
fn start_ground_member_adds_no_entry() {
    start_is(&Prob { t: pv(0), e: vec![], a: vec![(NAT, su(z()))], x: vec![] }, &pv(0), 1, &[], &[vec![]]);
}

#[test]
fn start_ground_non_member_is_none() {
    start_none(&Prob { t: pv(0), e: vec![], a: vec![(NAT, su(a()))], x: vec![] });
}

#[test]
fn start_empty_sort_on_variable_is_kept_not_rejected() {
    start_is(&Prob { t: pv(0), e: vec![], a: vec![(VOID, su(pv(0)))], x: vec![] }, &pv(0), 1, &[], &[vec![VOID]]);
}

#[test]
fn start_single_member_sort_keeps_the_variable() {
    start_is(&Prob { t: pv(0), e: vec![], a: vec![(UNIT, pv(0))], x: vec![] }, &pv(0), 1, &[], &[vec![UNIT]]);
}

#[test]
fn start_untyped_argument_position_leaves_variable_unsorted() {
    start_is(&Prob { t: pv(0), e: vec![], a: vec![(ANY, pf(F, vec![pv(0)]))], x: vec![] }, &pv(0), 1, &[], &[vec![]]);
}

#[test]
fn start_symbol_excluded_from_rest_is_none() {
    start_none(&Prob { t: pv(0), e: vec![], a: vec![(ANY, a())], x: vec![] });
}

#[test]
fn start_hidden_sort_variable_is_numbered_after_pattern_variables() {
    start_is(&Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(3))], x: vec![] }, &pv(0), 2, &[], &[vec![], vec![NAT]]);
}

#[test]
fn start_numbers_variables_in_order_pattern_then_sorts_then_exclusions() {
    start_is(&Prob { t: pv(2), e: vec![], a: vec![(NAT, pv(1))], x: vec![vec![(pv(0), pv(2))]] }, &pv(0), 3, &[vec![(pv(2), pv(0))]], &[vec![], vec![NAT], vec![]]);
}

#[test]
fn start_variable_only_in_exclusion_gets_unsorted_entry() {
    start_is(&Prob { t: pv(4), e: vec![], a: vec![], x: vec![vec![(pv(9), z())]] }, &pv(0), 2, &[vec![(pv(1), z())]], &[vec![], vec![]]);
}

#[test]
fn start_applies_equations_to_exclusions_without_judging_them() {
    start_is(&Prob { t: pv(0), e: vec![(pv(0), z())], a: vec![], x: vec![vec![(pv(0), z())]] }, &z(), 0, &[vec![(z(), z())]], &[]);
}

#[test]
fn start_equation_binding_makes_sort_reject() {
    start_none(&Prob { t: pv(0), e: vec![(pv(0), a())], a: vec![(NAT, pv(0))], x: vec![] });
}

#[test]
fn start_sort_is_pushed_through_equation_binding() {
    start_is(&Prob { t: pv(0), e: vec![(pv(0), pr(pv(1), pv(2)))], a: vec![(PAIR, pv(0))], x: vec![] }, &pr(pv(0), pv(1)), 2, &[], &[vec![NAT], vec![NAT]]);
}

#[test]
fn start_leaves_the_stack_empty_and_works_on_dirty_tables() {
    start_dirty(&Prob { t: f2(pv(5), pv(2)), e: vec![(pv(5), su(pv(1)))], a: vec![(NAT, pv(1)), (SUC, pv(2))], x: vec![vec![(pv(2), pv(1))]] });
}

#[test]
fn normal_of_bare_variable_is_itself() {
    normal_same(wf(), &Prob { t: pv(0), e: vec![], a: vec![], x: vec![] });
}

#[test]
fn normal_of_ground_pattern_has_no_conjunctions() {
    normal_same(wf(), &Prob { t: su(su(z())), e: vec![], a: vec![], x: vec![] });
}

#[test]
fn normal_renumbers_out_of_order_variables() {
    normal_same(wf(), &Prob { t: f2(pv(5), pv(2)), e: vec![], a: vec![], x: vec![] });
}

#[test]
fn normal_keeps_repeated_variable_shared() {
    normal_same(wf(), &Prob { t: pf(F, vec![pv(3), pv(3), pv(1)]), e: vec![], a: vec![], x: vec![] });
}

#[test]
fn normal_substitutes_equation_binding() {
    normal_same(wf(), &Prob { t: f2(pv(0), pv(1)), e: vec![(pv(0), su(pv(1)))], a: vec![], x: vec![] });
}

#[test]
fn normal_alias_equation_identifies_variables() {
    normal_same(wf(), &Prob { t: f2(pv(0), pv(1)), e: vec![(pv(1), pv(0))], a: vec![], x: vec![] });
}

#[test]
fn normal_clashing_equations_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![(pr(pv(0), z()), pr(z(), su(pv(0))))], a: vec![], x: vec![] });
}

#[test]
fn normal_occurs_check_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![(pv(0), pr(pv(1), pv(0)))], a: vec![], x: vec![] });
}

#[test]
fn normal_unsatisfiable_equation_on_hidden_variables_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![(pv(7), su(pv(7)))], a: vec![], x: vec![] });
}

#[test]
fn normal_satisfiable_equation_on_hidden_variables_changes_nothing() {
    normal_same(wf(), &Prob { t: pv(0), e: vec![(pv(7), su(pv(8)))], a: vec![], x: vec![] });
}

#[test]
fn normal_sorted_variable_carries_every_including_sort() {
    normal_same(wf(), &Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0))], x: vec![] });
}

#[test]
fn normal_single_member_sort_replaces_variable_by_value() {
    normal_pattern(&Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![(UNIT, pv(0))], x: vec![] }, &f2(z(), pv(0)));
}

#[test]
fn normal_single_root_sort_keeps_its_variable() {
    normal_pattern(&Prob { t: pv(0), e: vec![], a: vec![(SUC, pv(0))], x: vec![] }, &pv(0));
}

#[test]
fn normal_single_root_sort_with_single_value_arguments_becomes_ground() {
    normal_pattern(&Prob { t: pv(0), e: vec![], a: vec![(TWO, pv(0))], x: vec![] }, &pr(z(), z()));
}

#[test]
fn normal_empty_sort_on_variable_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(VOID, pv(0))], x: vec![] });
}

#[test]
fn normal_empty_sort_under_compound_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(VOID, su(su(pv(0))))], x: vec![] });
}

#[test]
fn normal_intersection_with_single_root_keeps_its_variable() {
    normal_pattern(&Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0)), (SUC, pv(0))], x: vec![] }, &pv(0));
}

#[test]
fn normal_intersection_with_single_value_grounds_variable() {
    normal_pattern(&Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0)), (UNIT, pv(0))], x: vec![] }, &z());
}

#[test]
fn normal_empty_intersection_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(UNIT, pv(0)), (SUC, pv(0))], x: vec![] });
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0)), (PAIR, pv(0))], x: vec![] });
}

#[test]
fn normal_recursive_sort_on_deep_compound_sorts_inner_variable() {
    normal_same(wf(), &Prob { t: pv(0), e: vec![], a: vec![(NAT, su(su(pv(0))))], x: vec![] });
}

#[test]
fn normal_ground_member_changes_nothing() {
    normal_same(wf(), &Prob { t: pv(0), e: vec![], a: vec![(NAT, su(su(z())))], x: vec![] });
}

#[test]
fn normal_ground_non_member_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(PAIR, pr(z(), a()))], x: vec![] });
}

#[test]
fn normal_alias_merges_sorts_of_both_variables() {
    normal_pattern(&Prob { t: f2(pv(0), pv(1)), e: vec![(pv(0), pv(1))], a: vec![(NAT, pv(0)), (SUC, pv(1))], x: vec![] }, &f2(pv(0), pv(0)));
}

#[test]
fn normal_alias_with_disjoint_sorts_is_none() {
    normal_none(wf(), &Prob { t: f2(pv(0), pv(1)), e: vec![(pv(0), pv(1))], a: vec![(UNIT, pv(0)), (SUC, pv(1))], x: vec![] });
}

#[test]
fn normal_sort_on_equation_bound_ground_value() {
    normal_pattern(&Prob { t: pv(0), e: vec![(pv(0), su(z()))], a: vec![(NAT, pv(0))], x: vec![] }, &su(z()));
}

#[test]
fn normal_equation_makes_sort_reject() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![(pv(0), su(z()))], a: vec![(UNIT, pv(0))], x: vec![] });
}

#[test]
fn normal_satisfiable_hidden_sorted_variable_is_cut() {
    normal_same(wf(), &Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(1))], x: vec![] });
}

#[test]
fn normal_unsatisfiable_hidden_variable_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(VOID, pv(1))], x: vec![] });
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(UNIT, pv(1)), (SUC, pv(1))], x: vec![] });
}

#[test]
fn normal_sort_linking_hidden_and_pattern_variable_sorts_pattern_variable() {
    normal_same(wf(), &Prob { t: pv(0), e: vec![], a: vec![(PAIR, pr(pv(0), pv(1)))], x: vec![] });
}

#[test]
fn normal_exclusion_that_always_holds_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![], x: vec![vec![]] });
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![], x: vec![vec![(pv(0), pv(0))]] });
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![], x: vec![vec![(z(), z())]] });
}

#[test]
fn normal_unsatisfiable_exclusion_is_dropped() {
    normal_same(wf(), &Prob { t: pv(0), e: vec![], a: vec![], x: vec![vec![(z(), su(pv(0)))], vec![(pv(0), su(pv(0)))], vec![(pv(0), z()), (pv(0), su(z()))]] });
}

#[test]
fn normal_keeps_exclusion_of_one_value_of_unsorted_variable() {
    normal_same(wf(), &Prob { t: pv(0), e: vec![], a: vec![], x: vec![vec![(pv(0), z())]] });
}

#[test]
fn normal_keeps_disequality_of_two_pattern_variables() {
    normal_same(wf(), &Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![], x: vec![vec![(pv(1), pv(0))]] });
}

#[test]
fn normal_exclusion_of_deep_value_stays() {
    normal_pattern(&Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0))], x: vec![vec![(pv(0), su(z()))]] }, &pv(0));
}

#[test]
fn normal_exclusion_of_only_value_of_sort_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(UNIT, pv(0))], x: vec![vec![(pv(0), z())]] });
}

#[test]
fn normal_exclusion_ruled_out_by_sort_is_dropped() {
    normal_same(wf(), &Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![(SUC, pv(0)), (BOX, pv(1))], x: vec![vec![(pv(0), z())], vec![(pv(0), pv(1))]] });
    normal_same(wf(), &Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0))], x: vec![vec![(pv(0), a())]] });
    normal_same(wf(), &Prob { t: pv(0), e: vec![], a: vec![(ANY, pv(0))], x: vec![vec![(pv(0), a())]] });
}

#[test]
fn normal_exclusion_true_after_equations_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![(pv(0), z())], a: vec![], x: vec![vec![(pv(0), z())]] });
}

#[test]
fn normal_exclusion_false_after_equations_is_dropped() {
    normal_pattern(&Prob { t: pv(0), e: vec![(pv(0), su(z()))], a: vec![], x: vec![vec![(pv(0), z())]] }, &su(z()));
}

#[test]
fn normal_equation_and_exclusion_of_same_alias_is_none() {
    normal_none(wf(), &Prob { t: f2(pv(0), pv(1)), e: vec![(pv(0), pv(1))], a: vec![], x: vec![vec![(pv(1), pv(0))]] });
}

#[test]
fn normal_duplicate_exclusions_are_kept_once() {
    normal_same(wf(), &Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![], x: vec![vec![(pv(0), pv(1))], vec![(pv(1), pv(0))], vec![(pv(0), pv(1))]] });
}

#[test]
fn normal_drops_exclusion_that_is_instance_of_another() {
    normal_same(wf(), &Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![], x: vec![vec![(pv(0), z()), (pv(1), z())], vec![(pv(0), z())]] });
    normal_same(wf(), &Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![], x: vec![vec![(pv(0), pv(1))], vec![(pv(0), z()), (pv(1), z())]] });
}

#[test]
fn normal_exclusion_decomposes_into_solved_bindings() {
    normal_same(wf(), &Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![], x: vec![vec![(pr(pv(0), su(pv(1))), pr(z(), pv(0)))]] });
    normal_same(wf(), &Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![], x: vec![vec![(pr(pv(0), pv(1)), pr(z(), z()))]] });
}

#[test]
fn normal_exclusion_over_hidden_variables_only_is_cut() {
    normal_same(wf(), &Prob { t: pv(0), e: vec![], a: vec![], x: vec![vec![(pv(1), z())], vec![(pv(1), pv(2))]] });
}

#[test]
fn normal_hidden_exclusion_that_empties_hidden_variable_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(UNIT, pv(1))], x: vec![vec![(pv(1), z())]] });
}

#[test]
fn normal_exclusion_mixing_pattern_and_hidden_variable_is_cut() {
    normal_same(wf(), &Prob { t: pv(0), e: vec![], a: vec![], x: vec![vec![(pv(0), pv(1))], vec![(pv(0), z()), (pv(2), z())], vec![(pv(0), su(pv(3)))]] });
}

#[test]
fn normal_hidden_single_value_variable_turns_mixed_exclusion_into_pattern_exclusion() {
    normal_same(wf(), &Prob { t: pv(0), e: vec![], a: vec![(UNIT, pv(1))], x: vec![vec![(pv(0), pv(1))]] });
}

#[test]
fn normal_hidden_single_value_exclusion_narrows_sorted_pattern_variable() {
    let p = Prob { t: pv(0), e: vec![], a: vec![(UNIT, pv(1)), (NAT, pv(0))], x: vec![vec![(pv(0), pv(1))]] };
    normal_is(&p, pv(0), &[&[NAT, SUC, ANY]], &[]);
}

#[test]
fn normal_disequality_of_two_single_member_variables_is_none() {
    normal_none(wf(), &Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![(UNIT, pv(0)), (UNIT, pv(1))], x: vec![vec![(pv(0), pv(1))]] });
}

#[test]
fn normal_disequality_of_variables_of_disjoint_sorts_is_dropped() {
    normal_pattern(&Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![(UNIT, pv(0)), (SUC, pv(1))], x: vec![vec![(pv(0), pv(1))]] }, &f2(z(), pv(0)));
}

#[test]
fn normal_exclusions_coincide_after_tightening_and_are_kept_once() {
    normal_pattern(&Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![(UNIT, pv(1))], x: vec![vec![(pv(0), z())], vec![(pv(0), pv(1))]] }, &f2(pv(0), z()));
}

#[test]
fn normal_exclusion_on_opened_variable_is_rewritten_over_new_variables() {
    normal_pattern(&Prob { t: pv(0), e: vec![], a: vec![(PAIR, pv(0))], x: vec![vec![(pv(0), pr(z(), z()))]] }, &pr(pv(0), pv(1)));
}

#[test]
fn normal_exclusion_on_opened_variable_with_hidden_alias() {
    normal_same(wf(), &Prob { t: pv(0), e: vec![], a: vec![(PAIR, pv(0))], x: vec![vec![(pv(0), pr(pv(1), pv(1)))]] });
}

#[test]
fn normal_exclusion_between_pattern_variable_and_term_over_pattern_variable_is_kept() {
    normal_same(wf(), &Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![(NAT, pv(0)), (NAT, pv(1))], x: vec![vec![(pv(0), su(pv(1)))]] });
}

#[test]
fn normal_exclusion_on_rest_sort_keeps_value_exclusion() {
    normal_pattern(&Prob { t: pv(0), e: vec![], a: vec![(ANY, pv(0))], x: vec![vec![(pv(0), z())]] }, &pv(0));
}

#[test]
fn normal_variable_only_in_exclusion_does_not_appear_in_result() {
    normal_pattern(&Prob { t: su(z()), e: vec![], a: vec![], x: vec![vec![(pv(9), z())]] }, &su(z()));
}

#[test]
fn normal_large_shared_subterms_are_handled_consistently() {
    let big = pr(pr(pv(4), pv(1)), pr(pv(4), pv(1)));
    normal_same(
        wf(),
        &Prob {
            t: f2(big.clone(), f2(big, pv(7))),
            e: vec![(pv(7), pr(pv(1), pv(4)))],
            a: vec![(PAIR, pr(pv(4), pv(1))), (SUC, pv(1))],
            x: vec![vec![(pv(4), z())], vec![(pv(4), pv(1))]],
        },
    );
}

#[test]
fn normal_everything_at_once_small() {
    normal_same(wf(), &Prob { t: f2(pv(3), pv(0)), e: vec![(pv(3), su(pv(2)))], a: vec![(NAT, pv(2)), (BOX, pv(0)), (UNIT, pv(5))], x: vec![vec![(pv(2), pv(5))], vec![(pv(0), k1(z()))], vec![(pv(6), pv(0))]] });
}

#[test]
fn normal_leaves_the_stack_empty_and_works_on_dirty_tables() {
    normal_dirty(&Prob { t: f2(pv(3), pv(0)), e: vec![(pv(3), su(pv(2)))], a: vec![(NAT, pv(2)), (BOX, pv(0))], x: vec![vec![(pv(0), k1(su(z())))]] });
}

#[test]
fn normal_of_a_normal_store_is_that_store() {
    for prob in [
        Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![(NAT, pv(0))], x: vec![vec![(pv(0), su(z()))], vec![(pv(1), pv(0))]] },
        Prob { t: pv(0), e: vec![], a: vec![(PAIR, pv(0))], x: vec![vec![(pv(0), pr(z(), z()))]] },
    ] {
        let fst = common::sorts::normal(&Sorts::new(wf()), &prob).expect("a store");
        normal_same(wf(), &fst.prob());
        let again = common::sorts::normal(&Sorts::new(wf()), &fst.prob()).expect("a store");
        assert_eq!(fst, again, "the reference is not idempotent on {prob:?}");
        let got = run_normal(wf(), &fst.prob(), false).expect("a store");
        assert_eq!(got, shape(&fst));
    }
}

// Hidden variables: the ones of the sorted patterns and the exclusions that
// do not occur in the pattern.

/// `normal` gives the store written by hand: the pattern `t`, the sorts `c`
/// of its variables in order, and the exclusions `x`, each the variables it
/// moves with their values. It is the store of the reference.
fn normal_is(p: &Prob, t: P, c: &[&[Name]], x: &[&[(usize, P)]]) {
    let want = Raw {
        t,
        c: c.iter().map(|l| l.iter().copied().collect()).collect(),
        x: x.iter().map(|b| b.to_vec()).collect(),
    };
    let reference = common::sorts::normal(&Sorts::new(wf()), p);
    assert_eq!(reference.as_ref(), Some(&want), "the reference on {p:?}");
    assert_eq!(run_normal(wf(), p, false), Some(shape(&want)), "{p:?}");
}

/// `normal` gives the problem `p` the store it gives `q`, and that is the
/// store of the reference for both.
fn normal_as(p: &Prob, q: &Prob) {
    normal_same(wf(), p);
    normal_same(wf(), q);
    assert_eq!(run_normal(wf(), p, false), run_normal(wf(), q, false), "{p:?} and {q:?}");
}

#[test]
fn normal_drops_a_hidden_variable_with_an_infinite_sort() {
    normal_is(&Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![(NAT, pv(2))], x: vec![] }, f2(pv(0), pv(1)), &[&[], &[]], &[]);
}

#[test]
fn normal_drops_a_hidden_variable_and_keeps_the_sorts_of_the_pattern_variables() {
    normal_is(
        &Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![(NAT, pv(1)), (NAT, pv(2)), (ANY, pv(3))], x: vec![] },
        f2(pv(0), pv(1)),
        &[&[], &[NAT, ANY]],
        &[],
    );
}

#[test]
fn normal_puts_the_one_member_of_a_hidden_variable_in_an_exclusion_before_judging_it() {
    // `x != (s h)` with `h` the one `unit` is `x != (s z)`.
    let p = Prob { t: pv(0), e: vec![], a: vec![(UNIT, pv(1))], x: vec![vec![(pv(0), su(pv(1)))]] };
    normal_is(&p, pv(0), &[&[]], &[&[(0, su(z()))]]);
    normal_as(&p, &Prob { t: pv(0), e: vec![], a: vec![], x: vec![vec![(pv(0), su(z()))]] });
}

#[test]
fn normal_puts_the_one_compound_member_of_a_hidden_variable_in_an_exclusion() {
    let p = Prob { t: pv(0), e: vec![], a: vec![(TWO, pv(1))], x: vec![vec![(pv(0), k1(pv(1)))]] };
    normal_is(&p, pv(0), &[&[]], &[&[(0, k1(pr(z(), z())))]]);
}

#[test]
fn normal_exclusion_with_the_one_member_of_a_hidden_variable_narrows_a_sorted_pattern_variable() {
    // `x != h` with `h` the one `unit` leaves a `nat` its successors only.
    let p = Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0)), (UNIT, pv(1))], x: vec![vec![(pv(1), pv(0))]] };
    normal_is(&p, pv(0), &[&[NAT, SUC, ANY]], &[]);
}

#[test]
fn normal_exclusion_of_the_one_member_of_a_hidden_variable_from_itself_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(TWO, pv(1))], x: vec![vec![(pv(1), pr(z(), z()))]] });
}

#[test]
fn normal_hidden_variable_without_a_value_is_none_though_its_exclusion_would_be_dropped() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(VOID, pv(1))], x: vec![vec![(pv(0), pv(1))]] });
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(1)), (PAIR, pv(1))], x: vec![vec![(pv(1), z())]] });
}

#[test]
fn normal_hidden_variable_without_a_value_under_a_sorted_pattern_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(PAIR, pr(pv(1), pv(2))), (BOX, pv(2))], x: vec![] });
}

#[test]
fn normal_drops_an_exclusion_of_a_sorted_hidden_variable_from_a_ground_term() {
    normal_is(&Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(1))], x: vec![vec![(pv(1), su(z()))]] }, pv(0), &[&[]], &[]);
}

#[test]
fn normal_drops_an_exclusion_of_a_hidden_variable_from_a_term_over_the_pattern_variable() {
    normal_is(&Prob { t: pv(0), e: vec![], a: vec![], x: vec![vec![(pv(1), pr(pv(0), z()))]] }, pv(0), &[&[]], &[]);
}

#[test]
fn normal_drops_an_exclusion_of_the_pattern_variable_from_a_term_over_a_hidden_variable() {
    normal_is(&Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(1))], x: vec![vec![(pv(0), k1(pv(1)))]] }, pv(0), &[&[]], &[]);
}

#[test]
fn normal_drops_an_exclusion_of_a_sorted_pattern_variable_from_a_term_over_a_hidden_variable() {
    // `x != (s h)` leaves a `nat` `x` every value: `z` is not excluded.
    normal_is(
        &Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0)), (NAT, pv(1))], x: vec![vec![(pv(0), su(pv(1)))]] },
        pv(0),
        &[&[NAT, ANY]],
        &[],
    );
}

#[test]
fn normal_exclusion_with_a_hidden_variable_equal_to_itself_is_the_rest_of_it() {
    // `[(h, h), (x, (s z))]` is `x != (s z)`.
    let p = Prob { t: pv(0), e: vec![], a: vec![], x: vec![vec![(pv(1), pv(1)), (pv(0), su(z()))]] };
    normal_is(&p, pv(0), &[&[]], &[&[(0, su(z()))]]);
}

#[test]
fn normal_exclusion_with_a_hidden_variable_equal_to_itself_gives_the_store_of_the_rest_of_it() {
    // `[(h, h), (x, a)]` is `x != a`, written before or after, sorted or not.
    let bare = Prob { t: pv(0), e: vec![], a: vec![], x: vec![vec![(pv(0), a())]] };
    normal_as(&Prob { x: vec![vec![(pv(1), pv(1)), (pv(0), a())]], ..bare.clone() }, &bare);
    normal_as(&Prob { x: vec![vec![(pv(0), a()), (pv(1), pv(1))]], ..bare.clone() }, &bare);
    normal_as(&Prob { a: vec![(NAT, pv(1))], x: vec![vec![(pv(1), pv(1)), (pv(0), a())]], ..bare.clone() }, &bare);
}

#[test]
fn normal_exclusion_with_a_hidden_variable_at_the_same_place_on_both_sides_is_the_rest_of_it() {
    let p = Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(1))], x: vec![vec![(pr(pv(1), pv(0)), pr(pv(1), z()))]] };
    normal_is(&p, pv(0), &[&[]], &[&[(0, z())]]);
}

#[test]
fn normal_exclusion_with_a_hidden_variable_equal_to_itself_narrows_a_sorted_pattern_variable() {
    // `[(h, h), (x, z)]` is `x != z`, which leaves a `nat` its successors.
    let p = Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0))], x: vec![vec![(pv(1), pv(1)), (pv(0), z())]] };
    normal_is(&p, pv(0), &[&[NAT, SUC, ANY]], &[]);
}

#[test]
fn normal_exclusion_of_a_hidden_variable_from_itself_is_none() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![], x: vec![vec![(pv(1), pv(1))]] });
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(1))], x: vec![vec![(su(pv(1)), su(pv(1)))]] });
}

#[test]
fn normal_exclusion_that_always_holds_once_the_pattern_variable_has_its_one_value_is_none_with_a_hidden_variable_in_it() {
    normal_none(wf(), &Prob { t: pv(0), e: vec![], a: vec![(UNIT, pv(0))], x: vec![vec![(pv(0), z()), (pv(1), pv(1))]] });
}

#[test]
fn normal_drops_an_exclusion_between_two_hidden_variables() {
    normal_is(&Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(1)), (NAT, pv(2))], x: vec![vec![(pv(1), pv(2))]] }, pv(0), &[&[]], &[]);
    normal_is(&Prob { t: pv(0), e: vec![], a: vec![], x: vec![vec![(pv(2), pv(1))]] }, pv(0), &[&[]], &[]);
}

#[test]
fn normal_drops_an_exclusion_between_the_pattern_variable_and_a_hidden_one_in_both_orders() {
    normal_is(&Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0)), (NAT, pv(1))], x: vec![vec![(pv(0), pv(1))]] }, pv(0), &[&[NAT, ANY]], &[]);
    normal_is(&Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0)), (NAT, pv(1))], x: vec![vec![(pv(1), pv(0))]] }, pv(0), &[&[NAT, ANY]], &[]);
}

#[test]
fn normal_drops_an_exclusion_that_makes_two_pattern_variables_equal_through_a_hidden_one() {
    // Not `x != y`: the hidden variable can differ from both.
    normal_is(
        &Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![], x: vec![vec![(pv(0), pv(2)), (pv(1), pv(2))]] },
        f2(pv(0), pv(1)),
        &[&[], &[]],
        &[],
    );
}

#[test]
fn normal_drops_an_exclusion_that_chains_through_a_hidden_variable_to_a_ground_term() {
    // Not `x != a`: the hidden variable can be another term than `a`.
    normal_is(&Prob { t: pv(0), e: vec![], a: vec![], x: vec![vec![(pv(0), pv(1)), (pv(1), a())]] }, pv(0), &[&[]], &[]);
}

#[test]
fn normal_keeps_the_exclusion_over_the_pattern_among_dropped_ones() {
    let p = Prob {
        t: f2(pv(0), pv(1)),
        e: vec![],
        a: vec![(NAT, pv(2))],
        x: vec![vec![(pv(0), pv(2))], vec![(pv(1), su(pv(0)))], vec![(pv(2), z())], vec![(pv(3), pv(2))]],
    };
    normal_is(&p, f2(pv(0), pv(1)), &[&[], &[]], &[&[(1, su(pv(0)))]]);
}

#[test]
fn normal_hidden_variable_whose_values_have_one_root_changes_nothing() {
    let bare = Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![(NAT, pv(1))], x: vec![] };
    for n in [SUC, BOX, PAIR, MIX, C2, C3] {
        let p = Prob { a: vec![(NAT, pv(1)), (n, pv(2))], ..bare.clone() };
        normal_as(&p, &bare);
    }
}

#[test]
fn normal_hidden_variable_left_one_root_by_an_exclusion_changes_nothing() {
    // `h` is a `nat` and not `z`: every value of it is a successor.
    let bare = Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0))], x: vec![] };
    let p = Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0)), (NAT, pv(1))], x: vec![vec![(pv(1), z())]] };
    normal_as(&p, &bare);
    normal_is(&p, pv(0), &[&[NAT, ANY]], &[]);
}

#[test]
fn normal_drops_an_exclusion_over_a_hidden_variable_whose_values_have_one_root() {
    // `x != h` with `h` a pair of `nat`, and `h` not the pair of two `z`.
    let p = Prob {
        t: pv(0),
        e: vec![],
        a: vec![(PAIR, pv(1))],
        x: vec![vec![(pv(0), pv(1))], vec![(pv(1), pr(z(), z()))]],
    };
    normal_is(&p, pv(0), &[&[]], &[]);
}

#[test]
fn normal_drops_a_hidden_variable_and_leaves_the_pattern_variable_of_the_same_sort_folded() {
    let p = Prob { t: pv(0), e: vec![], a: vec![(C3, pv(0)), (C3, pv(1))], x: vec![vec![(pv(0), pv(1))]] };
    normal_is(&p, pv(0), &[&[C3, ANY]], &[]);
}

#[test]
fn normal_hidden_variables_leave_the_stack_empty_and_work_on_dirty_tables() {
    normal_dirty(&Prob {
        t: f2(pv(0), pv(1)),
        e: vec![],
        a: vec![(NAT, pv(0)), (UNIT, pv(2)), (C2, pv(3)), (NAT, pv(4))],
        x: vec![vec![(pv(0), su(pv(2)))], vec![(pv(1), pv(3))], vec![(pv(4), pv(4)), (pv(1), a())], vec![(pv(4), z())]],
    });
}

// The cost of a hidden variable.

const T0: Name = 200;

/// `t0` is `z` or `s` of a `t0`, and `t(i)` is `f` of two `t(i-1)`, up to
/// `t(k)`: each has one root from `t1` on, and infinitely many members.
fn tower(k: u32) -> Vec<(Name, Def)> {
    let mut defs = vec![(T0, Def { cases: vec![(Z, vec![]), (SU, vec![Some(T0)])], rest: None })];
    for i in 1..=k {
        defs.push((T0 + i, one(F, vec![Some(T0 + i - 1), Some(T0 + i - 1)])));
    }
    defs
}

/// The problem of the pattern `x` with a hidden variable in `t(k)`.
fn hidden_in_tower(k: u32) -> Prob {
    Prob { t: pv(0), e: vec![], a: vec![(T0 + k, pv(1))], x: vec![] }
}

/// The normal store of the problem under the towers up to `k`, and the
/// ticks `normal` spent on it.
fn normal_ticks(k: u32, p: &Prob) -> (Option<Shape>, u64) {
    let mut f = fixture(tower(k));
    let (t, e, a, x) = put_prob(&mut f, p);
    let (decls, names) = (f.decls, f.names);
    let (got, ticks) = spent(&mut f.s, |s| normal(s, decls, names, t, e, a, x));
    f.empty_stack();
    let got = got.map(|r| {
        let t1 = get(&mut f.s, r.t);
        let cs = get_conjs(&mut f.s, r.c).into_iter().map(sorted).collect();
        let xs = get_lists(&mut f, r.x).iter().map(|l| format!("{l:?}")).collect();
        (t1, cs, sorted(xs))
    });
    (got, ticks)
}

#[test]
fn normal_does_not_expand_a_hidden_variable_with_one_root() {
    // Replacing the hidden variable by its root down to `t0` takes `2^k - 1`
    // replacements. Dropping it takes none: twice the depth is then at most
    // a fixed power of two times the work, far below the `2^k` of expanding.
    let k = 8;
    let want = Raw { t: pv(0), c: vec![Conj::new()], x: vec![] };
    let reference = common::sorts::normal(&Sorts::new(tower(k)), &hidden_in_tower(k));
    assert_eq!(reference.as_ref(), Some(&want), "the reference at depth {k}");
    let (shallow, t1) = normal_ticks(k, &hidden_in_tower(k));
    let (deep, t2) = normal_ticks(2 * k, &hidden_in_tower(2 * k));
    assert_eq!(shallow, Some(shape(&want)), "depth {k}");
    assert_eq!(deep, Some(shape(&want)), "depth {}", 2 * k);
    assert!(t2 <= 16 * t1, "{t1} ticks at depth {k} and {t2} at depth {}", 2 * k);
}

// # The folded store
//
// The canonical store leaves a subterm folded, as one variable with the
// sorts of the subterm, when nothing but its sorts is said of it
// (`lean/RwLog/Sorts/FoldRaw.lean`). Only a variable that an exclusion
// mentions is written out.

const NIL: u32 = 8;
const CONS: u32 = 9;
const KK: Name = 120;
const NOK: Name = 121;
const M2: Name = 122;
const LIST: Name = 123;
const NE: Name = 124;
const SA: Name = 125;
const B2: Name = 126;

fn g2(p: P, q: P) -> P {
    pf(G, vec![p, q])
}

fn with(extra: Vec<(Name, Def)>) -> Vec<(Name, Def)> {
    let mut d = wf();
    d.extend(extra);
    d
}

fn without(gone: &[Name], extra: Vec<(Name, Def)>) -> Vec<(Name, Def)> {
    let mut d: Vec<(Name, Def)> = wf().into_iter().filter(|(n, _)| !gone.contains(n)).collect();
    d.extend(extra);
    d
}

fn prob(t: P, a: Vec<(Name, P)>, x: Vec<Vec<(P, P)>>) -> Prob {
    Prob { t, e: vec![], a, x }
}

/// Both the reference and `normal` give the store of the pattern `t`, the
/// sorts `c` of its variables and the exclusions `x`; and that store, as a
/// problem, gives itself.
fn folded_is(defs: Vec<(Name, Def)>, p: &Prob, t: P, c: &[&[Name]], x: Vec<Binds>) {
    let want = Raw { t, c: c.iter().map(|l| l.iter().copied().collect()).collect(), x };
    let sorts = Sorts::new(defs.clone());
    assert_eq!(common::sorts::normal(&sorts, p).as_ref().map(shape), Some(shape(&want)), "the reference on {p:?}");
    assert_eq!(
        common::sorts::normal(&sorts, &want.prob()).as_ref().map(shape),
        Some(shape(&want)),
        "the reference on its own store for {p:?}"
    );
    assert_eq!(run_normal(defs.clone(), p, false), Some(shape(&want)), "{p:?}");
    assert_eq!(run_normal(defs, &want.prob(), false), Some(shape(&want)), "the store of {p:?} as a problem");
}

const N: &[Name] = &[NAT, ANY];
const S: &[Name] = &[NAT, SUC, ANY];

#[test]
fn fold_single_root_sort_without_exclusion_stays_a_variable() {
    folded_is(wf(), &prob(pv(0), vec![(BOX, pv(0))], vec![]), pv(0), &[&[BOX, ANY]], vec![]);
}

#[test]
fn fold_nested_single_root_sort_stays_a_variable() {
    folded_is(wf(), &prob(pv(0), vec![(C3, pv(0))], vec![]), pv(0), &[&[C3, ANY]], vec![]);
}

#[test]
fn fold_nat_without_zero_is_a_variable_of_the_successors() {
    folded_is(wf(), &prob(pv(0), vec![(NAT, pv(0))], vec![vec![(pv(0), z())]]), pv(0), &[S], vec![]);
}

#[test]
fn fold_exclusion_leaving_two_roots_keeps_variable_and_exclusion() {
    folded_is(wf(), &prob(pv(0), vec![(NAT, pv(0))], vec![vec![(pv(0), su(z()))]]), pv(0), &[N], vec![vec![(0, su(z()))]]);
}

#[test]
fn fold_exclusion_inside_box_writes_the_box_out() {
    folded_is(wf(), &prob(pv(0), vec![(BOX, pv(0))], vec![vec![(pv(0), k1(z()))]]), k1(pv(0)), &[S], vec![]);
}

#[test]
fn fold_exclusion_two_levels_down_writes_both_levels_out() {
    folded_is(wf(), &prob(pv(0), vec![(C2, pv(0))], vec![vec![(pv(0), k1(k1(z())))]]), k1(k1(pv(0))), &[S], vec![]);
}

#[test]
fn fold_exclusion_on_both_parts_of_a_pair_writes_the_pair_out_and_stays() {
    folded_is(
        wf(),
        &prob(pv(0), vec![(PAIR, pv(0))], vec![vec![(pv(0), pr(z(), z()))]]),
        pr(pv(0), pv(1)),
        &[N, N],
        vec![vec![(0, z()), (1, z())]],
    );
}

#[test]
fn fold_only_the_variable_an_exclusion_mentions_is_written_out() {
    folded_is(
        wf(),
        &prob(f2(pv(0), pv(1)), vec![(BOX, pv(0)), (BOX, pv(1))], vec![vec![(pv(0), k1(z()))]]),
        f2(k1(pv(0)), pv(1)),
        &[S, &[BOX, ANY]],
        vec![],
    );
}

#[test]
fn fold_exclusion_that_cannot_hold_leaves_the_variable_folded() {
    folded_is(wf(), &prob(pv(0), vec![(BOX, pv(0))], vec![vec![(pv(0), a())]]), pv(0), &[&[BOX, ANY]], vec![]);
}

#[test]
fn fold_exclusion_settles_one_argument_and_narrows_the_other() {
    folded_is(wf(), &prob(pv(0), vec![(MIX, pv(0))], vec![vec![(pv(0), g2(z(), z()))]]), g2(z(), pv(0)), &[S], vec![]);
}

#[test]
fn fold_bare_variable_is_not_a_subterm_to_fold() {
    folded_is(wf(), &prob(pv(0), vec![(NAT, pv(0))], vec![]), pv(0), &[N], vec![]);
}

#[test]
fn fold_ground_pattern_is_not_folded() {
    folded_is(wf(), &prob(pr(z(), z()), vec![], vec![]), pr(z(), z()), &[], vec![]);
}

#[test]
fn fold_sort_with_one_member_is_written_as_the_member() {
    folded_is(wf(), &prob(pv(0), vec![(TWO, pv(0))], vec![]), pr(z(), z()), &[], vec![]);
}

#[test]
fn fold_subterm_with_a_variable_twice_is_not_folded() {
    folded_is(wf(), &prob(pr(pv(0), pv(0)), vec![(NAT, pv(0))], vec![]), pr(pv(0), pv(0)), &[N], vec![]);
}

#[test]
fn fold_subterm_whose_variable_occurs_outside_it_is_not_folded() {
    folded_is(wf(), &prob(f2(k1(pv(0)), pv(0)), vec![(NAT, pv(0))], vec![]), f2(k1(pv(0)), pv(0)), &[N], vec![]);
}

#[test]
fn fold_subterm_whose_variable_an_exclusion_mentions_is_not_folded() {
    folded_is(
        wf(),
        &prob(k1(pv(0)), vec![(NAT, pv(0))], vec![vec![(pv(0), su(z()))]]),
        k1(pv(0)),
        &[N],
        vec![vec![(0, su(z()))]],
    );
}

#[test]
fn fold_subterm_narrower_than_every_declared_sort_is_not_folded() {
    folded_is(wf(), &prob(k1(pv(0)), vec![(SUC, pv(0))], vec![]), k1(pv(0)), &[S], vec![]);
}

#[test]
fn fold_subterm_that_is_exactly_a_sort_becomes_a_variable_of_it() {
    folded_is(wf(), &prob(k1(pv(0)), vec![(NAT, pv(0))], vec![]), pv(0), &[&[BOX, ANY]], vec![]);
}

#[test]
fn fold_subterm_of_unsorted_variables_is_not_folded() {
    folded_is(wf(), &prob(f2(pv(0), pv(1)), vec![], vec![]), f2(pv(0), pv(1)), &[&[], &[]], vec![]);
}

#[test]
fn fold_successor_is_not_folded_when_no_sort_is_the_successors() {
    folded_is(without(&[SUC], vec![]), &prob(su(pv(0)), vec![(NAT, pv(0))], vec![]), su(pv(0)), &[N], vec![]);
}

#[test]
fn fold_successor_is_folded_when_a_sort_is_the_successors() {
    folded_is(wf(), &prob(su(pv(0)), vec![(NAT, pv(0))], vec![]), pv(0), &[S], vec![]);
}

#[test]
fn fold_sort_with_the_symbol_at_two_arities_does_not_fold() {
    let kk = Def { cases: vec![(K, vec![Some(NAT)]), (K, vec![Some(NAT), Some(NAT)])], rest: None };
    folded_is(without(&[BOX, C2, C3], vec![(KK, kk)]), &prob(k1(pv(0)), vec![(NAT, pv(0))], vec![]), k1(pv(0)), &[N], vec![]);
}

#[test]
fn fold_wider_sort_is_carried_with_the_exact_one() {
    let kk = Def { cases: vec![(K, vec![Some(NAT)]), (K, vec![Some(NAT), Some(NAT)])], rest: None };
    folded_is(with(vec![(KK, kk)]), &prob(k1(pv(0)), vec![(NAT, pv(0))], vec![]), pv(0), &[&[BOX, ANY, KK]], vec![]);
}

#[test]
fn fold_three_nested_boxes_fold_to_one_variable() {
    folded_is(wf(), &prob(k1(k1(k1(pv(0)))), vec![(NAT, pv(0))], vec![]), pv(0), &[&[C3, ANY]], vec![]);
}

#[test]
fn fold_inner_subterm_folds_when_the_outer_one_does_not() {
    folded_is(wf(), &prob(su(su(pv(0))), vec![(NAT, pv(0))], vec![]), su(pv(0)), &[S], vec![]);
}

#[test]
fn fold_subterm_of_an_unsorted_variable_under_a_sorted_symbol_is_not_folded() {
    folded_is(wf(), &prob(k1(pv(0)), vec![], vec![]), k1(pv(0)), &[&[]], vec![]);
}

#[test]
fn fold_sort_that_rejects_the_root_is_not_among_the_sorts_of_the_subterm() {
    let nok = Def { cases: vec![], rest: Some((vec![(K, 1)], None)) };
    folded_is(with(vec![(NOK, nok)]), &prob(k1(pv(0)), vec![(NAT, pv(0))], vec![]), pv(0), &[&[BOX, ANY]], vec![]);
}

#[test]
fn fold_subterm_with_a_constant_the_sort_requires_is_folded() {
    folded_is(wf(), &prob(g2(z(), pv(0)), vec![(NAT, pv(0))], vec![]), pv(0), &[&[MIX, ANY]], vec![]);
}

#[test]
fn fold_subterm_with_a_constant_the_sort_does_not_require_is_not_folded() {
    folded_is(wf(), &prob(pr(z(), pv(0)), vec![(NAT, pv(0))], vec![]), pr(z(), pv(0)), &[N], vec![]);
}

#[test]
fn fold_unsorted_variable_fits_an_argument_of_any_term() {
    folded_is(
        with(vec![(M2, one(G, vec![None, Some(NAT)]))]),
        &prob(g2(pv(0), pv(1)), vec![(NAT, pv(1))], vec![]),
        pv(0),
        &[&[ANY, M2]],
        vec![],
    );
}

#[test]
fn fold_sorted_variable_does_not_fit_an_argument_of_any_term() {
    folded_is(
        with(vec![(M2, one(G, vec![None, Some(NAT)]))]),
        &prob(g2(pv(0), pv(1)), vec![(NAT, pv(0)), (NAT, pv(1))], vec![]),
        g2(pv(0), pv(1)),
        &[N, N],
        vec![],
    );
}

#[test]
fn fold_constant_folds_through_the_sort_that_requires_it() {
    folded_is(
        with(vec![(M2, one(G, vec![None, Some(NAT)]))]),
        &prob(g2(z(), pv(0)), vec![(NAT, pv(0))], vec![]),
        pv(0),
        &[&[MIX, ANY, M2]],
        vec![],
    );
}

fn list() -> Def {
    Def { cases: vec![(NIL, vec![]), (CONS, vec![Some(NAT), Some(LIST)])], rest: None }
}

#[test]
fn fold_cons_is_not_folded_when_no_sort_is_the_nonempty_lists() {
    folded_is(
        with(vec![(LIST, list())]),
        &prob(pf(CONS, vec![pv(0), pv(1)]), vec![(NAT, pv(0)), (LIST, pv(1))], vec![]),
        pf(CONS, vec![pv(0), pv(1)]),
        &[N, &[ANY, LIST]],
        vec![],
    );
}

#[test]
fn fold_cons_is_folded_when_a_sort_is_the_nonempty_lists() {
    folded_is(
        with(vec![(LIST, list()), (NE, one(CONS, vec![Some(NAT), Some(LIST)]))]),
        &prob(pf(CONS, vec![pv(0), pv(1)]), vec![(NAT, pv(0)), (LIST, pv(1))], vec![]),
        pv(0),
        &[&[ANY, LIST, NE]],
        vec![],
    );
}

fn sa() -> Vec<(Name, Def)> {
    with(vec![(SA, Def { cases: vec![(SU, vec![Some(NAT)]), (A, vec![])], rest: None })])
}

#[test]
fn fold_two_sorts_meeting_in_one_root_stay_a_variable() {
    folded_is(sa(), &prob(pv(0), vec![(NAT, pv(0)), (SA, pv(0))], vec![]), pv(0), &[&[NAT, SUC, ANY, SA]], vec![]);
}

#[test]
fn fold_variable_of_the_successors_carries_every_sort_above_them() {
    folded_is(sa(), &prob(pv(0), vec![(SUC, pv(0))], vec![]), pv(0), &[&[NAT, SUC, ANY, SA]], vec![]);
}

#[test]
fn fold_written_out_successor_folds_to_the_same_store_as_the_sorted_variable() {
    folded_is(sa(), &prob(su(pv(0)), vec![(NAT, pv(0))], vec![]), pv(0), &[&[NAT, SUC, ANY, SA]], vec![]);
}

#[test]
fn fold_argument_sorts_of_several_sorts_are_met_at_the_leaf() {
    folded_is(
        with(vec![(B2, one(K, vec![Some(SUC)]))]),
        &prob(k1(pv(0)), vec![(SUC, pv(0))], vec![]),
        pv(0),
        &[&[BOX, ANY, B2]],
        vec![],
    );
}

#[test]
fn fold_only_the_outermost_free_subterm_is_folded() {
    folded_is(wf(), &prob(k1(k1(k1(k1(pv(0))))), vec![(NAT, pv(0))], vec![]), k1(pv(0)), &[&[C3, ANY]], vec![]);
}

#[test]
fn fold_two_free_subterms_become_two_variables_in_order() {
    folded_is(
        wf(),
        &prob(f2(k1(pv(0)), pr(pv(1), pv(2))), vec![(NAT, pv(0)), (NAT, pv(1)), (NAT, pv(2))], vec![]),
        f2(pv(0), pv(1)),
        &[&[BOX, ANY], &[PAIR, ANY]],
        vec![],
    );
}

#[test]
fn fold_variables_after_a_folded_subterm_are_numbered_down() {
    folded_is(
        wf(),
        &prob(f2(pr(pv(0), pv(1)), pv(2)), vec![(NAT, pv(0)), (NAT, pv(1)), (NAT, pv(2))], vec![]),
        f2(pv(0), pv(1)),
        &[&[PAIR, ANY], N],
        vec![],
    );
}

#[test]
fn fold_repeated_variable_keeps_one_number_around_a_folded_subterm() {
    folded_is(
        wf(),
        &prob(f2(f2(pv(0), pr(pv(1), pv(2))), pv(0)), vec![(NAT, pv(0)), (NAT, pv(1)), (NAT, pv(2))], vec![]),
        f2(f2(pv(0), pv(1)), pv(0)),
        &[N, &[PAIR, ANY]],
        vec![],
    );
}

#[test]
fn fold_the_same_free_subterm_twice_is_one_variable_twice() {
    folded_is(wf(), &prob(f2(k1(pv(0)), k1(pv(0))), vec![(NAT, pv(0))], vec![]), f2(pv(0), pv(0)), &[&[BOX, ANY]], vec![]);
}

#[test]
fn fold_exclusion_follows_its_variable_to_the_new_number() {
    folded_is(
        wf(),
        &prob(
            f2(pr(pv(0), pv(1)), pv(2)),
            vec![(NAT, pv(0)), (NAT, pv(1)), (NAT, pv(2))],
            vec![vec![(pv(2), su(z()))]],
        ),
        f2(pv(0), pv(1)),
        &[&[PAIR, ANY], N],
        vec![vec![(1, su(z()))]],
    );
}

#[test]
fn fold_variable_on_the_right_of_an_exclusion_keeps_its_subterm_written_out() {
    folded_is(
        wf(),
        &prob(f2(pv(0), k1(pv(1))), vec![(NAT, pv(1))], vec![vec![(pv(0), k1(pv(1)))]]),
        f2(pv(0), k1(pv(1))),
        &[&[], N],
        vec![vec![(0, k1(pv(1)))]],
    );
}

#[test]
fn fold_exclusion_between_a_box_and_its_content_writes_the_box_out() {
    folded_is(
        wf(),
        &prob(f2(pv(0), pv(1)), vec![(BOX, pv(0)), (NAT, pv(1))], vec![vec![(pv(0), k1(pv(1)))]]),
        f2(k1(pv(0)), pv(1)),
        &[N, N],
        vec![vec![(1, pv(0))]],
    );
}

#[test]
fn fold_pair_of_two_different_nats_is_not_folded() {
    folded_is(
        wf(),
        &prob(pr(pv(0), pv(1)), vec![(NAT, pv(0)), (NAT, pv(1))], vec![vec![(pv(0), pv(1))]]),
        pr(pv(0), pv(1)),
        &[N, N],
        vec![vec![(1, pv(0))]],
    );
}

#[test]
fn fold_pair_of_two_nats_is_a_variable_of_the_pairs() {
    folded_is(wf(), &prob(pr(pv(0), pv(1)), vec![(NAT, pv(0)), (NAT, pv(1))], vec![]), pv(0), &[&[PAIR, ANY]], vec![]);
}

#[test]
fn fold_nat_without_zero_and_one_is_the_successor_of_a_successor_variable() {
    folded_is(
        wf(),
        &prob(pv(0), vec![(NAT, pv(0))], vec![vec![(pv(0), z())], vec![(pv(0), su(z()))]]),
        su(pv(0)),
        &[S],
        vec![],
    );
}

/// The problems have the same canonical store, in the reference and in
/// `normal`.
fn same_store(defs: Vec<(Name, Def)>, ps: &[Prob]) {
    let sorts = Sorts::new(defs.clone());
    let want = common::sorts::normal(&sorts, &ps[0]).as_ref().map(shape);
    assert!(want.is_some(), "the reference has no store for {:?}", ps[0]);
    for p in ps {
        assert_eq!(common::sorts::normal(&sorts, p).as_ref().map(shape), want, "the reference on {p:?}");
        assert_eq!(run_normal(defs.clone(), p, false), want, "{p:?}");
    }
}

#[test]
fn fold_sorted_variable_and_its_written_out_forms_have_one_store() {
    same_store(
        wf(),
        &[
            prob(pv(0), vec![(C3, pv(0))], vec![]),
            prob(k1(pv(0)), vec![(C2, pv(0))], vec![]),
            prob(k1(k1(k1(pv(0)))), vec![(NAT, pv(0))], vec![]),
        ],
    );
}

#[test]
fn fold_exclusion_against_a_box_variable_and_against_the_box_written_out_have_one_store() {
    same_store(
        wf(),
        &[
            prob(f2(pv(0), pv(1)), vec![(BOX, pv(1))], vec![vec![(pv(0), pv(1))]]),
            prob(f2(pv(0), k1(pv(1))), vec![(NAT, pv(1))], vec![vec![(pv(0), k1(pv(1)))]]),
        ],
    );
}

#[test]
fn fold_three_ways_to_say_at_least_two_have_one_store() {
    same_store(
        wf(),
        &[
            prob(su(pv(0)), vec![(SUC, pv(0))], vec![]),
            prob(su(su(pv(0))), vec![(NAT, pv(0))], vec![]),
            prob(pv(0), vec![(NAT, pv(0))], vec![vec![(pv(0), z())], vec![(pv(0), su(z()))]]),
        ],
    );
}

#[test]
fn fold_empty_sort_under_a_symbol_is_none() {
    normal_none(wf(), &prob(k1(pv(0)), vec![(VOID, pv(0))], vec![]));
}

#[test]
fn fold_sorts_with_nothing_in_common_are_none() {
    normal_none(wf(), &prob(pv(0), vec![(UNIT, pv(0)), (SUC, pv(0))], vec![]));
}

#[test]
fn fold_exclusion_of_the_only_member_is_none() {
    normal_none(wf(), &prob(pv(0), vec![(UNIT, pv(0))], vec![vec![(pv(0), z())]]));
}

#[test]
fn fold_dirty_tables_do_not_change_the_folded_store() {
    normal_dirty(&prob(f2(k1(pv(0)), pr(pv(1), pv(2))), vec![(NAT, pv(0)), (NAT, pv(1)), (NAT, pv(2))], vec![]));
}

#[test]
fn normal_does_not_write_out_a_pattern_variable_with_one_root() {
    // Writing the variable out down to `t0` takes `2^k - 1` replacements.
    // Leaving it folded takes none: twice the depth is then at most a fixed
    // power of two times the work, far below the `2^k` of writing it out.
    let k = 8;
    let p = |k: u32| Prob { t: pv(0), e: vec![], a: vec![(T0 + k, pv(0))], x: vec![] };
    let want = |k: u32| Raw { t: pv(0), c: vec![Conj::from([T0 + k])], x: vec![] };
    let reference = common::sorts::normal(&Sorts::new(tower(k)), &p(k));
    assert_eq!(reference.as_ref(), Some(&want(k)), "the reference at depth {k}");
    let (shallow, t1) = normal_ticks(k, &p(k));
    let (deep, t2) = normal_ticks(2 * k, &p(2 * k));
    assert_eq!(shallow, Some(shape(&want(k))), "depth {k}");
    assert_eq!(deep, Some(shape(&want(2 * k))), "depth {}", 2 * k);
    assert!(t2 <= 16 * t1, "{t1} ticks at depth {k} and {t2} at depth {}", 2 * k);
}

#[test]
fn fold_subterm_that_is_also_the_start_of_a_longer_application_is_not_folded() {
    // `k(y)` is an argument, and it is also `k(y, w)` without its last
    // argument: `y` occurs outside the argument, so the argument stays.
    folded_is(
        wf(),
        &prob(f2(k1(pv(0)), pf(K, vec![pv(0), pv(1)])), vec![(NAT, pv(0))], vec![]),
        f2(k1(pv(0)), pf(K, vec![pv(0), pv(1)])),
        &[N, &[]],
        vec![],
    );
}

#[test]
fn fold_subterm_beside_a_longer_application_of_its_symbol_is_folded() {
    folded_is(
        wf(),
        &prob(f2(k1(pv(0)), pf(K, vec![pv(1), pv(2)])), vec![(NAT, pv(0))], vec![]),
        f2(pv(0), pf(K, vec![pv(1), pv(2)])),
        &[&[BOX, ANY], &[], &[]],
        vec![],
    );
}

const G0: Name = 300;
const W: Name = 299;

/// `g0` is `z`, and `g(i)` is `f` of two `g(i-1)`, up to `g(k)`: each has
/// one member, a term with `2^k` leaves that is `k + 1` nodes of the store.
/// `w` is the pairs of the member of `g(k)` and a number.
fn doubling(k: u32) -> Vec<(Name, Def)> {
    let mut defs = vec![
        (NAT, Def { cases: vec![(Z, vec![]), (SU, vec![Some(NAT)])], rest: None }),
        (G0, one(Z, vec![])),
    ];
    for i in 1..=k {
        defs.push((G0 + i, one(F, vec![Some(G0 + i - 1), Some(G0 + i - 1)])));
    }
    defs.push((W, one(PR, vec![Some(G0 + k), Some(NAT)])));
    defs
}

/// The member of `g(k)`.
fn doubled(k: u32) -> P {
    (0..k).fold(z(), |g, _| f2(g.clone(), g))
}

#[test]
fn fold_visits_a_shared_subterm_without_a_variable_once() {
    // The pair of the member of `g(k)` and a number folds to a variable of
    // sort `w`. The member has `2^k` leaves and `k + 1` nodes: twice the
    // depth is at most a fixed power of two times the work.
    let k = 8;
    let p = |k: u32| Prob { t: pr(doubled(k), pv(0)), e: vec![], a: vec![(NAT, pv(0))], x: vec![] };
    let want = Raw { t: pv(0), c: vec![Conj::from([W])], x: vec![] };
    let run = |k: u32| {
        let mut f = fixture(doubling(k));
        let (t, e, a, x) = put_prob(&mut f, &p(k));
        let (decls, names) = (f.decls, f.names);
        let (got, ticks) = spent(&mut f.s, |s| normal(s, decls, names, t, e, a, x));
        f.empty_stack();
        let got = got.map(|r| {
            let t1 = get(&mut f.s, r.t);
            let cs = get_conjs(&mut f.s, r.c).into_iter().map(sorted).collect();
            let xs = get_lists(&mut f, r.x).iter().map(|l| format!("{l:?}")).collect();
            (t1, cs, sorted(xs))
        });
        (got, ticks)
    };
    let reference = common::sorts::normal(&Sorts::new(doubling(k)), &p(k));
    assert_eq!(reference.as_ref(), Some(&want), "the reference at depth {k}");
    let (shallow, t1): (Option<Shape>, u64) = run(k);
    let (deep, t2) = run(2 * k);
    assert_eq!(shallow, Some(shape(&want)), "depth {k}");
    assert_eq!(deep, Some(shape(&want)), "depth {}", 2 * k);
    assert!(t2 <= 16 * t1, "{t1} ticks at depth {k} and {t2} at depth {}", 2 * k);
}

/// A generator of numbers below a bound, the same on every run.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % n
    }
}

fn random_pat(rng: &mut Rng, depth: usize) -> P {
    match if depth == 0 { rng.below(4) } else { rng.below(10) } {
        0..=2 => pv(rng.below(4)),
        3 => z(),
        4 => su(random_pat(rng, depth - 1)),
        5 | 6 => k1(random_pat(rng, depth - 1)),
        7 => pr(random_pat(rng, depth - 1), random_pat(rng, depth - 1)),
        8 => g2(random_pat(rng, depth - 1), random_pat(rng, depth - 1)),
        _ => f2(random_pat(rng, depth - 1), random_pat(rng, depth - 1)),
    }
}

fn random_ground(rng: &mut Rng, depth: usize) -> P {
    match if depth == 0 { 0 } else { rng.below(4) } {
        0 => z(),
        1 => su(random_ground(rng, depth - 1)),
        2 => k1(random_ground(rng, depth - 1)),
        _ => pr(random_ground(rng, depth - 1), random_ground(rng, depth - 1)),
    }
}

#[test]
fn fold_random_problems_agree_with_the_reference() {
    let names = [NAT, SUC, BOX, PAIR, MIX, C2, C3, ANY, UNIT];
    let sorts = Sorts::new(wf());
    let mut rng = Rng(7);
    // How many problems have a store, how many of those fold a subterm, and
    // how many of those keep an exclusion.
    let (mut alive, mut folded, mut excl) = (0, 0, 0);
    for round in 0..600 {
        let t = random_pat(&mut rng, 3);
        let a = (0..rng.below(4)).map(|_| (names[rng.below(names.len())], pv(rng.below(4)))).collect();
        let x = (0..rng.below(3))
            .map(|_| {
                let r = if rng.below(3) == 0 { random_pat(&mut rng, 1) } else { random_ground(&mut rng, 2) };
                vec![(pv(rng.below(4)), r)]
            })
            .collect();
        let p = Prob { t, e: vec![], a, x };
        let want = common::sorts::normal(&sorts, &p);
        assert_eq!(run_normal(wf(), &p, false), want.as_ref().map(shape), "round {round}: {p:?}");
        if let Some(r) = want {
            alive += 1;
            if common::sorts::unfolded(&sorts, &p) != Some(r.clone()) {
                folded += 1;
                excl += usize::from(!r.x.is_empty());
            }
        }
    }
    assert!(alive > 300 && folded > 100 && excl > 10, "{alive} with a store, {folded} folded, {excl} of them with exclusions");
}
