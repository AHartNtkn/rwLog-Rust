//! The store a problem starts from (`sorts::start`) and its normal store
//! (`sorts::normal`), against `Prob.norm` of the specification
//! (`lean/RwLog/Sorts/Norm.lean`) as written on trees
//! (`common::sorts::normal`).
//!
//! A problem is a pattern, equations, sorts of patterns and exclusions.
//! `start` solves the equations, numbers the variables left in the order
//! they first occur in the pattern, the sorted patterns and the exclusions,
//! brings the sorts down to the variables, and pairs the pattern with the
//! list of all variables. `normal` tightens that store, numbers it again,
//! solves its exclusions, drops the ones another covers, and keeps what is
//! over the variables of the pattern. Every sort of a problem is declared.

mod common;

use common::sorts::*;
use common::{ap, get, get_list, v, T};
use rwlog_core::sorts::{normal, start};
use rwlog_core::store::{Node, Tbl, TermId};

// Symbols.
const Z: u32 = 0;
const SU: u32 = 1;
const PR: u32 = 2;
const F: u32 = 3;
const K: u32 = 6;
const A: u32 = 7;

// Names.
const UNIT: Name = 100;
const NAT: Name = 101;
const VOID: Name = 102;
const TWO: Name = 103;
const BOX: Name = 104;
const PAIR: Name = 105;
const MIX: Name = 106;
const C2: Name = 107;
const C3: Name = 108;
const SUC: Name = 109;
const ANY: Name = 110;

const G: u32 = 4;

fn z() -> P {
    pf(Z, vec![])
}
fn a() -> P {
    pf(A, vec![])
}
fn su(p: P) -> P {
    pf(SU, vec![p])
}
fn f2(p: P, q: P) -> P {
    pf(F, vec![p, q])
}
fn k1(p: P) -> P {
    pf(K, vec![p])
}
fn pr(p: P, q: P) -> P {
    pf(PR, vec![p, q])
}

fn one(f: u32, args: Vec<Option<Name>>) -> Def {
    Def { cases: vec![(f, args)], rest: None }
}

/// `unit` is `z`; `nat` is `z` or `s` of a `nat`; `void` is `s` of a `void`,
/// which nothing is; `two` is the pair of two `unit`; `box` is `k` of a
/// `nat`; `pair` is the pair of two `nat`; `mix` is `g` of a `unit` and a
/// `nat`; `c2` is `k` of a `box` and `c3` is `k` of a `c2`; `suc` is `s` of a
/// `nat`; `any` is `z` or anything else but `a`.
fn wf() -> Vec<(Name, Def)> {
    vec![
        (UNIT, one(Z, vec![])),
        (NAT, Def { cases: vec![(Z, vec![]), (SU, vec![Some(NAT)])], rest: None }),
        (VOID, one(SU, vec![Some(VOID)])),
        (TWO, one(PR, vec![Some(UNIT), Some(UNIT)])),
        (BOX, one(K, vec![Some(NAT)])),
        (PAIR, one(PR, vec![Some(NAT), Some(NAT)])),
        (MIX, one(G, vec![Some(UNIT), Some(NAT)])),
        (C2, one(K, vec![Some(BOX)])),
        (C3, one(K, vec![Some(C2)])),
        (SUC, one(SU, vec![Some(NAT)])),
        (ANY, Def { cases: vec![(Z, vec![])], rest: Some((vec![(A, 0)], None)) }),
    ]
}

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

/// What `start` returns, read back: the pattern, the list of variables it
/// is paired with, the exclusions, the entries and the next variable.
type Started = (T, Vec<T>, Vec<Vec<T>>, Entries, T);

fn run_start(p: &Prob, soiled: bool) -> Option<Started> {
    let mut f = fixture(wf());
    let (t, e, a, x) = put_prob(&mut f, p);
    if soiled {
        dirty(&mut f);
    }
    let got = start(&mut f.s, f.decls, f.names, t, e, a, x);
    f.empty_stack();
    got.map(|(t0, x0, es0, next0)| {
        let (h, vars) = match f.s.read(t0) {
            Node::App(h, vars) => (h, vars),
            _ => panic!("the pattern is not a pair"),
        };
        let t1 = match f.s.read(h) {
            Node::App(nil, t1) => {
                assert!(matches!(f.s.read(nil), Node::Nil), "the pair has another head");
                t1
            }
            _ => panic!("the pattern is not a pair"),
        };
        let t1 = get(&mut f.s, t1);
        let vars = get_list(&mut f.s, vars);
        let x0 = get_lists(&mut f, x0);
        let es = f.read_entries(es0);
        let next = get(&mut f.s, next0);
        (t1, vars, x0, es, next)
    })
}

fn start_is(p: &Prob, t: &P, n: usize, x: &[Vec<(P, P)>], ents: &[Vec<Name>]) {
    let order = fixture(wf()).order;
    let (gt, gvars, gx, ges, gnext) = run_start(p, false).expect("a store");
    assert_eq!(gt, t.tree(), "the pattern of {p:?}");
    let places: Vec<T> = (0..n).map(|i| v(i as u128)).collect();
    assert_eq!(gvars, places, "the variables of {p:?}");
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
    got.map(|(t1, cs, xs)| {
        let t1 = get(&mut f.s, t1);
        let cs = get_conjs(&mut f.s, cs).into_iter().map(sorted).collect();
        let xs = get_lists(&mut f, xs).iter().map(|l| format!("{l:?}")).collect();
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
fn normal_single_root_sort_opens_variable() {
    normal_pattern(&Prob { t: pv(0), e: vec![], a: vec![(SUC, pv(0))], x: vec![] }, &su(pv(0)));
}

#[test]
fn normal_box_sort_opens_variable() {
    normal_pattern(&Prob { t: pv(0), e: vec![], a: vec![(BOX, pv(0))], x: vec![] }, &k1(pv(0)));
}

#[test]
fn normal_nested_single_root_sorts_open_repeatedly() {
    normal_pattern(&Prob { t: pv(0), e: vec![], a: vec![(C3, pv(0))], x: vec![] }, &k1(k1(k1(pv(0)))));
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
fn normal_intersection_with_single_root_opens_variable() {
    normal_pattern(&Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0)), (SUC, pv(0))], x: vec![] }, &su(pv(0)));
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
    normal_pattern(&Prob { t: f2(pv(0), pv(1)), e: vec![(pv(0), pv(1))], a: vec![(NAT, pv(0)), (SUC, pv(1))], x: vec![] }, &f2(su(pv(0)), su(pv(0))));
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
fn normal_exclusion_of_zero_from_nat_opens_to_successor() {
    normal_pattern(&Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0))], x: vec![vec![(pv(0), z())]] }, &su(pv(0)));
}

#[test]
fn normal_two_exclusions_open_nat_twice() {
    normal_pattern(&Prob { t: pv(0), e: vec![], a: vec![(NAT, pv(0))], x: vec![vec![(pv(0), z())], vec![(pv(0), su(z()))]] }, &su(su(pv(0))));
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
fn normal_hidden_single_value_exclusion_opens_sorted_pattern_variable() {
    normal_pattern(&Prob { t: pv(0), e: vec![], a: vec![(UNIT, pv(1)), (NAT, pv(0))], x: vec![vec![(pv(0), pv(1))]] }, &su(pv(0)));
}

#[test]
fn normal_disequality_of_two_single_member_variables_is_none() {
    normal_none(wf(), &Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![(UNIT, pv(0)), (UNIT, pv(1))], x: vec![vec![(pv(0), pv(1))]] });
}

#[test]
fn normal_disequality_of_variables_of_disjoint_sorts_is_dropped() {
    normal_pattern(&Prob { t: f2(pv(0), pv(1)), e: vec![], a: vec![(UNIT, pv(0)), (SUC, pv(1))], x: vec![vec![(pv(0), pv(1))]] }, &f2(z(), su(pv(0))));
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
