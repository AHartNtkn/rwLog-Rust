//! Bringing a store to a tight one (`sorts::tighten`), with the checks it
//! makes on the way: a list reversed onto another (`sorts::rev_onto`),
//! whether an exclusion always holds (`sorts::always_on`,
//! `sorts::any_always`), and whether an entry has no member (the flag of
//! `sorts::settle`), against `always`, `stepAt` and `Tightens` of the
//! specification (`lean/RwLog/Sorts/Tighten.lean`, `Loop.lean`) as written on
//! trees here.
//!
//! A store is a pattern, a list of exclusions, a list of entries (a variable
//! with the conjunction of its sorts) and the next unused variable.
//! `tighten` first replaces each variable whose sorts have one member. Then,
//! as long as no exclusion always holds, it takes the first entry whose
//! values have one root, replaces its variable by that root applied to new
//! variables, and puts the entries of the new variables that are left, in
//! reverse, before the others.

mod common;

use common::sorts::*;
use common::{get, get_list, put_list, put_var, T};
use rwlog_core::sorts::{always_on, any_always, rev_onto, settle, tighten};
use rwlog_core::store::{Frame, Node, Store, Tbl, TermId};
use std::collections::BTreeMap;

// Symbols.
const Z: u32 = 0;
const SU: u32 = 1;
const PR: u32 = 2;
const F: u32 = 3;
const G: u32 = 4;
const H: u32 = 5;
const K: u32 = 6;
const A: u32 = 7;
const B: u32 = 8;

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
// Sorts with two members, which well-formed sorts do not have.
const OPT: Name = 120;
const ENUM: Name = 121;

fn z() -> P {
    pf(Z, vec![])
}
fn a() -> P {
    pf(A, vec![])
}
fn b() -> P {
    pf(B, vec![])
}
fn su(p: P) -> P {
    pf(SU, vec![p])
}
fn f1(p: P) -> P {
    pf(F, vec![p])
}
fn f2(p: P, q: P) -> P {
    pf(F, vec![p, q])
}
fn g1(p: P) -> P {
    pf(G, vec![p])
}
fn g2(p: P, q: P) -> P {
    pf(G, vec![p, q])
}
fn h2(p: P, q: P) -> P {
    pf(H, vec![p, q])
}
fn k1(p: P) -> P {
    pf(K, vec![p])
}
fn pr(p: P, q: P) -> P {
    pf(PR, vec![p, q])
}
fn num(n: usize, end: P) -> P {
    (0..n).fold(end, |p, _| su(p))
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

/// The sorts of `wf` with `opt`, which is `z` or `s` of a `unit`, and
/// `enum`, which is `z` or `a`.
fn two_members() -> Vec<(Name, Def)> {
    let mut d = wf();
    d.push((OPT, Def { cases: vec![(Z, vec![]), (SU, vec![Some(UNIT)])], rest: None }));
    d.push((ENUM, Def { cases: vec![(Z, vec![]), (A, vec![])], rest: None }));
    d
}

type Eqs = Vec<(P, P)>;
type Sets = Vec<(usize, Conj)>;
type St = (P, Excls, Entries, usize);

fn conj(c: &[Name]) -> Conj {
    c.iter().copied().collect()
}

fn sets(es: &Entries) -> Sets {
    es.iter().map(|(v, c)| (*v, conj(c))).collect()
}

fn subst_all(t: &mut P, x: &mut Excls, v: usize, by: P) {
    let one = BTreeMap::from([(v, by)]);
    *t = t.subst(&one);
    for e in x.iter_mut() {
        for (l, r) in e.iter_mut() {
            *l = l.subst(&one);
            *r = r.subst(&one);
        }
    }
}

/// `always` of the specification: the most general solution of the
/// equations moves no variable.
fn always_ref(e: &[(P, P)]) -> bool {
    mgu(e).is_some_and(|m| m.is_empty())
}

/// `CStore.settle` on trees, with whether every entry has a member.
fn settle_ref(ss: &Sorts, t: &mut P, x: &mut Excls, es: &Sets) -> (bool, Sets) {
    let mut ok = true;
    let mut kept = Vec::new();
    for (v, c) in es {
        match ss.size(c) {
            Size::One(g) => subst_all(t, x, *v, g),
            Size::Empty => {
                ok = false;
                kept.push((*v, c.clone()));
            }
            Size::Infinite => kept.push((*v, c.clone())),
        }
    }
    (ok, kept)
}

/// Steps of `Tightens` of the specification on trees, taken in the order
/// `sorts::tighten` takes them. The sorts must be well formed.
fn tighten_ref(ss: &Sorts, t: &P, x: &Excls, es: &Entries, next: usize) -> Option<(P, Excls, Sets, usize)> {
    let mut t = t.clone();
    let mut x = x.clone();
    let mut next = next;
    let (ok, mut es) = settle_ref(ss, &mut t, &mut x, &sets(es));
    if !ok {
        return None;
    }
    loop {
        if x.iter().any(|e| always_ref(e)) {
            return None;
        }
        let Some(i) = es.iter().position(|(v, c)| ss.sole(c, &gone(&x, *v)).is_some()) else {
            return Some((t, x, es, next));
        };
        let (v, c) = es.remove(i);
        let ((f, n), kids) = ss.sole(&c, &gone(&x, v)).expect("found above");
        let args: Vec<P> = (0..n).map(|j| pv(next + j)).collect();
        subst_all(&mut t, &mut x, v, pf(f, args));
        let new: Sets = kids.iter().enumerate().map(|(j, k)| (next + j, k.clone())).collect();
        next += n;
        let (ok, kept) = settle_ref(ss, &mut t, &mut x, &new);
        if !ok {
            return None;
        }
        es = kept.into_iter().rev().chain(es).collect();
    }
}

/// `tighten` in the store, with the nodes it returned.
fn run(fxt: &mut Fx, t: &P, x: &Excls, es: &Entries, next: usize) -> Option<(TermId, TermId, TermId, TermId)> {
    let ti = put_pat(&mut fxt.s, t);
    let xi = put_excls(&mut fxt.s, x);
    let ei = fxt.entries(es);
    let ni = put_var(&mut fxt.s, next as u128);
    let got = tighten(&mut fxt.s, fxt.decls, fxt.names, ti, xi, ei, ni);
    fxt.empty_stack();
    got
}

/// What `tighten` returned is the store `want`, node for node.
fn check(fxt: &mut Fx, got: Option<(TermId, TermId, TermId, TermId)>, want: &Option<St>) {
    match (got, want) {
        (None, None) => {}
        (Some((t1, x1, e1, n1)), Some((wt, wx, wes, wn))) => {
            let wti = put_pat(&mut fxt.s, wt);
            let wxi = put_excls(&mut fxt.s, wx);
            let wni = put_var(&mut fxt.s, *wn as u128);
            assert!(fxt.s.same(t1, wti), "the pattern is {:?}", get(&mut fxt.s, t1));
            assert!(fxt.s.same(x1, wxi), "the exclusions are {:?}", get(&mut fxt.s, x1));
            assert_eq!(sets(&fxt.read_entries(e1)), sets(wes), "the entries");
            assert!(fxt.s.same(n1, wni), "the next variable is {:?}", get(&mut fxt.s, n1));
        }
        (Some((t1, _, _, _)), None) => panic!("a store with the pattern {:?}", get(&mut fxt.s, t1)),
        (None, Some(_)) => panic!("no store"),
    }
}

/// With well-formed sorts, the store written by hand is that of the
/// reference and that of `tighten`.
fn tight_is(t: P, x: Excls, es: Entries, next: usize, want: Option<St>) {
    let mut fxt = fixture(wf());
    let r = tighten_ref(&fxt.ss, &t, &x, &es, next);
    let w = want.clone().map(|(wt, wx, wes, wn)| (wt, wx, sets(&wes), wn));
    assert_eq!(r, w, "the reference");
    let got = run(&mut fxt, &t, &x, &es, next);
    check(&mut fxt, got, &want);
}

/// With sorts that have two members, the store written by hand is that of
/// `tighten`.
fn tight2_is(t: P, x: Excls, es: Entries, next: usize, want: Option<St>) {
    let mut fxt = fixture(two_members());
    let got = run(&mut fxt, &t, &x, &es, next);
    check(&mut fxt, got, &want);
}

fn unchanged(t: P, x: Excls, es: Entries, next: usize) {
    tight_is(t.clone(), x.clone(), es.clone(), next, Some((t, x, es, next)));
}

// A list reversed onto another.

fn syms(s: &mut Store, fs: &[u32]) -> TermId {
    let ts: Vec<T> = fs.iter().map(|f| T::S(*f)).collect();
    put_list(s, &ts)
}

fn onto(l: &[u32], out: &[u32]) -> Vec<T> {
    let mut s = Store::new();
    let li = syms(&mut s, l);
    let oi = syms(&mut s, out);
    let r = rev_onto(&mut s, li, oi);
    assert!(s.pop().is_none(), "the stack is not empty");
    get_list(&mut s, r)
}

fn ss(fs: &[u32]) -> Vec<T> {
    fs.iter().map(|f| T::S(*f)).collect()
}

#[test]
fn nothing_onto_nothing_is_the_empty_list() {
    assert_eq!(onto(&[], &[]), ss(&[]));
}

#[test]
fn nothing_onto_a_list_is_the_node_of_that_list() {
    let mut s = Store::new();
    let nil = s.alloc(Node::Nil);
    let out = syms(&mut s, &[A, B]);
    let r = rev_onto(&mut s, nil, out);
    assert!(s.same(r, out));
}

#[test]
fn a_list_onto_nothing_is_the_list_in_the_other_order() {
    assert_eq!(onto(&[A, B, F], &[]), ss(&[F, B, A]));
}

#[test]
fn one_member_goes_in_front() {
    assert_eq!(onto(&[A], &[B]), ss(&[A, B]));
}

#[test]
fn the_reversed_list_comes_before_the_other_in_its_order() {
    assert_eq!(onto(&[A, B, F], &[G, H]), ss(&[F, B, A, G, H]));
}

#[test]
fn the_other_list_is_the_tail_node() {
    let mut s = Store::new();
    let l = syms(&mut s, &[A, B]);
    let out = syms(&mut s, &[G, H]);
    let r = rev_onto(&mut s, l, out);
    let want = syms(&mut s, &[B, A, G, H]);
    assert!(s.same(r, want));
}

#[test]
fn members_that_are_lists_are_not_reversed_inside() {
    let mut s = Store::new();
    let l = put_list(&mut s, &[T::A(Box::new(T::S(A)), Box::new(T::S(B))), T::S(F)]);
    let nil = s.alloc(Node::Nil);
    let r = rev_onto(&mut s, l, nil);
    assert_eq!(get_list(&mut s, r), vec![T::S(F), T::A(Box::new(T::S(A)), Box::new(T::S(B)))]);
}

#[test]
fn repeated_members_stay_repeated() {
    assert_eq!(onto(&[A, A, B], &[]), ss(&[B, A, A]));
}

#[test]
fn a_list_onto_itself() {
    let mut s = Store::new();
    let l = syms(&mut s, &[A, B]);
    let r = rev_onto(&mut s, l, l);
    assert_eq!(get_list(&mut s, r), ss(&[B, A, A, B]));
}

#[test]
fn reversing_twice_gives_the_node_of_the_list() {
    let mut s = Store::new();
    let l = syms(&mut s, &[A, B, F]);
    let nil = s.alloc(Node::Nil);
    let r = rev_onto(&mut s, l, nil);
    let rr = rev_onto(&mut s, r, nil);
    assert!(s.same(rr, l));
}

#[test]
fn a_long_list_is_reversed_without_the_call_stack() {
    let mut s = Store::new();
    let nil = s.alloc(Node::Nil);
    let fa = s.alloc(Node::Sym(A));
    let fb = s.alloc(Node::Sym(B));
    let mut l = s.alloc(Node::App(fb, nil));
    for _ in 0..100_000 {
        l = s.alloc(Node::App(fa, l));
    }
    let r = rev_onto(&mut s, l, nil);
    assert!(s.pop().is_none(), "the stack is not empty");
    match s.read(r) {
        Node::App(h, _) => assert!(s.same(h, fb)),
        _ => panic!("not a list"),
    }
}

// Whether an exclusion always holds.

fn x() -> P {
    pv(5)
}
fn y() -> P {
    pv(6)
}

fn always_in(prep: impl FnOnce(&mut Store), e: &[(P, P)]) -> bool {
    let mut s = Store::new();
    prep(&mut s);
    let ei = put_eqns(&mut s, e);
    let got = always_on(&mut s, ei);
    assert!(s.pop().is_none(), "the stack is not empty");
    got
}

fn always_is(e: &[(P, P)], want: bool) {
    assert_eq!(always_ref(e), want, "the reference on {:?}", e);
    assert_eq!(always_in(|_| (), e), want, "the store on {:?}", e);
}

#[test]
fn no_equation_always_holds() {
    always_is(&[], true);
}

#[test]
fn equal_ground_sides_always_hold() {
    always_is(&[(a(), a())], true);
    always_is(&[(f2(a(), b()), f2(a(), b()))], true);
}

#[test]
fn different_ground_sides_never_hold() {
    always_is(&[(a(), b())], false);
    always_is(&[(f1(a()), g1(a()))], false);
}

#[test]
fn ground_sides_with_different_numbers_of_arguments_never_hold() {
    always_is(&[(f1(a()), f2(a(), b()))], false);
}

#[test]
fn a_variable_equated_to_itself_always_holds() {
    always_is(&[(x(), x())], true);
}

#[test]
fn the_same_term_with_variables_on_both_sides_always_holds() {
    always_is(&[(f1(x()), f1(x()))], true);
    always_is(&[(g2(x(), y()), g2(x(), y()))], true);
}

#[test]
fn two_variables_equated_do_not_always_hold() {
    always_is(&[(x(), y())], false);
    always_is(&[(y(), x())], false);
}

#[test]
fn a_variable_equated_to_a_constant_does_not_always_hold() {
    always_is(&[(x(), a())], false);
    always_is(&[(a(), x())], false);
}

#[test]
fn a_variable_bound_below_a_symbol_does_not_always_hold() {
    always_is(&[(f1(x()), f1(a()))], false);
    always_is(&[(f1(x()), f1(y()))], false);
}

#[test]
fn a_variable_inside_its_own_value_never_holds() {
    always_is(&[(x(), f1(x()))], false);
}

#[test]
fn a_cycle_through_two_variables_never_holds() {
    always_is(&[(x(), f1(y())), (y(), f1(x()))], false);
}

#[test]
fn an_equation_that_always_holds_twice_always_holds() {
    always_is(&[(x(), x()), (x(), x())], true);
    always_is(&[(a(), a()), (a(), a())], true);
}

#[test]
fn an_equation_that_binds_twice_does_not_always_hold() {
    always_is(&[(x(), a()), (x(), a())], false);
}

#[test]
fn one_binding_equation_among_others_does_not_always_hold() {
    always_is(&[(x(), a()), (a(), a()), (y(), y())], false);
    always_is(&[(a(), a()), (x(), a()), (y(), y())], false);
    always_is(&[(a(), a()), (y(), y()), (x(), a())], false);
}

#[test]
fn one_failing_equation_among_others_does_not_always_hold() {
    always_is(&[(x(), x()), (a(), b())], false);
}

#[test]
fn two_variables_equated_both_ways_do_not_always_hold() {
    always_is(&[(x(), y()), (y(), x())], false);
}

#[test]
fn two_values_for_a_variable_never_hold() {
    always_is(&[(x(), a()), (x(), b())], false);
}

#[test]
fn the_variable_zero_is_a_variable_like_another() {
    always_is(&[(pv(0), pv(0))], true);
    always_is(&[(pv(0), a())], false);
}

#[test]
fn a_shared_subterm_on_both_sides() {
    let s = f1(x());
    always_is(&[(h2(s.clone(), s.clone()), h2(s.clone(), s.clone()))], true);
    always_is(&[(h2(s, x()), h2(f1(a()), x()))], false);
}

#[test]
fn what_the_tables_held_before_does_not_change_always() {
    let dirty = |s: &mut Store| {
        let xi = put_var(s, 5);
        let ai = put_pat(s, &a());
        s.set(Tbl::A, xi, ai);
        s.set_flag(Tbl::B, xi, true);
        s.set_flag(Tbl::A, ai, true);
    };
    assert!(always_in(dirty, &[(x(), x())]));
    assert!(!always_in(dirty, &[(x(), a())]));
}

#[test]
fn every_pair_of_small_equations_agrees_with_the_reference() {
    let terms = [x(), y(), a(), b(), f1(x()), f1(y()), f1(a()), f2(x(), a()), f2(a(), y())];
    for p in &terms {
        for q in &terms {
            for r in &terms {
                for t in [a(), x(), f1(y()), f1(x())] {
                    let e = vec![(p.clone(), q.clone()), (r.clone(), t)];
                    assert_eq!(always_in(|_| (), &e), always_ref(&e), "{:?}", e);
                }
            }
        }
    }
}

// Whether some exclusion of a list always holds.

fn any_is(xs: &[Eqs], want: bool) {
    assert_eq!(xs.iter().any(|e| always_ref(e)), want, "the reference on {:?}", xs);
    let mut s = Store::new();
    let xi = put_excls(&mut s, xs);
    assert_eq!(any_always(&mut s, xi), want, "the store on {:?}", xs);
    assert!(s.pop().is_none(), "the stack is not empty");
}

#[test]
fn of_no_exclusion_none_always_holds() {
    any_is(&[], false);
}

#[test]
fn the_exclusion_with_no_equation_always_holds() {
    any_is(&[vec![]], true);
}

#[test]
fn one_exclusion_that_always_holds() {
    any_is(&[vec![(x(), x())]], true);
}

#[test]
fn one_exclusion_that_does_not_always_hold() {
    any_is(&[vec![(x(), a())]], false);
}

#[test]
fn one_that_always_holds_is_found_wherever_it_is() {
    any_is(&[vec![(a(), a())], vec![(x(), a())]], true);
    any_is(&[vec![(x(), a())], vec![(a(), a())]], true);
    any_is(&[vec![(x(), a())], vec![(y(), y())], vec![(a(), b())]], true);
}

#[test]
fn none_of_several_always_holds() {
    any_is(&[vec![(x(), a())], vec![(a(), b())], vec![(x(), y())]], false);
}

#[test]
fn exclusions_that_never_hold_do_not_hide_a_later_one() {
    any_is(&[vec![(a(), b())], vec![(x(), f1(x()))], vec![(x(), x())]], true);
}

#[test]
fn what_one_exclusion_binds_is_not_bound_in_the_next() {
    any_is(&[vec![(x(), a())], vec![(x(), x())]], true);
    any_is(&[vec![(x(), a())], vec![(f1(x()), f1(a()))]], false);
}

#[test]
fn the_same_exclusion_listed_twice() {
    any_is(&[vec![(x(), a())], vec![(x(), a())]], false);
    any_is(&[vec![(x(), x())], vec![(x(), x())]], true);
}

// Whether every entry has a member.

fn settle_flag(es: Entries) -> bool {
    let mut fxt = fixture(wf());
    let t = g2(pv(0), g2(pv(1), pv(2)));
    let x: Excls = vec![];
    let ti = put_pat(&mut fxt.s, &t);
    let xi = put_excls(&mut fxt.s, &x);
    let ei = fxt.entries(&es);
    let (ok, t1, x1, e1) = settle(&mut fxt.s, fxt.decls, fxt.names, ti, xi, ei);
    fxt.empty_stack();
    let (mut rt, mut rx) = (t, x);
    let (rok, rkept) = settle_ref(&fxt.ss, &mut rt, &mut rx, &sets(&es));
    let wt = put_pat(&mut fxt.s, &rt);
    let wx = put_excls(&mut fxt.s, &rx);
    assert!(fxt.s.same(t1, wt), "the pattern is {:?}", get(&mut fxt.s, t1));
    assert!(fxt.s.same(x1, wx), "the exclusions are {:?}", get(&mut fxt.s, x1));
    assert_eq!(sets(&fxt.read_entries(e1)), rkept, "the entries");
    assert_eq!(ok, rok, "the reference");
    ok
}

#[test]
fn no_entry_has_no_empty_one() {
    assert!(settle_flag(vec![]));
}

#[test]
fn an_entry_with_one_member_has_a_member() {
    assert!(settle_flag(vec![(0, vec![UNIT])]));
}

#[test]
fn an_entry_with_many_members_has_a_member() {
    assert!(settle_flag(vec![(0, vec![NAT])]));
}

#[test]
fn an_entry_of_a_sort_with_no_member_is_reported() {
    assert!(!settle_flag(vec![(0, vec![VOID])]));
}

#[test]
fn an_entry_of_two_sorts_with_no_member_in_common_is_reported() {
    assert!(!settle_flag(vec![(0, vec![UNIT, TWO])]));
}

#[test]
fn an_entry_of_two_sorts_with_one_member_in_common_has_a_member() {
    assert!(settle_flag(vec![(0, vec![UNIT, NAT])]));
}

#[test]
fn one_entry_with_no_member_among_others_is_reported_wherever_it_is() {
    assert!(!settle_flag(vec![(0, vec![VOID]), (1, vec![UNIT]), (2, vec![NAT])]));
    assert!(!settle_flag(vec![(0, vec![UNIT]), (1, vec![VOID]), (2, vec![NAT])]));
    assert!(!settle_flag(vec![(0, vec![UNIT]), (1, vec![NAT]), (2, vec![VOID])]));
}

#[test]
fn an_entry_with_no_member_of_a_variable_that_occurs_nowhere_is_reported() {
    assert!(!settle_flag(vec![(7, vec![VOID])]));
}

#[test]
fn an_entry_of_no_sort_has_a_member() {
    assert!(settle_flag(vec![(0, vec![])]));
}

// Stores that need no replacement.

#[test]
fn the_store_with_nothing_in_it_is_returned() {
    unchanged(z(), vec![], vec![], 0);
}

#[test]
fn a_store_that_needs_no_replacement_is_returned_as_it_is() {
    unchanged(
        pr(pv(0), pv(1)),
        vec![vec![(pv(0), su(pv(1)))]],
        vec![(0, vec![NAT]), (1, vec![NAT])],
        2,
    );
}

#[test]
fn a_store_that_needs_no_replacement_is_returned_as_the_same_nodes() {
    let mut fxt = fixture(wf());
    let ti = put_pat(&mut fxt.s, &pr(pv(0), pv(1)));
    let xi = put_excls(&mut fxt.s, &[vec![(pv(0), su(pv(1)))]]);
    let ei = fxt.entries(&[(0, vec![NAT]), (1, vec![NAT])]);
    let ni = put_var(&mut fxt.s, 2);
    let (t1, x1, e1, n1) =
        tighten(&mut fxt.s, fxt.decls, fxt.names, ti, xi, ei, ni).expect("a store");
    assert!(fxt.s.same(t1, ti) && fxt.s.same(x1, xi) && fxt.s.same(e1, ei) && fxt.s.same(n1, ni));
}

#[test]
fn variables_without_entries_are_never_replaced() {
    unchanged(pr(pv(0), pv(1)), vec![vec![(pv(0), z())]], vec![], 2);
}

#[test]
fn an_exclusion_that_never_holds_is_kept() {
    unchanged(pv(0), vec![vec![(z(), su(z()))]], vec![(0, vec![NAT])], 1);
}

#[test]
fn exclusions_that_are_not_of_one_variable_leave_two_roots() {
    unchanged(
        pr(pv(0), pv(1)),
        vec![vec![(pr(pv(0), pv(1)), pr(z(), z()))]],
        vec![(0, vec![NAT]), (1, vec![NAT])],
        2,
    );
}

#[test]
fn a_variable_of_a_sort_with_a_rest_is_never_replaced() {
    unchanged(pv(0), vec![vec![(pv(0), z())]], vec![(0, vec![ANY])], 1);
}

#[test]
fn an_entry_of_no_sort_is_kept_and_its_variable_not_replaced() {
    unchanged(pv(0), vec![vec![(pv(0), z())]], vec![(0, vec![])], 1);
}

// One replacement.

#[test]
fn a_variable_of_a_sort_with_one_case_becomes_that_case() {
    tight_is(pv(0), vec![], vec![(0, vec![BOX])], 1, Some((k1(pv(1)), vec![], vec![(1, vec![NAT])], 2)));
}

#[test]
fn a_number_that_is_not_zero_becomes_a_successor() {
    tight_is(
        pv(0),
        vec![vec![(pv(0), z())]],
        vec![(0, vec![NAT])],
        1,
        Some((su(pv(1)), vec![vec![(su(pv(1)), z())]], vec![(1, vec![NAT])], 2)),
    );
}

#[test]
fn a_root_with_several_arguments_gets_a_variable_for_each() {
    tight_is(
        pv(0),
        vec![],
        vec![(0, vec![PAIR])],
        1,
        Some((pr(pv(1), pv(2)), vec![], vec![(2, vec![NAT]), (1, vec![NAT])], 3)),
    );
}

#[test]
fn a_new_variable_with_one_value_becomes_it_and_keeps_its_number() {
    tight_is(
        pv(0),
        vec![],
        vec![(0, vec![MIX])],
        1,
        Some((g2(z(), pv(2)), vec![], vec![(2, vec![NAT])], 3)),
    );
}

#[test]
fn two_sorts_whose_common_members_have_one_root() {
    tight_is(
        pv(0),
        vec![],
        vec![(0, vec![NAT, SUC])],
        1,
        Some((su(pv(1)), vec![], vec![(1, vec![NAT])], 2)),
    );
}

#[test]
fn a_root_with_no_argument_is_a_constant() {
    tight2_is(
        pv(0),
        vec![vec![(pv(0), z())]],
        vec![(0, vec![ENUM])],
        1,
        Some((a(), vec![vec![(a(), z())]], vec![], 1)),
    );
}

#[test]
fn all_new_variables_becoming_their_one_value_leaves_a_ground_term() {
    tight2_is(
        pv(0),
        vec![vec![(pv(0), z())]],
        vec![(0, vec![OPT])],
        1,
        Some((su(z()), vec![vec![(su(z()), z())]], vec![], 2)),
    );
}

#[test]
fn no_root_left_returns_the_store() {
    let x = vec![vec![(pv(0), z())], vec![(pv(0), a())]];
    tight2_is(pv(0), x.clone(), vec![(0, vec![ENUM])], 1, Some((pv(0), x, vec![(0, vec![ENUM])], 1)));
}

// More than one replacement.

#[test]
fn a_chain_of_sorts_with_one_case() {
    tight_is(
        pv(0),
        vec![],
        vec![(0, vec![C3])],
        1,
        Some((k1(k1(k1(pv(3)))), vec![], vec![(3, vec![NAT])], 4)),
    );
}

#[test]
fn a_new_variable_gets_one_root_from_the_next_excluded_number() {
    let t = su(su(pv(2)));
    tight_is(
        pv(0),
        vec![vec![(pv(0), z())], vec![(pv(0), su(z()))]],
        vec![(0, vec![NAT])],
        1,
        Some((t.clone(), vec![vec![(t.clone(), z())], vec![(t, su(z()))]], vec![(2, vec![NAT])], 3)),
    );
}

#[test]
fn as_many_replacements_as_excluded_numbers() {
    let x: Excls = (0..5).map(|n| vec![(pv(0), num(n, z()))]).collect();
    let t = num(5, pv(5));
    let wx: Excls = (0..5).map(|n| vec![(t.clone(), num(n, z()))]).collect();
    tight_is(pv(0), x, vec![(0, vec![NAT])], 1, Some((t, wx, vec![(5, vec![NAT])], 6)));
}

#[test]
fn the_excluded_numbers_may_come_in_any_order() {
    let t = su(su(pv(2)));
    tight_is(
        pv(0),
        vec![vec![(pv(0), su(z()))], vec![(pv(0), z())]],
        vec![(0, vec![NAT])],
        1,
        Some((t.clone(), vec![vec![(t.clone(), su(z()))], vec![(t, z())]], vec![(2, vec![NAT])], 3)),
    );
}

#[test]
fn a_number_not_excluded_stops_the_replacements() {
    let t = su(pv(1));
    tight_is(
        pv(0),
        vec![vec![(pv(0), z())], vec![(pv(0), su(su(z())))]],
        vec![(0, vec![NAT])],
        1,
        Some((t.clone(), vec![vec![(t.clone(), z())], vec![(t, su(su(z())))]], vec![(1, vec![NAT])], 2)),
    );
}

#[test]
fn the_same_term_excluded_twice() {
    let t = su(pv(1));
    tight_is(
        pv(0),
        vec![vec![(pv(0), z())], vec![(pv(0), z())]],
        vec![(0, vec![NAT])],
        1,
        Some((t.clone(), vec![vec![(t.clone(), z())], vec![(t, z())]], vec![(1, vec![NAT])], 2)),
    );
}

#[test]
fn the_first_entry_with_one_root_is_replaced_first() {
    tight_is(
        pr(pv(0), pv(1)),
        vec![],
        vec![(0, vec![BOX]), (1, vec![BOX])],
        2,
        Some((pr(k1(pv(2)), k1(pv(3))), vec![], vec![(3, vec![NAT]), (2, vec![NAT])], 4)),
    );
}

#[test]
fn an_entry_without_one_root_is_passed_over() {
    tight_is(
        pr(pv(0), pv(1)),
        vec![],
        vec![(0, vec![NAT]), (1, vec![BOX])],
        2,
        Some((pr(pv(0), k1(pv(2))), vec![], vec![(2, vec![NAT]), (0, vec![NAT])], 3)),
    );
}

#[test]
fn new_entries_come_reversed_before_the_others_in_their_order() {
    tight_is(
        g2(pv(0), g2(pv(1), pv(2))),
        vec![],
        vec![(0, vec![NAT]), (1, vec![PAIR]), (2, vec![NAT])],
        3,
        Some((
            g2(pv(0), g2(pr(pv(3), pv(4)), pv(2))),
            vec![],
            vec![(4, vec![NAT]), (3, vec![NAT]), (0, vec![NAT]), (2, vec![NAT])],
            5,
        )),
    );
}

#[test]
fn an_exclusion_over_variables_without_entries_still_excludes() {
    tight_is(
        pr(pv(0), pv(1)),
        vec![vec![(pv(1), pv(1)), (pv(0), z())]],
        vec![(0, vec![NAT])],
        2,
        Some((
            pr(su(pv(2)), pv(1)),
            vec![vec![(pv(1), pv(1)), (su(pv(2)), z())]],
            vec![(2, vec![NAT])],
            3,
        )),
    );
}

// The variables.

#[test]
fn new_variables_are_numbered_from_the_next_one_given() {
    tight_is(pv(0), vec![], vec![(0, vec![BOX])], 9, Some((k1(pv(9)), vec![], vec![(9, vec![NAT])], 10)));
}

#[test]
fn the_numbers_go_on_from_one_replacement_to_the_next() {
    tight_is(
        pv(0),
        vec![],
        vec![(0, vec![C3])],
        7,
        Some((k1(k1(k1(pv(9)))), vec![], vec![(9, vec![NAT])], 10)),
    );
}

#[test]
fn a_variable_that_is_not_the_first_is_replaced_like_another() {
    tight_is(
        pv(5),
        vec![vec![(pv(5), z())]],
        vec![(5, vec![NAT])],
        6,
        Some((su(pv(6)), vec![vec![(su(pv(6)), z())]], vec![(6, vec![NAT])], 7)),
    );
}

#[test]
fn every_place_of_the_variable_is_replaced() {
    let s2 = su(pv(2));
    tight_is(
        g2(pv(0), g2(pv(0), pv(1))),
        vec![vec![(pv(0), z())], vec![(pr(pv(0), pv(1)), pr(su(pv(0)), pv(1)))]],
        vec![(0, vec![NAT])],
        2,
        Some((
            g2(s2.clone(), g2(s2.clone(), pv(1))),
            vec![vec![(s2.clone(), z())], vec![(pr(s2.clone(), pv(1)), pr(su(s2), pv(1)))]],
            vec![(2, vec![NAT])],
            3,
        )),
    );
}

#[test]
fn a_shared_subterm_with_two_variables_that_are_replaced() {
    let q = g2(pv(0), pv(1));
    let q1 = g2(k1(pv(2)), k1(pv(3)));
    tight_is(
        pr(q.clone(), q),
        vec![],
        vec![(0, vec![BOX]), (1, vec![BOX])],
        2,
        Some((pr(q1.clone(), q1), vec![], vec![(3, vec![NAT]), (2, vec![NAT])], 4)),
    );
}

// The first replacement of the variables with one value.

#[test]
fn variables_with_one_value_are_replaced_first() {
    tight_is(
        pr(pv(0), pv(1)),
        vec![],
        vec![(0, vec![UNIT]), (1, vec![NAT])],
        2,
        Some((pr(z(), pv(1)), vec![], vec![(1, vec![NAT])], 2)),
    );
}

#[test]
fn a_variable_with_one_value_gives_an_earlier_entry_one_root() {
    tight_is(
        pr(pv(0), pv(1)),
        vec![vec![(pr(pv(0), pv(1)), pr(z(), z()))]],
        vec![(0, vec![NAT]), (1, vec![UNIT])],
        2,
        Some((
            pr(su(pv(2)), z()),
            vec![vec![(pr(su(pv(2)), z()), pr(z(), z()))]],
            vec![(2, vec![NAT])],
            3,
        )),
    );
}

#[test]
fn a_replacement_at_a_later_entry_gives_an_earlier_one_one_root() {
    let t = pr(su(pv(3)), su(z()));
    tight2_is(
        pr(pv(0), pv(1)),
        vec![vec![(pr(pv(0), pv(1)), pr(z(), su(z())))], vec![(pv(1), z())]],
        vec![(0, vec![NAT]), (1, vec![OPT])],
        2,
        Some((
            t.clone(),
            vec![vec![(t, pr(z(), su(z())))], vec![(su(z()), z())]],
            vec![(3, vec![NAT])],
            4,
        )),
    );
}

// Stores that denote nothing.

#[test]
fn an_entry_with_no_member_gives_nothing() {
    tight_is(pv(0), vec![], vec![(0, vec![VOID])], 1, None);
    tight_is(pr(pv(0), pv(1)), vec![], vec![(0, vec![NAT]), (1, vec![VOID])], 2, None);
}

#[test]
fn an_entry_of_two_sorts_with_no_member_in_common_gives_nothing() {
    tight_is(pv(0), vec![], vec![(0, vec![UNIT, TWO])], 1, None);
}

#[test]
fn an_exclusion_that_always_holds_gives_nothing() {
    tight_is(pv(0), vec![vec![(pv(0), pv(0))]], vec![(0, vec![NAT])], 1, None);
    tight_is(pv(0), vec![vec![]], vec![(0, vec![NAT])], 1, None);
    tight_is(pv(0), vec![vec![(z(), z())]], vec![(0, vec![NAT])], 1, None);
}

#[test]
fn an_exclusion_that_always_holds_once_a_variable_has_its_one_value_gives_nothing() {
    tight_is(pv(0), vec![vec![(pv(0), z())]], vec![(0, vec![UNIT])], 1, None);
}

#[test]
fn an_exclusion_that_always_holds_is_seen_before_any_replacement() {
    tight_is(pr(pv(0), pv(1)), vec![vec![(pv(1), pv(1))]], vec![(0, vec![BOX])], 2, None);
}

// What is returned, and the store afterwards.

fn results() -> Vec<(P, Excls, Entries, usize)> {
    vec![
        (pv(0), vec![], vec![(0, vec![C3])], 1),
        (pv(0), vec![vec![(pv(0), z())], vec![(pv(0), su(z()))]], vec![(0, vec![NAT])], 1),
        (g2(pv(0), g2(pv(1), pv(2))), vec![], vec![(0, vec![NAT]), (1, vec![PAIR]), (2, vec![MIX])], 3),
        (pr(pv(0), pv(1)), vec![vec![(pr(pv(0), pv(1)), pr(z(), z()))]], vec![(0, vec![NAT]), (1, vec![UNIT])], 2),
    ]
}

#[test]
fn tightening_what_was_returned_changes_nothing() {
    for (t, x, es, next) in results() {
        let mut fxt = fixture(wf());
        let (t1, x1, e1, n1) = run(&mut fxt, &t, &x, &es, next).expect("a store");
        let (t2, x2, e2, n2) =
            tighten(&mut fxt.s, fxt.decls, fxt.names, t1, x1, e1, n1).expect("a store");
        assert!(fxt.s.same(t1, t2) && fxt.s.same(x1, x2) && fxt.s.same(e1, e2) && fxt.s.same(n1, n2));
    }
}

#[test]
fn no_exclusion_returned_always_holds() {
    for (t, x, es, next) in results() {
        let mut fxt = fixture(wf());
        let (_, x1, _, _) = run(&mut fxt, &t, &x, &es, next).expect("a store");
        assert!(!any_always(&mut fxt.s, x1));
    }
}

#[test]
fn the_stack_is_left_empty_when_it_was_empty() {
    let mut fxt = fixture(wf());
    assert!(run(&mut fxt, &pv(0), &vec![], &vec![(0, vec![VOID])], 1).is_none());
    assert!(run(&mut fxt, &pv(0), &vec![vec![]], &vec![(0, vec![NAT])], 1).is_none());
    assert!(run(&mut fxt, &pv(0), &vec![], &vec![(0, vec![NAT])], 1).is_some());
    assert!(run(&mut fxt, &pv(0), &vec![], &vec![(0, vec![C3])], 1).is_some());
    let v = put_var(&mut fxt.s, 0);
    fxt.s.push(Frame::Visit(v, v));
    assert!(fxt.s.pop().is_some());
    assert!(fxt.s.pop().is_none());
}

#[test]
fn what_the_tables_held_before_does_not_change_the_result() {
    let mut fxt = fixture(wf());
    let v0 = put_var(&mut fxt.s, 0);
    let zi = put_pat(&mut fxt.s, &z());
    let ai = put_pat(&mut fxt.s, &a());
    fxt.s.set(Tbl::A, v0, ai);
    fxt.s.set(Tbl::A, zi, ai);
    fxt.s.set_flag(Tbl::B, v0, true);
    fxt.s.set_flag(Tbl::A, zi, true);
    let x = vec![vec![(pv(0), z())], vec![(pv(0), su(z()))]];
    let got = run(&mut fxt, &pv(0), &x, &vec![(0, vec![NAT])], 1);
    let t = su(su(pv(2)));
    let want = Some((t.clone(), vec![vec![(t.clone(), z())], vec![(t, su(z()))]], vec![(2, vec![NAT])], 3));
    check(&mut fxt, got, &want);
}

// Small stores.

#[test]
fn small_stores_agree_with_the_reference() {
    let pats = [pr(pv(0), pv(1)), g2(pv(0), g2(pv(1), pv(0)))];
    let excls: Vec<Excls> = vec![
        vec![],
        vec![vec![(pv(0), z())]],
        vec![vec![(pv(0), z())], vec![(pv(0), su(z()))]],
        vec![vec![(pv(1), k1(z()))]],
        vec![vec![(pr(pv(0), pv(1)), pr(z(), z()))]],
        vec![vec![(pv(0), pv(1))]],
        vec![vec![(pv(0), su(pv(0)))]],
        vec![vec![(pv(0), z())], vec![(pv(1), pv(1))]],
    ];
    let sorts = [vec![], vec![NAT], vec![UNIT], vec![BOX], vec![PAIR], vec![MIX], vec![VOID], vec![NAT, SUC], vec![C2]];
    for t in &pats {
        for x in &excls {
            for c0 in &sorts {
                for c1 in &sorts {
                    let es: Entries = vec![(0, c0.clone()), (1, c1.clone())];
                    let mut fxt = fixture(wf());
                    let want = tighten_ref(&fxt.ss, t, x, &es, 2);
                    let got = run(&mut fxt, t, x, &es, 2);
                    match (got, want) {
                        (None, None) => {}
                        (Some((t1, x1, e1, n1)), Some((wt, wx, wes, wn))) => {
                            let wti = put_pat(&mut fxt.s, &wt);
                            let wxi = put_excls(&mut fxt.s, &wx);
                            let wni = put_var(&mut fxt.s, wn as u128);
                            assert!(fxt.s.same(t1, wti), "{:?} {:?} {:?}", t, x, es);
                            assert!(fxt.s.same(x1, wxi), "{:?} {:?} {:?}", t, x, es);
                            assert_eq!(sets(&fxt.read_entries(e1)), wes, "{:?} {:?} {:?}", t, x, es);
                            assert!(fxt.s.same(n1, wni), "{:?} {:?} {:?}", t, x, es);
                        }
                        (g, w) => panic!("{:?} {:?} {:?}: {} against {:?}", t, x, es, g.is_some(), w),
                    }
                }
            }
        }
    }
}
