//! The exclusions of a normal store put together: whether one solved
//! exclusion removes only what another does (`sorts::covers`), the solved
//! forms of a list of exclusions (`sorts::norm_exs`), and the exclusions no
//! other covers (`sorts::antichain`); against `covers`, `normExs` and
//! `antichain` (`lean/RwLog/Sorts/Assemble.lean`).
//!
//! A solved exclusion is the list of the values it gives the variables,
//! which are numbered from 0; a free variable is its own value.

mod common;

use common::sorts::*;
use common::{get_list, put_var, T};
use rwlog_core::sorts::{antichain, covers, norm_ex, norm_exs};
use rwlog_core::store::{Node, Store, Tbl, TermId};

// Symbols.
const Z: u32 = 0;
const SU: u32 = 1;
const PR: u32 = 2;
const G: u32 = 4;
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

fn z() -> P {
    pf(Z, vec![])
}
fn a() -> P {
    pf(A, vec![])
}
fn su(p: P) -> P {
    pf(SU, vec![p])
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



fn vars(s: &mut Store, k: usize) -> TermId {
    let ps: Vec<P> = (0..k).map(pv).collect();
    put_pats(s, &ps)
}

fn put_lists(s: &mut Store, ls: &[Vec<P>]) -> TermId {
    let ids: Vec<TermId> = ls.iter().map(|l| put_pats(s, l)).collect();
    let mut out = s.alloc(Node::Nil);
    for id in ids.into_iter().rev() {
        out = s.alloc(Node::App(id, out));
    }
    out
}

fn get_lists(s: &mut Store, mut p: TermId) -> Vec<Vec<T>> {
    let mut out = Vec::new();
    loop {
        match s.read(p) {
            Node::Nil => return out,
            Node::App(h, rest) => {
                out.push(get_list(s, h));
                p = rest;
            }
            _ => panic!("a term where a list was expected"),
        }
    }
}

fn trees(ls: &[Vec<P>]) -> Vec<Vec<T>> {
    ls.iter().map(|l| l.iter().map(P::tree).collect()).collect()
}

fn conjs(f: &mut Fx, cs: &[Vec<Name>]) -> TermId {
    let ids: Vec<TermId> = cs.iter().map(|c| f.conj(c)).collect();
    let mut out = f.s.alloc(Node::Nil);
    for id in ids.into_iter().rev() {
        out = f.s.alloc(Node::App(id, out));
    }
    out
}

/// Tables with entries and flags left by earlier work.
fn dirty(s: &mut Store) {
    let v0 = put_var(s, 0);
    let v1 = put_var(s, 1);
    let v2 = put_var(s, 2);
    let zi = s.alloc(Node::Sym(Z));
    s.set(Tbl::A, v0, zi);
    s.set(Tbl::A, v1, v0);
    s.set(Tbl::A, zi, v2);
    s.set(Tbl::B, v0, v1);
    s.set(Tbl::B, v2, zi);
}

// Value lists over three variables.
fn id3() -> Vec<P> {
    vec![pv(0), pv(1), pv(2)]
}
fn lc() -> Vec<P> {
    vec![z(), pv(1), pv(2)]
}
fn lb() -> Vec<P> {
    vec![z(), su(pv(2)), pv(2)]
}
fn la() -> Vec<P> {
    vec![z(), su(z()), z()]
}
fn lq() -> Vec<P> {
    vec![pv(0), z(), pv(2)]
}
fn al() -> Vec<P> {
    vec![pv(0), pv(0), pv(2)]
}
fn lr() -> Vec<P> {
    vec![pr(pv(1), pv(1)), pv(1), pv(2)]
}

// One exclusion removes only what another does.

fn covers_is(a: &[P], b: &[P], want: bool) {
    let mut s = Store::new();
    let vs = vars(&mut s, a.len());
    let ai = put_pats(&mut s, a);
    let bi = put_pats(&mut s, b);
    dirty(&mut s);
    let r = covers(&mut s, vs, ai, bi);
    assert!(s.pop().is_none(), "the stack is not empty");
    assert_eq!(r, want, "{a:?} under {b:?}");
}

#[test]
fn covers_without_variables() {
    covers_is(&[], &[], true);
}

#[test]
fn covers_of_an_exclusion_and_itself() {
    covers_is(&lc(), &lc(), true);
    covers_is(&al(), &al(), true);
    covers_is(&id3(), &id3(), true);
}

#[test]
fn covers_holds_from_the_instance_to_the_general_one_only() {
    covers_is(&la(), &lc(), true);
    covers_is(&la(), &lb(), true);
    covers_is(&lb(), &lc(), true);
    covers_is(&lc(), &la(), false);
    covers_is(&lb(), &la(), false);
    covers_is(&lc(), &lb(), false);
}

#[test]
fn covers_by_the_exclusion_that_binds_nothing() {
    covers_is(&la(), &id3(), true);
    covers_is(&lc(), &id3(), true);
    covers_is(&id3(), &lc(), false);
}

#[test]
fn covers_fails_between_exclusions_that_bind_different_variables() {
    covers_is(&lc(), &lq(), false);
    covers_is(&lq(), &lc(), false);
}

#[test]
fn covers_fails_when_symbols_differ() {
    let a = [z(), pv(1), pv(2)];
    let b = [su(z()), pv(1), pv(2)];
    covers_is(&a, &b, false);
    covers_is(&b, &a, false);
}

#[test]
fn covers_of_an_alias_by_its_instances() {
    covers_is(&[z(), z(), pv(2)], &al(), true);
    covers_is(&al(), &[z(), z(), pv(2)], false);
    covers_is(&[z(), su(z()), pv(2)], &al(), false);
}

#[test]
fn covers_between_aliases() {
    let all = [pv(0), pv(0), pv(0)];
    covers_is(&all, &al(), true);
    covers_is(&al(), &all, false);
    covers_is(&al(), &[pv(0), pv(1), pv(1)], false);
}

#[test]
fn covers_with_a_repeated_variable_in_a_value() {
    covers_is(&[pr(su(z()), su(z())), su(z()), pv(2)], &lr(), true);
    covers_is(&[pr(pv(1), pv(2)), pv(1), pv(2)], &lr(), false);
    covers_is(&lr(), &[pr(pv(1), pv(2)), pv(1), pv(2)], false);
}

#[test]
fn covers_with_a_repeated_subterm_in_a_value() {
    let u = pr(pv(1), pv(1));
    let zz = pr(z(), z());
    covers_is(&[pr(zz.clone(), zz), z(), pv(2)], &[pr(u.clone(), u), pv(1), pv(2)], true);
}

#[test]
fn covers_replaces_the_variables_once() {
    covers_is(&[pv(1), z()], &[pv(0), pv(1)], true);
}

#[test]
fn covers_asks_for_the_values_of_the_first_to_be_instances_through_itself() {
    covers_is(&[pv(1), pv(0)], &[pv(1), pv(0)], false);
    covers_is(&[pv(0), pv(0)], &[pv(1), pv(1)], true);
    covers_is(&[pv(1), pv(1)], &[pv(0), pv(0)], true);
}

#[test]
fn covers_twice_does_not_reuse_what_the_first_call_rebuilt() {
    let mut s = Store::new();
    let vs = vars(&mut s, 3);
    let a1 = put_pats(&mut s, &la());
    let a2 = put_pats(&mut s, &[z(), z(), z()]);
    let c = put_pats(&mut s, &lc());
    assert!(covers(&mut s, vs, a1, c));
    assert!(covers(&mut s, vs, a2, c));
    assert!(!covers(&mut s, vs, c, a1));
    assert!(s.pop().is_none());
}

// The solved forms of a list of exclusions.

fn norm_exs_in(cs: &[Vec<Name>], x: &[Vec<(P, P)>]) -> (Vec<Vec<T>>, Vec<Option<Vec<T>>>) {
    let mut f = fixture(wf());
    let vs = vars(&mut f.s, cs.len());
    let ci = conjs(&mut f, cs);
    let xi = put_excls(&mut f.s, x);
    let (decls, names) = (f.decls, f.names);
    dirty(&mut f.s);
    let r = norm_exs(&mut f.s, decls, names, vs, ci, xi);
    f.empty_stack();
    let got = get_lists(&mut f.s, r);
    let mut each = Vec::new();
    for e in x {
        let ei = put_eqns(&mut f.s, e);
        let o = norm_ex(&mut f.s, decls, names, vs, ci, ei);
        each.push(o.map(|l| get_list(&mut f.s, l)));
    }
    (got, each)
}

/// The list is the solved form of each exclusion that has one, in order.
fn norm_exs_is(cs: &[Vec<Name>], x: &[Vec<(P, P)>], want: &[Vec<P>]) {
    let (got, each) = norm_exs_in(cs, x);
    assert_eq!(got, trees(want), "{cs:?} {x:?}");
    let some: Vec<Vec<T>> = each.into_iter().flatten().collect();
    assert_eq!(got, some, "{cs:?} {x:?}");
}

#[test]
fn norm_exs_of_no_exclusion_is_empty() {
    norm_exs_is(&[vec![], vec![]], &[], &[]);
}

#[test]
fn norm_exs_leaves_out_the_exclusions_that_exclude_nothing() {
    let x = vec![vec![(pv(0), su(pv(0)))], vec![(pv(0), a())]];
    norm_exs_is(&[vec![NAT]], &x, &[]);
}

#[test]
fn norm_exs_keeps_the_order_of_the_exclusions() {
    let x = vec![
        vec![(pv(0), z())],
        vec![(pv(0), su(pv(0)))],
        vec![(pv(1), z())],
    ];
    norm_exs_is(&[vec![], vec![]], &x, &[vec![z(), pv(1)], vec![pv(0), z()]]);
}

#[test]
fn norm_exs_keeps_two_exclusions_with_one_solved_form() {
    let x = vec![vec![(pv(0), pv(1))], vec![(pv(1), pv(0))]];
    norm_exs_is(&[vec![], vec![]], &x, &[vec![pv(0), pv(0)], vec![pv(0), pv(0)]]);
}

#[test]
fn norm_exs_binds_what_the_sorts_leave_one_value() {
    let x = vec![vec![(pv(0), su(pv(1)))]];
    norm_exs_is(&[vec![], vec![UNIT]], &x, &[vec![su(z()), z()]]);
}

#[test]
fn norm_exs_of_an_exclusion_without_equations() {
    norm_exs_is(&[vec![NAT], vec![]], &[vec![]], &[vec![pv(0), pv(1)]]);
    norm_exs_is(&[vec![VOID], vec![]], &[vec![]], &[]);
}

#[test]
fn norm_exs_without_variables() {
    norm_exs_is(&[], &[vec![]], &[vec![]]);
}

// The exclusions no other covers.

fn antichain_is(k: usize, l: &[Vec<P>], want: &[Vec<P>]) {
    let mut s = Store::new();
    let vs = vars(&mut s, k);
    let li = put_lists(&mut s, l);
    dirty(&mut s);
    let r = antichain(&mut s, vs, li);
    assert!(s.pop().is_none(), "the stack is not empty");
    assert_eq!(get_lists(&mut s, r), trees(want), "{l:?}");
}

#[test]
fn antichain_of_no_exclusion_and_of_one() {
    antichain_is(3, &[], &[]);
    antichain_is(3, &[la()], &[la()]);
}

#[test]
fn antichain_keeps_the_later_of_two_equal_exclusions() {
    antichain_is(3, &[la(), la()], &[la()]);
    antichain_is(3, &[la(), lq(), la()], &[lq(), la()]);
}

#[test]
fn antichain_of_a_chain_is_its_most_general_member_in_every_order() {
    let (a, b, c) = (la(), lb(), lc());
    let want = [c.clone()];
    antichain_is(3, &[a.clone(), b.clone(), c.clone()], &want);
    antichain_is(3, &[a.clone(), c.clone(), b.clone()], &want);
    antichain_is(3, &[b.clone(), a.clone(), c.clone()], &want);
    antichain_is(3, &[b.clone(), c.clone(), a.clone()], &want);
    antichain_is(3, &[c.clone(), a.clone(), b.clone()], &want);
    antichain_is(3, &[c, b, a], &want);
}

#[test]
fn antichain_of_two_comparable_exclusions() {
    antichain_is(3, &[la(), lc()], &[lc()]);
    antichain_is(3, &[lc(), la()], &[lc()]);
}

#[test]
fn antichain_keeps_exclusions_that_do_not_cover_each_other_in_order() {
    antichain_is(3, &[lc(), lq()], &[lc(), lq()]);
    antichain_is(3, &[lq(), lc()], &[lq(), lc()]);
}

#[test]
fn antichain_drops_members_after_others_that_the_first_covers() {
    antichain_is(3, &[lc(), la(), lq(), lb()], &[lc(), lq()]);
    let b2 = vec![z(), z(), pv(2)];
    antichain_is(3, &[lc(), la(), lq(), b2.clone()], &[lc(), lq()]);
    antichain_is(3, &[la(), lq(), b2], &[la(), lq()]);
}

#[test]
fn antichain_drops_the_first_when_a_later_member_covers_it() {
    antichain_is(3, &[la(), lq(), lc()], &[lq(), lc()]);
}

#[test]
fn antichain_of_an_alias_and_its_instance() {
    let zz = vec![z(), z(), pv(2)];
    antichain_is(3, &[zz.clone(), al()], &[al()]);
    antichain_is(3, &[al(), zz], &[al()]);
}

#[test]
fn antichain_with_the_exclusion_that_binds_nothing_is_that_one() {
    antichain_is(3, &[la(), id3(), lq()], &[id3()]);
    antichain_is(3, &[id3(), la()], &[id3()]);
}

#[test]
fn antichain_without_variables() {
    antichain_is(0, &[vec![], vec![]], &[vec![]]);
}
