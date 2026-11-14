//! The steps that bring a store to a tight one: the next variable
//! (`sorts::var_succ`), replacing each variable whose sorts have one member
//! by that member (`sorts::settle`), and replacing a variable by a symbol
//! applied to new variables (`sorts::open_var`), against `CStore.settle`,
//! `CStore.set` and `CStore.exp` of the specification
//! (`lean/RwLog/Sorts/Loop.lean`) as written on trees here.
//!
//! A store is a pattern, a list of exclusions and a list of entries: an
//! entry is a variable with the conjunction of its sorts.

mod common;

use common::sorts::*;
use common::{get, put_var, T};
use rwlog_core::sorts::{open_var, settle, var_succ};
use rwlog_core::store::{Frame, Node, Store, TermId};
use std::collections::BTreeMap;

// Symbols.
const Z: u32 = 0;
const SU: u32 = 1;
const PR: u32 = 2;
const F: u32 = 3;
const G: u32 = 4;
const H: u32 = 5;
const K: u32 = 6;
const C: u32 = 7;

// Names.
const UNIT: Name = 100;
const NAT: Name = 101;
const VOID: Name = 102;
const TWO: Name = 103;

fn z() -> P {
    pf(Z, vec![])
}
fn su(p: P) -> P {
    pf(SU, vec![p])
}
fn f1(p: P) -> P {
    pf(F, vec![p])
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

/// `unit` is `z`; `nat` is `z` or `s` of a `nat`; `void` is `s` of a `void`,
/// which nothing is; `two` is the pair of two `unit`.
fn defs() -> Vec<(Name, Def)> {
    vec![
        (UNIT, Def { cases: vec![(Z, vec![])], rest: None }),
        (NAT, Def { cases: vec![(Z, vec![]), (SU, vec![Some(NAT)])], rest: None }),
        (VOID, Def { cases: vec![(SU, vec![Some(VOID)])], rest: None }),
        (TWO, Def { cases: vec![(PR, vec![Some(UNIT), Some(UNIT)])], rest: None }),
    ]
}

type Excls = Vec<Vec<(P, P)>>;
type Entries = Vec<(usize, Vec<Name>)>;

struct Fx {
    s: Store,
    ss: Sorts,
    decls: TermId,
    order: Vec<Name>,
    names: TermId,
}

fn fx() -> Fx {
    let ss = Sorts::new(defs());
    let mut s = Store::new();
    let decls = put_sorts(&mut s, &ss);
    let order = ss.all_names();
    let names = put_names(&mut s, &order);
    Fx { s, ss, decls, order, names }
}

impl Fx {
    fn conj(&mut self, c: &[Name]) -> TermId {
        let set: Conj = c.iter().copied().collect();
        let list = canon(&self.order, &set);
        put_names(&mut self.s, &list)
    }

    fn entries(&mut self, es: &[(usize, Vec<Name>)]) -> TermId {
        let mut out = self.s.alloc(Node::Nil);
        for (v, c) in es.iter().rev() {
            let vi = put_var(&mut self.s, *v as u128);
            let ci = self.conj(c);
            let e = self.s.alloc(Node::App(vi, ci));
            out = self.s.alloc(Node::App(e, out));
        }
        out
    }

    fn read_entries(&mut self, mut p: TermId) -> Entries {
        let mut out = Vec::new();
        loop {
            match self.s.read(p) {
                Node::Nil => return out,
                Node::App(e, rest) => {
                    match self.s.read(e) {
                        Node::App(v, c) => {
                            let n = match get(&mut self.s, v) {
                                T::V(n) => n as usize,
                                _ => panic!("an entry of something that is not a variable"),
                            };
                            out.push((n, get_names(&mut self.s, c)));
                        }
                        _ => panic!("an entry that is not a pair"),
                    }
                    p = rest;
                }
                _ => panic!("a term where a list was expected"),
            }
        }
    }

    fn empty_stack(&mut self) {
        assert!(self.s.pop().is_none(), "the stack is not empty");
    }
}

/// `CStore.settle` on trees.
fn settle_ref(ss: &Sorts, t: &P, x: &Excls, es: &Entries) -> (P, Excls, Entries) {
    let mut t = t.clone();
    let mut x = x.clone();
    let mut kept = Vec::new();
    for (v, c) in es {
        let set: Conj = c.iter().copied().collect();
        match ss.size(&set) {
            Size::One(g) => {
                let one = BTreeMap::from([(*v, g)]);
                t = t.subst(&one);
                for e in x.iter_mut() {
                    for (a, b) in e.iter_mut() {
                        *a = a.subst(&one);
                        *b = b.subst(&one);
                    }
                }
            }
            _ => kept.push((*v, c.clone())),
        }
    }
    (t, x, kept)
}

/// `settle` in the store is `settle_ref`, and is the answer written by hand.
fn settle_is(t: P, x: Excls, es: Entries, want: (P, Excls, Entries)) {
    let mut f = fx();
    assert_eq!(settle_ref(&f.ss, &t, &x, &es), want, "the reference");
    let ti = put_pat(&mut f.s, &t);
    let xi = put_excls(&mut f.s, &x);
    let ei = f.entries(&es);
    let (t1, x1, e1) = settle(&mut f.s, f.decls, f.names, ti, xi, ei);
    f.empty_stack();
    let wt = put_pat(&mut f.s, &want.0);
    let wx = put_excls(&mut f.s, &want.1);
    assert!(f.s.same(t1, wt), "the pattern is {:?}", get(&mut f.s, t1));
    assert!(f.s.same(x1, wx), "the exclusions are {:?}", get(&mut f.s, x1));
    assert_eq!(f.read_entries(e1), want.2, "the entries");
}

/// `CStore.exp` on trees: the pattern, the exclusions, the new entries and
/// the next variable.
fn open_ref(v: usize, f: u32, kids: &[Vec<Name>], next: usize, t: &P, x: &Excls) -> (P, Excls, Entries, usize) {
    let args: Vec<P> = (0..kids.len()).map(|i| pv(next + i)).collect();
    let one = BTreeMap::from([(v, pf(f, args))]);
    let x1 = x
        .iter()
        .map(|e| e.iter().map(|(a, b)| (a.subst(&one), b.subst(&one))).collect())
        .collect();
    let es = kids.iter().enumerate().map(|(i, k)| (next + i, k.clone())).collect();
    (t.subst(&one), x1, es, next + kids.len())
}

fn open_in(fxt: &mut Fx, v: usize, f: u32, kids: &[Vec<Name>], next: usize, t: &P, x: &Excls) -> (TermId, TermId, TermId, TermId) {
    let ti = put_pat(&mut fxt.s, t);
    let xi = put_excls(&mut fxt.s, x);
    let vi = put_var(&mut fxt.s, v as u128);
    let fi = fxt.s.alloc(Node::Sym(f));
    let ni = put_var(&mut fxt.s, next as u128);
    let mut ki = fxt.s.alloc(Node::Nil);
    for k in kids.iter().rev() {
        let c = fxt.conj(k);
        ki = fxt.s.alloc(Node::App(c, ki));
    }
    let got = open_var(&mut fxt.s, vi, fi, ki, ni, ti, xi);
    fxt.empty_stack();
    got
}

fn open_is(v: usize, f: u32, kids: &[Vec<Name>], next: usize, t: P, x: Excls, want: (P, Excls, Entries, usize)) {
    assert_eq!(open_ref(v, f, kids, next, &t, &x), want, "the reference");
    let mut fxt = fx();
    let (t1, x1, e1, n1) = open_in(&mut fxt, v, f, kids, next, &t, &x);
    let wt = put_pat(&mut fxt.s, &want.0);
    let wx = put_excls(&mut fxt.s, &want.1);
    let wn = put_var(&mut fxt.s, want.3 as u128);
    assert!(fxt.s.same(t1, wt), "the pattern is {:?}", get(&mut fxt.s, t1));
    assert!(fxt.s.same(x1, wx), "the exclusions are {:?}", get(&mut fxt.s, x1));
    assert_eq!(fxt.read_entries(e1), want.2, "the entries");
    assert!(fxt.s.same(n1, wn), "the next variable is {:?}", get(&mut fxt.s, n1));
}

// The next variable.

fn succ_of(n: u128) -> T {
    let mut s = Store::new();
    let v = put_var(&mut s, n);
    let r = var_succ(&mut s, v);
    assert!(s.pop().is_none(), "the stack is not empty");
    let w = put_var(&mut s, n + 1);
    assert!(s.same(r, w), "another node than that of the next number");
    get(&mut s, r)
}

#[test]
fn the_variable_after_zero_is_one() {
    assert_eq!(succ_of(0), T::V(1));
}

#[test]
fn the_variable_after_an_even_number_changes_its_last_digit() {
    assert_eq!(succ_of(2), T::V(3));
    assert_eq!(succ_of(6), T::V(7));
    assert_eq!(succ_of(8), T::V(9));
}

#[test]
fn the_variable_after_an_odd_number_carries() {
    assert_eq!(succ_of(1), T::V(2));
    assert_eq!(succ_of(5), T::V(6));
}

#[test]
fn the_variable_after_all_ones_is_a_power_of_two() {
    assert_eq!(succ_of(3), T::V(4));
    assert_eq!(succ_of(7), T::V(8));
    assert_eq!(succ_of((1u128 << 100) - 1), T::V(1u128 << 100));
}

#[test]
fn every_small_variable_has_the_next_number() {
    for n in 0..300u128 {
        assert_eq!(succ_of(n), T::V(n + 1));
    }
}

#[test]
fn a_long_carry_does_not_use_the_call_stack() {
    let mut s = Store::new();
    let mut v = s.alloc(Node::V0);
    for _ in 0..200_000 {
        v = s.alloc(Node::VR(v));
    }
    let mut r = var_succ(&mut s, v);
    assert!(s.pop().is_none(), "the stack is not empty");
    let mut zeros = 0;
    while let Node::VL(a) = s.read(r) {
        zeros += 1;
        r = a;
    }
    assert_eq!(zeros, 200_000);
    match s.read(r) {
        Node::VR(a) => assert!(matches!(s.read(a), Node::V0)),
        _ => panic!("the leading digit is not one"),
    }
}

#[test]
#[should_panic]
fn the_next_of_a_symbol_is_refused() {
    let mut s = Store::new();
    let f = s.alloc(Node::Sym(F));
    let _ = var_succ(&mut s, f);
}

// Settling.

#[test]
fn no_entry_changes_nothing() {
    settle_is(f1(pv(1)), vec![], vec![], (f1(pv(1)), vec![], vec![]));
}

#[test]
fn a_variable_of_a_sort_with_one_member_becomes_that_member() {
    settle_is(f1(pv(1)), vec![], vec![(1, vec![UNIT])], (f1(z()), vec![], vec![]));
}

#[test]
fn the_one_member_may_have_arguments() {
    settle_is(f1(pv(1)), vec![], vec![(1, vec![TWO])], (f1(pr(z(), z())), vec![], vec![]));
}

#[test]
fn a_variable_of_a_sort_with_many_members_stays() {
    settle_is(f1(pv(1)), vec![], vec![(1, vec![NAT])], (f1(pv(1)), vec![], vec![(1, vec![NAT])]));
}

#[test]
fn a_variable_of_a_sort_with_no_member_stays() {
    settle_is(f1(pv(1)), vec![], vec![(1, vec![VOID])], (f1(pv(1)), vec![], vec![(1, vec![VOID])]));
}

#[test]
fn a_variable_of_two_sorts_with_one_member_in_common_becomes_it() {
    settle_is(f1(pv(1)), vec![], vec![(1, vec![UNIT, NAT])], (f1(z()), vec![], vec![]));
}

#[test]
fn a_variable_of_no_sort_stays() {
    settle_is(f1(pv(1)), vec![], vec![(1, vec![])], (f1(pv(1)), vec![], vec![(1, vec![])]));
}

#[test]
fn the_entries_kept_are_in_their_order() {
    settle_is(
        g2(pv(1), g2(pv(2), pv(3))),
        vec![],
        vec![(1, vec![NAT]), (2, vec![UNIT]), (3, vec![NAT])],
        (g2(pv(1), g2(z(), pv(3))), vec![], vec![(1, vec![NAT]), (3, vec![NAT])]),
    );
}

#[test]
fn two_variables_are_each_replaced_by_their_own_member() {
    settle_is(
        g2(pv(1), pv(2)),
        vec![],
        vec![(1, vec![UNIT]), (2, vec![TWO])],
        (g2(z(), pr(z(), z())), vec![], vec![]),
    );
}

#[test]
fn a_variable_in_the_exclusions_is_replaced_there() {
    settle_is(
        f1(pv(2)),
        vec![vec![(pv(2), su(pv(1)))], vec![(pv(1), pv(2)), (pv(2), z())]],
        vec![(1, vec![UNIT])],
        (f1(pv(2)), vec![vec![(pv(2), su(z()))], vec![(z(), pv(2)), (pv(2), z())]], vec![]),
    );
}

#[test]
fn a_variable_that_occurs_nowhere_only_loses_its_entry() {
    settle_is(
        f1(pv(2)),
        vec![vec![(pv(2), z())]],
        vec![(1, vec![UNIT])],
        (f1(pv(2)), vec![vec![(pv(2), z())]], vec![]),
    );
}

#[test]
fn every_place_of_a_shared_subterm_is_replaced() {
    settle_is(
        h2(k1(pv(1)), k1(pv(1))),
        vec![],
        vec![(1, vec![UNIT])],
        (h2(k1(z()), k1(z())), vec![], vec![]),
    );
}

#[test]
fn other_variables_are_left_alone() {
    settle_is(
        g2(pv(1), g2(pv(2), pv(3))),
        vec![vec![(pv(3), pv(2))]],
        vec![(1, vec![UNIT])],
        (g2(z(), g2(pv(2), pv(3))), vec![vec![(pv(3), pv(2))]], vec![]),
    );
}

#[test]
fn the_variable_zero_is_settled_like_another() {
    settle_is(f1(pv(0)), vec![], vec![(0, vec![UNIT])], (f1(z()), vec![], vec![]));
}

#[test]
fn settling_nothing_gives_back_the_same_nodes() {
    let mut f = fx();
    let ti = put_pat(&mut f.s, &f1(pv(1)));
    let xi = put_excls(&mut f.s, &[vec![(pv(1), z())]]);
    let ei = f.entries(&[(1, vec![NAT])]);
    let (t1, x1, _) = settle(&mut f.s, f.decls, f.names, ti, xi, ei);
    assert!(f.s.same(t1, ti));
    assert!(f.s.same(x1, xi));
}

#[test]
fn settle_leaves_the_stack_empty() {
    let mut f = fx();
    let ti = put_pat(&mut f.s, &g2(pv(1), pv(2)));
    let xi = put_excls(&mut f.s, &[]);
    let ei = f.entries(&[(1, vec![UNIT]), (2, vec![NAT])]);
    let _ = settle(&mut f.s, f.decls, f.names, ti, xi, ei);
    let v = put_var(&mut f.s, 1);
    f.s.push(Frame::Visit(v, v));
    assert!(f.s.pop().is_some());
    assert!(f.s.pop().is_none());
}

// Replacing a variable by a symbol applied to new variables.

#[test]
fn a_symbol_without_arguments_replaces_the_variable_and_makes_none() {
    open_is(1, C, &[], 2, f1(pv(1)), vec![], (f1(pf(C, vec![])), vec![], vec![], 2));
}

#[test]
fn one_argument_is_one_new_variable_with_its_sorts() {
    open_is(
        1,
        C,
        &[vec![NAT]],
        2,
        f1(pv(1)),
        vec![],
        (f1(pf(C, vec![pv(2)])), vec![], vec![(2, vec![NAT])], 3),
    );
}

#[test]
fn the_new_variables_are_numbered_in_the_order_of_the_arguments() {
    open_is(
        1,
        C,
        &[vec![NAT], vec![UNIT], vec![UNIT, NAT]],
        3,
        f1(pv(1)),
        vec![],
        (
            f1(pf(C, vec![pv(3), pv(4), pv(5)])),
            vec![],
            vec![(3, vec![NAT]), (4, vec![UNIT]), (5, vec![UNIT, NAT])],
            6,
        ),
    );
}

#[test]
fn the_numbers_carry() {
    open_is(
        1,
        C,
        &[vec![NAT], vec![NAT]],
        7,
        f1(pv(1)),
        vec![],
        (f1(pf(C, vec![pv(7), pv(8)])), vec![], vec![(7, vec![NAT]), (8, vec![NAT])], 9),
    );
}

#[test]
fn an_argument_of_no_sort_still_takes_a_number() {
    open_is(
        1,
        C,
        &[vec![NAT], vec![], vec![UNIT]],
        2,
        f1(pv(1)),
        vec![],
        (
            f1(pf(C, vec![pv(2), pv(3), pv(4)])),
            vec![],
            vec![(2, vec![NAT]), (3, vec![]), (4, vec![UNIT])],
            5,
        ),
    );
}

#[test]
fn every_place_of_the_variable_is_replaced_in_the_pattern_and_the_exclusions() {
    open_is(
        1,
        SU,
        &[vec![NAT]],
        3,
        g2(pv(1), h2(pv(1), pv(2))),
        vec![vec![(pv(1), z())], vec![(pv(2), su(pv(1)))]],
        (
            g2(su(pv(3)), h2(su(pv(3)), pv(2))),
            vec![vec![(su(pv(3)), z())], vec![(pv(2), su(su(pv(3))))]],
            vec![(3, vec![NAT])],
            4,
        ),
    );
}

#[test]
fn a_variable_that_is_not_there_changes_nothing_but_the_entries_are_made() {
    open_is(
        1,
        C,
        &[vec![NAT]],
        3,
        f1(pv(2)),
        vec![vec![(pv(2), z())]],
        (f1(pv(2)), vec![vec![(pv(2), z())]], vec![(3, vec![NAT])], 4),
    );
}

#[test]
fn a_variable_only_in_the_exclusions_leaves_the_node_of_the_pattern() {
    let mut fxt = fx();
    let t = f1(pv(2));
    let ti = put_pat(&mut fxt.s, &t);
    let (t1, _, _, _) = open_in(&mut fxt, 1, C, &[vec![NAT]], 3, &t, &vec![vec![(pv(1), z())]]);
    assert!(fxt.s.same(t1, ti));
}

#[test]
fn the_new_variables_can_be_settled() {
    let mut fxt = fx();
    let (t1, x1, e1, _) = open_in(&mut fxt, 1, C, &[vec![UNIT], vec![NAT]], 2, &f1(pv(1)), &vec![]);
    let (t2, _, e2) = settle(&mut fxt.s, fxt.decls, fxt.names, t1, x1, e1);
    fxt.empty_stack();
    let want = put_pat(&mut fxt.s, &f1(pf(C, vec![z(), pv(3)])));
    assert!(fxt.s.same(t2, want), "the pattern is {:?}", get(&mut fxt.s, t2));
    assert_eq!(fxt.read_entries(e2), vec![(3, vec![NAT])]);
}
