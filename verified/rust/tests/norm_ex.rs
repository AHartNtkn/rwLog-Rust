//! An exclusion brought to solved form under the sorts (`sorts::norm_ex`),
//! with what it is made of: the list of the variables of a numbered store
//! (`sorts::places`), aliases turned to the earlier variable
//! (`sorts::orient`), the sorts of the variables pushed onto their values
//! (`sorts::push_all`), the sorts this puts on one variable (`sorts::ups`),
//! and the variables left with one value bound to it (`sorts::close`);
//! against `normEx` of the specification
//! (`lean/RwLog/Sorts/NormEx.lean`, `Orient.lean`, `Solved.lean`).
//!
//! The variables of the store are numbered from 0, and a solved exclusion
//! is kept as the list of the values it gives them, a free variable having
//! itself as its value.

mod common;

use common::sorts::*;
use common::{get_list, put_var, T};
use rwlog_core::sorts::{close, norm_ex, orient, places, push_all, ups};
use rwlog_core::store::{Node, Store, Tbl, TermId};
use std::collections::{BTreeMap, BTreeSet};

// Symbols.
const Z: u32 = 0;
const SU: u32 = 1;
const PR: u32 = 2;
const F: u32 = 3;
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
fn f1(p: P) -> P {
    pf(F, vec![p])
}
fn f2(p: P, q: P) -> P {
    pf(F, vec![p, q])
}
fn g2(p: P, q: P) -> P {
    pf(G, vec![p, q])
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


fn kk(p: P) -> P {
    pf(K, vec![p])
}

fn vars(s: &mut Store, k: usize) -> TermId {
    let ps: Vec<P> = (0..k).map(pv).collect();
    put_pats(s, &ps)
}

fn conjs(f: &mut Fx, cs: &[Vec<Name>]) -> TermId {
    let ids: Vec<TermId> = cs.iter().map(|c| f.conj(c)).collect();
    let mut out = f.s.alloc(Node::Nil);
    for id in ids.into_iter().rev() {
        out = f.s.alloc(Node::App(id, out));
    }
    out
}

fn atoms(s: &mut Store, at: &[(usize, Name)]) -> TermId {
    let mut out = s.alloc(Node::Nil);
    for (v, n) in at.iter().rev() {
        let vi = put_var(s, *v as u128);
        let ni = s.alloc(Node::Sym(*n));
        let a = s.alloc(Node::App(vi, ni));
        out = s.alloc(Node::App(a, out));
    }
    out
}

fn read_atoms(s: &mut Store, mut p: TermId) -> BTreeSet<(usize, Name)> {
    let mut out = BTreeSet::new();
    loop {
        match s.read(p) {
            Node::Nil => return out,
            Node::App(a, rest) => {
                match s.read(a) {
                    Node::App(v, n) => {
                        let v = match common::get(s, v) {
                            T::V(v) => v as usize,
                            _ => panic!("an atom of something that is not a variable"),
                        };
                        match s.read(n) {
                            Node::Sym(n) => out.insert((v, n)),
                            _ => panic!("an atom of something that is not a sort"),
                        };
                    }
                    _ => panic!("an atom that is not a pair"),
                }
                p = rest;
            }
            _ => panic!("a term where a list was expected"),
        }
    }
}

fn trees(ps: &[P]) -> Vec<T> {
    ps.iter().map(P::tree).collect()
}

// The variables of a numbered store.

fn places_is(cs: &[Vec<Name>], k: usize) {
    let mut f = fixture(wf());
    let ci = conjs(&mut f, cs);
    let w = vars(&mut f.s, k);
    let r = places(&mut f.s, ci);
    f.empty_stack();
    assert!(f.s.same(r, w));
}

#[test]
fn places_of_no_conjunction_is_empty() {
    places_is(&[], 0);
}

#[test]
fn places_of_one_conjunction_is_the_first_variable() {
    places_is(&[vec![NAT]], 1);
}

#[test]
fn places_counts_the_conjunctions_not_their_sorts() {
    places_is(&[vec![NAT], vec![], vec![UNIT, NAT]], 3);
}

#[test]
fn places_of_many_conjunctions() {
    places_is(&vec![vec![]; 9], 9);
}

// Aliases turned to the earlier variable.

fn orient_is(vals: &[P], want: &[P]) {
    let mut s = Store::new();
    let vs = vars(&mut s, vals.len());
    let vi = put_pats(&mut s, vals);
    let w = put_pats(&mut s, want);
    let r = orient(&mut s, vs, vi);
    assert!(s.pop().is_none(), "the stack is not empty");
    assert!(s.same(r, w), "{vals:?}: {:?}", get_list(&mut s, r));
}

#[test]
fn orient_leaves_free_variables() {
    orient_is(&[pv(0), pv(1)], &[pv(0), pv(1)]);
}

#[test]
fn orient_turns_an_alias_to_the_earlier_variable() {
    orient_is(&[pv(1), pv(1)], &[pv(0), pv(0)]);
}

#[test]
fn orient_keeps_an_alias_to_the_earlier_variable() {
    orient_is(&[pv(0), pv(0)], &[pv(0), pv(0)]);
}

#[test]
fn orient_turns_a_chain_to_its_first_variable() {
    orient_is(&[pv(2), pv(2), pv(2)], &[pv(0), pv(0), pv(0)]);
}

#[test]
fn orient_of_an_alias_among_later_variables() {
    orient_is(&[pv(0), pv(2), pv(2)], &[pv(0), pv(1), pv(1)]);
}

#[test]
fn orient_renames_inside_a_value() {
    orient_is(&[f1(pv(2)), pv(2), pv(2)], &[f1(pv(1)), pv(1), pv(1)]);
}

#[test]
fn orient_renames_all_at_once() {
    orient_is(&[pv(1), pv(1), f2(pv(1), pv(1))], &[pv(0), pv(0), f2(pv(0), pv(0))]);
}

#[test]
fn orient_of_two_aliases_that_cross() {
    orient_is(&[pv(3), pv(2), pv(2), pv(3)], &[pv(0), pv(1), pv(1), pv(0)]);
}

#[test]
fn orient_leaves_values_without_variables() {
    orient_is(&[z(), su(z())], &[z(), su(z())]);
}

#[test]
fn orient_of_no_variable() {
    orient_is(&[], &[]);
}

// The sorts of the variables pushed onto their values.

fn push_all_is(cs: &[Vec<Name>], vals: &[P], want: Option<&[(usize, Name)]>) {
    let mut f = fixture(wf());
    let ci = conjs(&mut f, cs);
    let vi = put_pats(&mut f.s, vals);
    let decls = f.decls;
    let r = push_all(&mut f.s, decls, ci, vi);
    f.empty_stack();
    let got = r.map(|a| read_atoms(&mut f.s, a));
    assert_eq!(got, want.map(|w| w.iter().copied().collect()), "{cs:?} on {vals:?}");
}

#[test]
fn push_all_gives_a_free_variable_its_own_sorts() {
    push_all_is(&[vec![NAT, SUC]], &[pv(0)], Some(&[(0, NAT), (0, SUC)]));
}

#[test]
fn push_all_without_sorts_gives_no_atom() {
    push_all_is(&[vec![], vec![]], &[a(), pv(1)], Some(&[]));
}

#[test]
fn push_all_of_a_ground_value_in_its_sort_gives_no_atom() {
    push_all_is(&[vec![NAT]], &[su(z())], Some(&[]));
}

#[test]
fn push_all_is_nothing_when_a_sort_rejects_the_root() {
    push_all_is(&[vec![NAT]], &[a()], None);
}

#[test]
fn push_all_is_nothing_when_a_sort_rejects_a_symbol_inside() {
    push_all_is(&[vec![NAT]], &[su(a())], None);
}

#[test]
fn push_all_is_nothing_when_a_later_value_is_rejected() {
    push_all_is(&[vec![], vec![BOX]], &[pv(0), su(pv(0))], None);
}

#[test]
fn push_all_is_nothing_when_the_second_sort_of_a_variable_rejects() {
    push_all_is(&[vec![NAT, BOX]], &[su(pv(0))], None);
}

#[test]
fn push_all_goes_through_a_value_to_its_variables() {
    push_all_is(
        &[vec![MIX], vec![], vec![]],
        &[g2(pv(1), pv(2)), pv(1), pv(2)],
        Some(&[(1, UNIT), (2, NAT)]),
    );
}

#[test]
fn push_all_sends_the_sorts_of_an_alias_to_its_variable() {
    push_all_is(&[vec![NAT], vec![UNIT]], &[pv(0), pv(0)], Some(&[(0, NAT), (0, UNIT)]));
}

#[test]
fn push_all_of_no_variable() {
    push_all_is(&[], &[], Some(&[]));
}

// The sorts put on one variable.

fn ups_is(at: &[(usize, Name)], y: usize, want: &[Name]) {
    let mut f = fixture(wf());
    let ai = atoms(&mut f.s, at);
    let yi = put_var(&mut f.s, y as u128);
    let w = f.conj(want);
    let names = f.names;
    let r = ups(&mut f.s, names, ai, yi);
    f.empty_stack();
    assert!(f.s.same(r, w), "{at:?} at {y}: {:?}", get_names(&mut f.s, r));
}

#[test]
fn ups_without_atoms_is_no_sort() {
    ups_is(&[], 0, &[]);
}

#[test]
fn ups_of_a_variable_without_atom_is_no_sort() {
    ups_is(&[(0, NAT)], 1, &[]);
}

#[test]
fn ups_collects_the_sorts_once_each_as_a_conjunction() {
    ups_is(&[(0, UNIT), (1, SUC), (0, NAT), (0, UNIT)], 0, &[NAT, UNIT]);
    ups_is(&[(0, UNIT), (1, SUC), (0, NAT), (0, UNIT)], 1, &[SUC]);
}

#[test]
fn ups_does_not_take_a_variable_for_one_inside_its_node() {
    ups_is(&[(1, NAT), (2, SUC)], 0, &[]);
    ups_is(&[(0, NAT)], 1, &[]);
}

// The variables left with one value bound to it.

fn close_is(vals: &[P], at: &[(usize, Name)], want: Option<&[P]>) {
    let mut f = fixture(wf());
    let vs = vars(&mut f.s, vals.len());
    let vi = put_pats(&mut f.s, vals);
    let ai = atoms(&mut f.s, at);
    let (decls, names) = (f.decls, f.names);
    let r = close(&mut f.s, decls, names, vs, vi, ai);
    f.empty_stack();
    let got = r.map(|l| get_list(&mut f.s, l));
    assert_eq!(got, want.map(trees), "{vals:?} with {at:?}");
}

#[test]
fn close_without_atoms_keeps_the_values() {
    close_is(&[pv(0), su(pv(0))], &[], Some(&[pv(0), su(pv(0))]));
}

#[test]
fn close_is_nothing_when_a_variable_has_no_value() {
    close_is(&[pv(0), pv(1)], &[(1, VOID)], None);
}

#[test]
fn close_is_nothing_when_a_bound_variable_has_atoms_without_value() {
    close_is(&[pv(0), pv(0)], &[(1, VOID)], None);
}

#[test]
fn close_binds_a_variable_with_one_value_and_replaces_it() {
    close_is(&[pv(0), su(pv(0))], &[(0, UNIT)], Some(&[z(), su(z())]));
}

#[test]
fn close_does_not_bind_a_bound_variable() {
    close_is(&[pv(0), pv(0)], &[(1, UNIT)], Some(&[pv(0), pv(0)]));
}

#[test]
fn close_keeps_a_variable_with_many_values() {
    close_is(&[pv(0), pv(1)], &[(0, NAT), (0, SUC)], Some(&[pv(0), pv(1)]));
}

#[test]
fn close_binds_two_variables_with_one_value() {
    close_is(
        &[pv(0), pv(1), pr(pv(0), pv(1))],
        &[(0, UNIT), (1, UNIT)],
        Some(&[z(), z(), pr(z(), z())]),
    );
}

#[test]
fn close_is_nothing_when_a_later_variable_has_no_value() {
    close_is(&[pv(0), pv(1)], &[(0, UNIT), (1, VOID)], None);
}

#[test]
fn close_takes_the_sorts_of_a_variable_together() {
    close_is(&[pv(0)], &[(0, NAT), (0, UNIT)], Some(&[z()]));
    close_is(&[pv(0)], &[(0, SUC), (0, UNIT)], None);
}

// The solved form.

type Vals = Option<Vec<P>>;

/// `normEx` of the specification on trees, as the list of the values of the
/// variables.
fn norm_ex_ref(ss: &Sorts, cs: &[Vec<Name>], e: &[(P, P)]) -> Vals {
    let k = cs.len();
    let m = mgu(e)?;
    let mut vals: Vec<P> = (0..k).map(|i| pv(i).subst(&m)).collect();
    let mut put: BTreeMap<usize, Conj> = BTreeMap::new();
    for (c, p) in cs.iter().zip(&vals) {
        for n in c {
            for (y, n1) in push(ss, *n, p)? {
                put.entry(y).or_default().insert(n1);
            }
        }
    }
    if put.values().any(|c| matches!(ss.size(c), Size::Empty)) {
        return None;
    }
    let given = vals.clone();
    for (y, own) in given.iter().enumerate() {
        if *own == pv(y) {
            if let Some(Size::One(g)) = put.get(&y).map(|c| ss.size(c)) {
                let one = BTreeMap::from([(y, g)]);
                for p in vals.iter_mut() {
                    *p = p.subst(&one);
                }
            }
        }
    }
    Some(vals)
}

fn norm_ex_in(f: &mut Fx, prep: impl FnOnce(&mut Store), cs: &[Vec<Name>], e: &[(P, P)]) -> Vals {
    let vs = vars(&mut f.s, cs.len());
    let ci = conjs(f, cs);
    let ei = put_eqns(&mut f.s, e);
    prep(&mut f.s);
    let (decls, names) = (f.decls, f.names);
    let r = norm_ex(&mut f.s, decls, names, vs, ci, ei);
    f.empty_stack();
    r.map(|l| {
        let ts = get_list(&mut f.s, l);
        let ps: Vec<P> = vals_of(&ts);
        let w = put_pats(&mut f.s, &ps);
        assert!(f.s.same(l, w));
        ps
    })
}

fn pat_of(t: &T) -> P {
    let mut args = Vec::new();
    let mut h = t;
    loop {
        match h {
            T::V(v) => {
                assert!(args.is_empty(), "a variable applied");
                return pv(*v as usize);
            }
            T::S(f) => {
                args.reverse();
                return pf(*f, args);
            }
            T::A(l, r) => {
                args.push(pat_of(r));
                h = l;
            }
        }
    }
}

fn vals_of(ts: &[T]) -> Vec<P> {
    ts.iter().map(pat_of).collect()
}

/// The values written by hand are those of the reference and those of
/// `norm_ex`.
fn norm_is(cs: &[Vec<Name>], e: &[(P, P)], want: Option<&[P]>) {
    let mut f = fixture(wf());
    let want: Vals = want.map(|w| w.to_vec());
    assert_eq!(norm_ex_ref(&f.ss, cs, e), want, "the reference, {cs:?} {e:?}");
    assert_eq!(norm_ex_in(&mut f, |_| (), cs, e), want, "{cs:?} {e:?}");
}

#[test]
fn norm_ex_of_no_equation_is_the_variables() {
    norm_is(&[vec![NAT], vec![]], &[], Some(&[pv(0), pv(1)]));
}

#[test]
fn norm_ex_without_variables() {
    norm_is(&[], &[], Some(&[]));
    norm_is(&[], &[(z(), z())], Some(&[]));
    norm_is(&[], &[(z(), a())], None);
}

#[test]
fn norm_ex_is_nothing_when_symbols_differ() {
    norm_is(&[vec![]], &[(su(pv(0)), z())], None);
}

#[test]
fn norm_ex_is_nothing_when_the_numbers_of_arguments_differ() {
    norm_is(&[vec![], vec![]], &[(f1(pv(0)), f2(pv(0), pv(1)))], None);
}

#[test]
fn norm_ex_is_nothing_when_a_variable_would_hold_itself() {
    norm_is(&[vec![]], &[(pv(0), su(pv(0)))], None);
    norm_is(&[vec![], vec![]], &[(pv(0), su(pv(1))), (pv(1), pv(0))], None);
}

#[test]
fn norm_ex_binds_the_later_variable_of_an_alias() {
    norm_is(&[vec![], vec![]], &[(pv(1), pv(0))], Some(&[pv(0), pv(0)]));
}

#[test]
fn norm_ex_turns_an_alias_written_the_other_way() {
    norm_is(&[vec![], vec![]], &[(pv(0), pv(1))], Some(&[pv(0), pv(0)]));
}

#[test]
fn norm_ex_of_a_chain_of_aliases() {
    norm_is(
        &[vec![], vec![], vec![]],
        &[(pv(0), pv(1)), (pv(1), pv(2))],
        Some(&[pv(0), pv(0), pv(0)]),
    );
}

#[test]
fn norm_ex_of_an_alias_of_the_later_two() {
    norm_is(&[vec![], vec![], vec![]], &[(pv(1), pv(2))], Some(&[pv(0), pv(1), pv(1)]));
}

#[test]
fn norm_ex_of_a_value_with_an_aliased_variable() {
    norm_is(
        &[vec![], vec![], vec![]],
        &[(pv(0), f1(pv(2))), (pv(1), pv(2))],
        Some(&[f1(pv(1)), pv(1), pv(1)]),
    );
}

#[test]
fn norm_ex_of_a_value_that_names_a_turned_alias() {
    norm_is(
        &[vec![], vec![], vec![]],
        &[(pv(2), f1(pv(0))), (pv(0), pv(1))],
        Some(&[pv(0), pv(0), f1(pv(0))]),
    );
}

#[test]
fn norm_ex_of_an_equation_that_always_holds_is_the_variables() {
    norm_is(&[vec![NAT]], &[(pv(0), pv(0))], Some(&[pv(0)]));
    norm_is(&[vec![NAT]], &[(f1(pv(0)), f1(pv(0)))], Some(&[pv(0)]));
}

#[test]
fn norm_ex_takes_two_terms_apart() {
    norm_is(
        &[vec![NAT], vec![UNIT]],
        &[(f2(pv(0), z()), f2(su(pv(1)), pv(1)))],
        Some(&[su(z()), z()]),
    );
}

#[test]
fn norm_ex_of_a_value_in_the_sort_of_its_variable() {
    norm_is(&[vec![NAT]], &[(pv(0), z())], Some(&[z()]));
    norm_is(&[vec![NAT]], &[(z(), pv(0))], Some(&[z()]));
}

#[test]
fn norm_ex_is_nothing_when_the_sort_of_the_variable_rejects_its_value() {
    norm_is(&[vec![NAT]], &[(pv(0), a())], None);
    norm_is(&[vec![NAT]], &[(pv(0), su(a()))], None);
    norm_is(&[vec![BOX], vec![]], &[(pv(0), su(pv(1)))], None);
}

#[test]
fn norm_ex_of_a_variable_without_sorts_takes_any_value() {
    norm_is(&[vec![]], &[(pv(0), a())], Some(&[a()]));
}

#[test]
fn norm_ex_keeps_a_variable_whose_pushed_sort_has_many_members() {
    norm_is(&[vec![NAT], vec![]], &[(pv(0), su(pv(1)))], Some(&[su(pv(1)), pv(1)]));
}

#[test]
fn norm_ex_binds_a_variable_whose_pushed_sort_has_one_member() {
    norm_is(&[vec![TWO], vec![]], &[(pv(0), pr(pv(1), z()))], Some(&[pr(z(), z()), z()]));
}

#[test]
fn norm_ex_binds_one_variable_and_keeps_another() {
    norm_is(
        &[vec![MIX], vec![], vec![]],
        &[(pv(0), g2(pv(1), pv(2)))],
        Some(&[g2(z(), pv(2)), z(), pv(2)]),
    );
}

#[test]
fn norm_ex_takes_a_pushed_sort_with_the_own_sorts_of_the_variable() {
    norm_is(&[vec![SUC], vec![UNIT]], &[(pv(0), su(pv(1)))], Some(&[su(z()), z()]));
    norm_is(&[vec![SUC], vec![SUC]], &[(pv(0), su(pv(1)))], Some(&[su(pv(1)), pv(1)]));
    norm_is(&[vec![SUC], vec![BOX]], &[(pv(0), su(pv(1)))], None);
}

#[test]
fn norm_ex_takes_the_sorts_two_values_push_on_one_variable_together() {
    norm_is(
        &[vec![SUC], vec![MIX], vec![]],
        &[(pv(0), su(pv(2))), (pv(1), g2(pv(2), z()))],
        Some(&[su(z()), g2(z(), z()), z()]),
    );
    norm_is(
        &[vec![SUC], vec![C2], vec![]],
        &[(pv(0), su(pv(2))), (pv(1), kk(pv(2)))],
        None,
    );
}

#[test]
fn norm_ex_gives_an_alias_the_sorts_of_both_variables() {
    norm_is(&[vec![NAT], vec![SUC]], &[(pv(0), pv(1))], Some(&[pv(0), pv(0)]));
    norm_is(&[vec![UNIT], vec![NAT]], &[(pv(0), pv(1))], Some(&[z(), z()]));
    norm_is(&[vec![SUC], vec![UNIT]], &[(pv(1), pv(0))], None);
    norm_is(
        &[vec![NAT], vec![], vec![UNIT]],
        &[(pv(0), pv(1)), (pv(1), pv(2))],
        Some(&[z(), z(), z()]),
    );
}

#[test]
fn norm_ex_of_a_value_with_a_repeated_subterm() {
    let v = pr(su(pv(1)), su(pv(1)));
    norm_is(&[vec![PAIR], vec![]], &[(pv(0), v.clone())], Some(&[v, pv(1)]));
}

#[test]
fn norm_ex_binds_two_free_variables_in_one_call() {
    norm_is(
        &[vec![], vec![], vec![TWO]],
        &[(pv(2), pr(pv(0), pv(1)))],
        Some(&[z(), z(), pr(z(), z())]),
    );
}

#[test]
fn norm_ex_of_a_free_variable_whose_own_sorts_have_one_or_no_member() {
    norm_is(&[vec![UNIT]], &[], Some(&[z()]));
    norm_is(&[vec![VOID]], &[], None);
}

#[test]
fn norm_ex_of_a_sort_with_a_rest() {
    norm_is(&[vec![ANY]], &[(pv(0), a())], None);
    norm_is(&[vec![ANY]], &[(pv(0), f1(z()))], Some(&[f1(z())]));
}

#[test]
fn norm_ex_does_not_depend_on_what_the_tables_held() {
    let cs = [vec![UNIT], vec![NAT]];
    let e = [(pv(0), pv(1))];
    let mut f = fixture(wf());
    let got = norm_ex_in(
        &mut f,
        |s| {
            let v0 = put_var(s, 0);
            let v1 = put_var(s, 1);
            let zi = s.alloc(Node::Sym(Z));
            s.set(Tbl::A, v0, zi);
            s.set(Tbl::A, v1, zi);
            s.set(Tbl::B, v0, v1);
            s.set(Tbl::B, v1, zi);
        },
        &cs,
        &e,
    );
    assert_eq!(got, Some(vec![z(), z()]));
}

/// Every pattern over three symbols and two variables up to a depth.
fn pats(depth: u32) -> Vec<P> {
    let mut out = vec![z(), a(), pv(0), pv(1)];
    if depth > 0 {
        let sub = pats(depth - 1);
        for l in &sub {
            out.push(su(l.clone()));
        }
        for l in &sub {
            for r in &sub {
                out.push(pr(l.clone(), r.clone()));
            }
        }
    }
    out
}

#[test]
fn norm_ex_is_the_reference_on_every_small_equation() {
    let mut f = fixture(wf());
    let sorts: Vec<[Vec<Name>; 2]> = vec![
        [vec![], vec![]],
        [vec![NAT], vec![]],
        [vec![NAT], vec![UNIT]],
        [vec![SUC], vec![NAT]],
        [vec![PAIR], vec![NAT]],
        [vec![TWO], vec![ANY]],
        [vec![ANY], vec![SUC, NAT]],
    ];
    let ps = pats(1);
    for l in &ps {
        for r in &ps {
            let e = [(l.clone(), r.clone())];
            for cs in &sorts {
                let want = norm_ex_ref(&f.ss, cs, &e);
                let got = norm_ex_in(&mut f, |_| (), cs, &e);
                assert_eq!(got, want, "{cs:?} {e:?}");
            }
        }
    }
}
