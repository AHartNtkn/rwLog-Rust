//! Numbering the variables of a store by first occurrence
//! (`sorts::renumber`), with what it is made of: a term rebuilt through a
//! table of variables (`Leaf::Map`), the variables of a term in the order
//! they first occur (`sorts::firsts`), the conjunction of a variable among
//! the entries (`sorts::conj_at`), and every declared sort that holds of all
//! members of a conjunction but some ground terms (`sorts::uppers`); against
//! `firsts` (`lean/RwLog/Sorts/Renum.lean`) and `ofTight`
//! (`lean/RwLog/Sorts/Norm.lean`) of the specification.

mod common;

use common::sorts::*;
use common::{put_var, T};
use rwlog_core::sorts::{conj_at, firsts, renumber, uppers};
use rwlog_core::store::{Node, Store, Tbl, TermId};
use rwlog_core::term::{rebuild, Leaf};

// Symbols.
const Z: u32 = 0;
const SU: u32 = 1;
const PR: u32 = 2;
const F: u32 = 3;
const G: u32 = 4;
const H: u32 = 5;
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

const ALL: [Name; 11] = [UNIT, NAT, VOID, TWO, BOX, PAIR, MIX, C2, C3, SUC, ANY];

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
fn g1(p: P) -> P {
    pf(G, vec![p])
}
fn g2(p: P, q: P) -> P {
    pf(G, vec![p, q])
}
fn h2(p: P, q: P) -> P {
    pf(H, vec![p, q])
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

fn var(s: &mut Store, n: usize) -> TermId {
    put_var(s, n as u128)
}

fn empty_stack(s: &mut Store) {
    assert!(s.pop().is_none(), "the stack is not empty");
}

// A term rebuilt through a table of variables.

/// The pattern `p` rebuilt with each variable of `map` replaced by its
/// pattern there is the pattern `want`.
fn map_is(map: &[(usize, P)], p: P, want: P) {
    let mut s = Store::new();
    let pi = put_pat(&mut s, &p);
    let wi = put_pat(&mut s, &want);
    s.clear(Tbl::A);
    s.clear(Tbl::B);
    for (v, u) in map {
        let vi = var(&mut s, *v);
        let ui = put_pat(&mut s, u);
        s.set(Tbl::B, vi, ui);
    }
    let r = rebuild(&mut s, Leaf::Map, pi);
    empty_stack(&mut s);
    assert!(s.same(r, wi), "{map:?} on {p:?}");
}

#[test]
fn map_variable_without_entry_stays() {
    map_is(&[], f2(pv(3), z()), f2(pv(3), z()));
}

#[test]
fn map_replaces_all_variables_at_once() {
    map_is(&[(0, pv(1)), (1, pv(0))], f2(pv(0), pv(1)), f2(pv(1), pv(0)));
}

#[test]
fn map_does_not_look_inside_the_node_of_a_variable() {
    map_is(&[(0, z())], pv(1), pv(1));
    map_is(&[(0, z())], pv(2), pv(2));
    map_is(&[(1, z())], pv(3), pv(3));
}

#[test]
fn map_does_not_replace_inside_what_it_put() {
    map_is(&[(0, g1(pv(0)))], f1(pv(0)), f1(g1(pv(0))));
}

#[test]
fn map_to_the_first_variable() {
    map_is(&[(5, pv(0))], f1(pv(5)), f1(pv(0)));
}

#[test]
fn map_of_a_repeated_subterm() {
    let p = f2(g2(pv(3), pv(5)), g2(pv(3), pv(5)));
    let w = f2(g2(pv(0), pv(1)), g2(pv(0), pv(1)));
    map_is(&[(3, pv(0)), (5, pv(1))], p, w);
}

#[test]
fn map_of_a_term_without_variables_is_the_term() {
    map_is(&[(0, pv(1))], pr(z(), z()), pr(z(), z()));
}

#[test]
fn map_of_a_bare_variable() {
    map_is(&[(4, su(z()))], pv(4), su(z()));
}

// The variables of a term in the order they first occur.

fn firsts_of(prep: impl FnOnce(&mut Store, TermId), p: &P) -> Vec<T> {
    let mut s = Store::new();
    let pi = put_pat(&mut s, p);
    prep(&mut s, pi);
    let r = firsts(&mut s, pi);
    empty_stack(&mut s);
    common::get_list(&mut s, r)
}

fn firsts_is(p: P, want: &[usize]) {
    let w: Vec<T> = want.iter().map(|n| T::V(*n as u128)).collect();
    assert_eq!(firsts_of(|_, _| (), &p), w, "{p:?}");
}

#[test]
fn firsts_of_a_term_without_variables_is_empty() {
    firsts_is(z(), &[]);
    firsts_is(pr(z(), z()), &[]);
}

#[test]
fn firsts_of_a_bare_variable() {
    firsts_is(pv(5), &[5]);
    firsts_is(pv(0), &[0]);
}

#[test]
fn firsts_lists_a_repeated_variable_once() {
    firsts_is(f2(pv(0), pv(0)), &[0]);
    firsts_is(pr(pv(2), pr(pv(1), pv(2))), &[2, 1]);
}

#[test]
fn firsts_goes_left_to_right() {
    firsts_is(f2(pv(1), pv(0)), &[1, 0]);
    firsts_is(pr(pv(1), pr(pv(2), pv(0))), &[1, 2, 0]);
    firsts_is(pr(pr(pv(3), pv(1)), pv(2)), &[3, 1, 2]);
}

#[test]
fn firsts_does_not_list_the_variables_inside_the_node_of_a_variable() {
    firsts_is(f1(pv(1)), &[1]);
    firsts_is(f2(pv(2), pv(1)), &[2, 1]);
    firsts_is(f1(pv(6)), &[6]);
}

#[test]
fn firsts_of_a_repeated_subterm() {
    firsts_is(f2(g2(pv(3), pv(5)), g2(pv(3), pv(5))), &[3, 5]);
    firsts_is(h2(g1(pv(7)), pr(pv(2), g1(pv(7)))), &[7, 2]);
}

#[test]
fn firsts_of_a_variable_met_again_after_a_repeated_subterm() {
    firsts_is(pr(g1(pv(4)), pr(pv(1), pr(g1(pv(4)), pv(4)))), &[4, 1]);
}

#[test]
fn firsts_keeps_numbers_that_are_far_apart() {
    firsts_is(f2(pv(9), pv(4)), &[9, 4]);
    firsts_is(f2(pv(1000), pv(0)), &[1000, 0]);
}

#[test]
fn firsts_does_not_depend_on_what_the_table_held() {
    let p = f1(pv(0));
    let got = firsts_of(
        |s, pi| {
            let v0 = var(s, 0);
            s.set_flag(Tbl::B, v0, true);
            s.set_flag(Tbl::B, pi, true);
        },
        &p,
    );
    assert_eq!(got, vec![T::V(0)]);
}

#[test]
fn firsts_of_a_deep_term_does_not_use_the_call_stack() {
    let mut s = Store::new();
    let mut pi = var(&mut s, 1);
    let su_ = s.alloc(Node::Sym(SU));
    for _ in 0..100_000 {
        pi = s.alloc(Node::App(su_, pi));
    }
    let r = firsts(&mut s, pi);
    assert_eq!(common::get_list(&mut s, r), vec![T::V(1)]);
}

// The conjunction of a variable among the entries.

fn conj_at_is(es: &[(usize, Vec<Name>)], v: usize, want: &[Name]) {
    let mut f = fixture(wf());
    let ei = f.entries(es);
    let vi = var(&mut f.s, v);
    let w = f.conj(want);
    let r = conj_at(&mut f.s, ei, vi);
    f.empty_stack();
    assert!(f.s.same(r, w), "{es:?} at {v}");
}

#[test]
fn conj_at_among_no_entries_is_empty() {
    conj_at_is(&[], 0, &[]);
}

#[test]
fn conj_at_finds_the_entry_wherever_it_is() {
    let es = [(4, vec![PAIR]), (9, vec![NAT]), (2, vec![BOX, ANY])];
    conj_at_is(&es, 4, &[PAIR]);
    conj_at_is(&es, 9, &[NAT]);
    conj_at_is(&es, 2, &[BOX, ANY]);
}

#[test]
fn conj_at_of_a_variable_without_entry_is_empty() {
    conj_at_is(&[(4, vec![PAIR]), (9, vec![NAT])], 0, &[]);
    conj_at_is(&[(4, vec![PAIR]), (9, vec![NAT])], 5, &[]);
}

#[test]
fn conj_at_does_not_take_a_variable_for_one_inside_its_node() {
    conj_at_is(&[(1, vec![NAT])], 0, &[]);
    conj_at_is(&[(0, vec![NAT])], 1, &[]);
    conj_at_is(&[(2, vec![NAT])], 1, &[]);
}

// Every declared sort that holds of all members of a conjunction but some
// ground terms.

/// The answer written by hand is that of the reference and that of
/// `uppers`.
fn uppers_is(c: &[Name], g: &[P], want: &[Name]) {
    let mut f = fixture(wf());
    let cs: Conj = c.iter().copied().collect();
    let by_ref: Vec<Name> =
        ALL.iter().copied().filter(|n| f.ss.included_but(&cs, *n, g)).collect();
    assert_eq!(by_ref, want, "the reference, {c:?} but {g:?}");
    let ci = f.conj(c);
    let gi = put_pats(&mut f.s, g);
    let w = f.conj(want);
    let (decls, names) = (f.decls, f.names);
    let r = uppers(&mut f.s, decls, names, ci, gi);
    f.empty_stack();
    assert!(f.s.same(r, w), "{c:?} but {g:?}: {:?}", get_names(&mut f.s, r));
}

#[test]
fn uppers_of_no_sort_is_no_sort() {
    uppers_is(&[], &[], &[]);
}

#[test]
fn uppers_of_no_sort_but_the_one_term_a_sort_lacks() {
    uppers_is(&[], &[a()], &[ANY]);
}

#[test]
fn uppers_of_no_sort_but_another_term_is_no_sort() {
    uppers_is(&[], &[z()], &[]);
}

#[test]
fn uppers_adds_the_sorts_that_hold_more() {
    uppers_is(&[NAT], &[], &[NAT, ANY]);
    uppers_is(&[SUC], &[], &[NAT, SUC, ANY]);
    uppers_is(&[BOX], &[], &[BOX, ANY]);
    uppers_is(&[C2], &[], &[C2, ANY]);
    uppers_is(&[PAIR], &[], &[PAIR, ANY]);
    uppers_is(&[ANY], &[], &[ANY]);
}

#[test]
fn uppers_without_a_term_adds_the_sorts_that_only_lacked_it() {
    uppers_is(&[NAT], &[z()], &[NAT, SUC, ANY]);
}

#[test]
fn uppers_without_a_term_that_was_no_exception_adds_nothing() {
    uppers_is(&[NAT], &[su(z())], &[NAT, ANY]);
    uppers_is(&[NAT], &[a()], &[NAT, ANY]);
}

#[test]
fn uppers_without_more_terms_than_needed() {
    uppers_is(&[NAT], &[z(), su(z())], &[NAT, SUC, ANY]);
}

#[test]
fn uppers_of_a_sort_with_one_member() {
    uppers_is(&[UNIT], &[], &[UNIT, NAT, ANY]);
    uppers_is(&[TWO], &[], &[TWO, PAIR, ANY]);
}

#[test]
fn uppers_of_a_conjunction_without_members_is_every_sort() {
    uppers_is(&[VOID], &[], &ALL);
    uppers_is(&[BOX, C2], &[], &ALL);
}

#[test]
fn uppers_without_the_only_member_is_every_sort() {
    uppers_is(&[UNIT], &[z()], &ALL);
}

#[test]
fn uppers_of_a_conjunction_that_says_a_sort_twice_over() {
    uppers_is(&[NAT, ANY], &[], &[NAT, ANY]);
    uppers_is(&[NAT, SUC], &[], &[NAT, SUC, ANY]);
}

#[test]
fn uppers_of_its_own_answer_is_that_answer() {
    uppers_is(&[NAT, SUC, ANY], &[], &[NAT, SUC, ANY]);
    uppers_is(&[UNIT, NAT, ANY], &[], &[UNIT, NAT, ANY]);
}

// Numbering a store.

type Out = (P, Excls, Vec<Vec<Name>>);

fn renumber_in(
    f: &mut Fx,
    prep: impl FnOnce(&mut Store, TermId),
    t: &P,
    x: &Excls,
    es: &Entries,
) -> (TermId, TermId, TermId) {
    let ti = put_pat(&mut f.s, t);
    let xi = put_excls(&mut f.s, x);
    let ei = f.entries(es);
    prep(&mut f.s, ti);
    let (decls, names) = (f.decls, f.names);
    let r = renumber(&mut f.s, decls, names, ti, xi, ei);
    f.empty_stack();
    r
}

/// `ofTight` of the specification before its exclusions are put in normal
/// form: the pattern and the exclusions with each variable replaced by its
/// place among the first occurrences, and for each variable in that order
/// the declared sorts that hold of all its values.
fn renumber_ref(ss: &Sorts, t: &P, x: &Excls, es: &Entries) -> Out {
    let mut vs = Vec::new();
    t.vars(&mut vs);
    let ren: std::collections::BTreeMap<usize, P> =
        vs.iter().enumerate().map(|(i, v)| (*v, pv(i))).collect();
    let cs = vs
        .iter()
        .map(|v| {
            let c: Conj = es
                .iter()
                .filter(|(u, _)| u == v)
                .flat_map(|(_, c)| c.iter().copied())
                .collect();
            let g = gone(x, *v);
            ALL.iter().copied().filter(|n| ss.included_but(&c, *n, &g)).collect()
        })
        .collect();
    let x1 = x
        .iter()
        .map(|e| e.iter().map(|(l, r)| (l.subst(&ren), r.subst(&ren))).collect())
        .collect();
    (t.subst(&ren), x1, cs)
}

/// The store written by hand is that of the reference and that of
/// `renumber`.
fn renumber_is(t: P, x: Excls, es: Entries, want: Out) {
    let mut f = fixture(wf());
    assert_eq!(renumber_ref(&f.ss, &t, &x, &es), want, "the reference");
    let (t1, x1, cs) = renumber_in(&mut f, |_, _| (), &t, &x, &es);
    let wt = put_pat(&mut f.s, &want.0);
    let wx = put_excls(&mut f.s, &want.1);
    assert!(f.s.same(t1, wt), "the pattern");
    assert!(f.s.same(x1, wx), "the exclusions");
    let wcs: Vec<TermId> = want.2.iter().map(|c| f.conj(c)).collect();
    let mut p = cs;
    for (i, w) in wcs.iter().enumerate() {
        match f.s.read(p) {
            Node::App(h, rest) => {
                assert!(f.s.same(h, *w), "the sorts of variable {i}: {:?}", get_names(&mut f.s, h));
                p = rest;
            }
            _ => panic!("fewer conjunctions than variables"),
        }
    }
    assert!(matches!(f.s.read(p), Node::Nil), "more conjunctions than variables");
}

#[test]
fn renumber_of_a_store_without_variables() {
    renumber_is(z(), vec![], vec![], (z(), vec![], vec![]));
}

#[test]
fn renumber_of_a_numbered_store_gives_its_nodes() {
    let t = f2(pv(0), pv(1));
    let x = vec![vec![(pv(1), z())]];
    let es = vec![(0, vec![BOX]), (1, vec![NAT])];
    let mut f = fixture(wf());
    let ti = put_pat(&mut f.s, &t);
    let xi = put_excls(&mut f.s, &x);
    let (t1, x1, _) = renumber_in(&mut f, |_, _| (), &t, &x, &es);
    assert!(f.s.same(t1, ti));
    assert!(f.s.same(x1, xi));
    renumber_is(t.clone(), x.clone(), es, (t, x, vec![vec![BOX, ANY], vec![NAT, SUC, ANY]]));
}

#[test]
fn renumber_exchanges_two_variables() {
    renumber_is(
        f2(pv(1), pv(0)),
        vec![vec![(pv(0), z())], vec![(pv(1), pv(0))]],
        vec![(0, vec![NAT]), (1, vec![BOX])],
        (
            f2(pv(0), pv(1)),
            vec![vec![(pv(1), z())], vec![(pv(0), pv(1))]],
            vec![vec![BOX, ANY], vec![NAT, SUC, ANY]],
        ),
    );
}

#[test]
fn renumber_turns_three_variables_round() {
    renumber_is(
        pr(pv(1), pr(pv(2), pv(0))),
        vec![vec![(pv(0), pv(1))], vec![(pv(2), su(pv(0)))]],
        vec![],
        (
            pr(pv(0), pr(pv(1), pv(2))),
            vec![vec![(pv(2), pv(0))], vec![(pv(1), su(pv(2)))]],
            vec![vec![], vec![], vec![]],
        ),
    );
}

#[test]
fn renumber_closes_the_gaps_and_finds_entries_in_any_order() {
    renumber_is(
        f2(pv(9), pv(4)),
        vec![vec![(pv(9), z())]],
        vec![(4, vec![PAIR]), (9, vec![NAT])],
        (f2(pv(0), pv(1)), vec![vec![(pv(0), z())]], vec![vec![NAT, SUC, ANY], vec![PAIR, ANY]]),
    );
}

#[test]
fn renumber_of_variables_whose_nodes_hold_other_variables() {
    renumber_is(f2(pv(2), pv(1)), vec![], vec![], (f2(pv(0), pv(1)), vec![], vec![vec![], vec![]]));
    renumber_is(f1(pv(1)), vec![], vec![], (f1(pv(0)), vec![], vec![vec![]]));
    renumber_is(f1(pv(3)), vec![], vec![], (f1(pv(0)), vec![], vec![vec![]]));
}

#[test]
fn renumber_of_a_repeated_subterm() {
    renumber_is(
        f2(g2(pv(3), pv(5)), g2(pv(3), pv(5))),
        vec![],
        vec![(5, vec![SUC])],
        (f2(g2(pv(0), pv(1)), g2(pv(0), pv(1))), vec![], vec![vec![], vec![NAT, SUC, ANY]]),
    );
}

#[test]
fn renumber_gives_a_variable_without_sorts_the_sort_its_exclusion_leaves() {
    renumber_is(pv(0), vec![vec![(pv(0), a())]], vec![], (pv(0), vec![vec![(pv(0), a())]], vec![vec![ANY]]));
    renumber_is(pv(0), vec![], vec![], (pv(0), vec![], vec![vec![]]));
}

#[test]
fn renumber_adds_no_sort_for_an_exclusion_of_two_variables() {
    let t = pr(pv(0), pv(1));
    let es = vec![(0, vec![NAT]), (1, vec![NAT])];
    let cs = vec![vec![NAT, ANY], vec![NAT, ANY]];
    let x = vec![vec![(pv(0), z()), (pv(1), z())]];
    renumber_is(t.clone(), x.clone(), es.clone(), (t.clone(), x, cs.clone()));
    let x = vec![vec![(pr(pv(0), pv(1)), pr(z(), z()))]];
    renumber_is(t.clone(), x.clone(), es, (t, x, cs));
}

#[test]
fn renumber_reads_the_exclusions_by_the_old_numbers() {
    renumber_is(
        f2(pv(1), pv(0)),
        vec![vec![(pv(1), z())]],
        vec![(1, vec![NAT])],
        (f2(pv(0), pv(1)), vec![vec![(pv(0), z())]], vec![vec![NAT, SUC, ANY], vec![]]),
    );
}

#[test]
fn renumber_twice_gives_the_same_nodes() {
    let t = f2(pv(1), pv(0));
    let x = vec![vec![(pv(0), z())], vec![(pv(1), pv(0))]];
    let es = vec![(0, vec![NAT]), (1, vec![BOX])];
    let mut f = fixture(wf());
    let (t1, x1, cs1) = renumber_in(&mut f, |_, _| (), &t, &x, &es);
    let ei = f.entries(&[(0, vec![BOX]), (1, vec![NAT])]);
    let (decls, names) = (f.decls, f.names);
    let (t2, x2, cs2) = renumber(&mut f.s, decls, names, t1, x1, ei);
    f.empty_stack();
    assert!(f.s.same(t1, t2));
    assert!(f.s.same(x1, x2));
    assert!(f.s.same(cs1, cs2));
}

#[test]
fn renumber_does_not_depend_on_the_order_of_the_entries() {
    let t = f2(pv(1), pv(0));
    let x = vec![vec![(pv(0), z())], vec![(pv(1), pv(0))]];
    let mut f = fixture(wf());
    let (t1, x1, cs1) =
        renumber_in(&mut f, |_, _| (), &t, &x, &vec![(0, vec![NAT]), (1, vec![BOX])]);
    let (t2, x2, cs2) =
        renumber_in(&mut f, |_, _| (), &t, &x, &vec![(1, vec![BOX]), (0, vec![NAT])]);
    assert!(f.s.same(t1, t2));
    assert!(f.s.same(x1, x2));
    assert!(f.s.same(cs1, cs2));
}

#[test]
fn renumber_does_not_depend_on_what_the_tables_held() {
    let t = f2(pv(1), pv(0));
    let x = vec![vec![(pv(0), z())], vec![(pv(1), pv(0))]];
    let es = vec![(0, vec![NAT]), (1, vec![BOX])];
    let mut f = fixture(wf());
    let (t1, x1, cs1) = renumber_in(&mut f, |_, _| (), &t, &x, &es);
    let (t2, x2, cs2) = renumber_in(
        &mut f,
        |s, ti| {
            let zi = s.alloc(Node::Sym(Z));
            let v0 = var(s, 0);
            let v1 = var(s, 1);
            s.set(Tbl::A, ti, zi);
            s.set(Tbl::B, v1, zi);
            s.set_flag(Tbl::B, v0, true);
        },
        &t,
        &x,
        &es,
    );
    assert!(f.s.same(t1, t2));
    assert!(f.s.same(x1, x2));
    assert!(f.s.same(cs1, cs2));
}

/// Every pattern over two symbols and three variables up to a depth.
fn pats(depth: u32) -> Vec<P> {
    let mut out = vec![z(), pv(0), pv(1), pv(2)];
    if depth > 0 {
        let sub = pats(depth - 1);
        for l in &sub {
            out.push(su(l.clone()));
            for r in &sub {
                out.push(pr(l.clone(), r.clone()));
            }
        }
    }
    out
}

#[test]
fn renumber_is_the_reference_on_every_small_store() {
    let mut f = fixture(wf());
    let excls: Vec<Excls> = vec![
        vec![],
        vec![vec![(pv(0), z())]],
        vec![vec![(pv(1), z())], vec![(pv(2), su(z()))]],
        vec![vec![(pv(0), pv(1))], vec![(pv(2), z()), (pv(1), z())]],
    ];
    let entries: Vec<Entries> = vec![
        vec![],
        vec![(0, vec![NAT]), (1, vec![SUC]), (2, vec![UNIT])],
        vec![(2, vec![NAT]), (0, vec![PAIR])],
    ];
    for t in pats(1) {
        let mut vs = Vec::new();
        t.vars(&mut vs);
        for x in &excls {
            let x: Excls = x
                .iter()
                .filter(|e| {
                    e.iter().all(|(l, r)| {
                        let mut ws = Vec::new();
                        l.vars(&mut ws);
                        r.vars(&mut ws);
                        ws.iter().all(|w| vs.contains(w))
                    })
                })
                .cloned()
                .collect();
            for es in &entries {
                let es: Entries = es.iter().filter(|(v, _)| vs.contains(v)).cloned().collect();
                let want = renumber_ref(&f.ss, &t, &x, &es);
                let (t1, x1, cs) = renumber_in(&mut f, |_, _| (), &t, &x, &es);
                let wt = put_pat(&mut f.s, &want.0);
                let wx = put_excls(&mut f.s, &want.1);
                assert!(f.s.same(t1, wt), "the pattern of {t:?} {x:?} {es:?}");
                assert!(f.s.same(x1, wx), "the exclusions of {t:?} {x:?} {es:?}");
                let got: Vec<Conj> =
                    get_conjs(&mut f.s, cs).into_iter().map(|c| c.into_iter().collect()).collect();
                let wcs: Vec<Conj> = want.2.iter().map(|c| c.iter().copied().collect()).collect();
                assert_eq!(got, wcs, "the sorts of {t:?} {x:?} {es:?}");
            }
        }
    }
}
