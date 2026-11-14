//! The operations of the sorts as a constraint domain (`dom`), against
//! `Rep.one`, `Rep.compose`, `Rep.meet`, `Rep.right`, `Rep.conv` and the
//! `isBound` and `covers` of `dom` in the specification
//! (`lean/RwLog/Sorts/Dom.lean`) as written on trees: each states a problem
//! and takes its normal store (`common::sorts::normal`).
//!
//! A relation is written here as a problem whose pattern is the pair of its
//! two sides; its representative is the normal store of that problem. In
//! the reference the pair is the symbol `PSYM` applied to the two sides;
//! in the store it is `Nil` applied to them.

mod common;

use common::decls::*;
use common::sorts::*;
use common::{ap, get, get_list, v, T};
use rwlog_core::dom::{self, Rep};
use rwlog_core::store::{Node, Tbl, TermId};

/// The pair of the reference.
const PSYM: u32 = 99;

fn pair(l: P, r: P) -> P {
    pf(PSYM, vec![l, r])
}

/// The relation of the sides `l` and `r` under the sorts `a` of patterns
/// and the exclusions `x`.
fn rel(l: P, r: P, a: Vec<(Name, P)>, x: Excls) -> Prob {
    Prob { t: pair(l, r), e: vec![], a, x }
}

/// The relation of the sides `l` and `r` with nothing said of the variables.
fn plain(l: P, r: P) -> Prob {
    rel(l, r, vec![], vec![])
}

fn sides(r: &Raw) -> (P, P) {
    match &r.t {
        P::F(f, args) if *f == PSYM && args.len() == 2 => (args[0].clone(), args[1].clone()),
        _ => panic!("the pattern of a representative is not a pair"),
    }
}

fn shift(p: &P, k: usize) -> P {
    match p {
        P::V(x) => pv(x + k),
        P::F(f, args) => pf(*f, args.iter().map(|q| shift(q, k)).collect()),
    }
}

/// `Rep.one`: the pair of `u` and `w` over the solutions of `r`.
fn ref_one(ss: &Sorts, r: &Raw, u: &P, w: &P) -> Option<Raw> {
    normal(ss, &Prob { t: pair(u.clone(), w.clone()), ..r.prob() })
}

/// `Rep.two`: the pair of `u` and `w` and the equations `e` over the
/// solutions of `a` and, its variables moved above those of `a`, of `b`.
fn ref_two(ss: &Sorts, a: &Raw, b: &Raw, u: &P, w: &P, e: Vec<(P, P)>) -> Option<Raw> {
    let k = a.c.len();
    let (pa, pb) = (a.prob(), b.prob());
    let mut at = pa.a;
    at.extend(pb.a.iter().map(|(n, p)| (*n, shift(p, k))));
    let mut x = pa.x;
    x.extend(pb.x.iter().map(|e| e.iter().map(|(l, r)| (shift(l, k), shift(r, k))).collect::<Vec<_>>()));
    normal(ss, &Prob { t: pair(u.clone(), w.clone()), e, a: at, x })
}

fn ref_compose(ss: &Sorts, a: &Raw, b: &Raw) -> Option<Raw> {
    let k = a.c.len();
    let ((al, ar), (bl, br)) = (sides(a), sides(b));
    ref_two(ss, a, b, &al, &shift(&br, k), vec![(ar, shift(&bl, k))])
}

fn ref_meet(ss: &Sorts, a: &Raw, b: &Raw) -> Option<Raw> {
    let k = a.c.len();
    let ((al, ar), (bl, br)) = (sides(a), sides(b));
    ref_two(ss, a, b, &al, &ar, vec![(al.clone(), shift(&bl, k)), (ar.clone(), shift(&br, k))])
}

fn ref_right(ss: &Sorts, a: &Raw) -> Option<Raw> {
    let (_, r) = sides(a);
    ref_one(ss, a, &r, &r)
}

fn ref_conv(ss: &Sorts, a: &Raw) -> Raw {
    let (l, r) = sides(a);
    ref_one(ss, a, &r, &l).unwrap_or_else(|| a.clone())
}

/// The representative of a relation; it relates something.
fn rep(defs: &[(Name, Def)], p: &Prob) -> Raw {
    normal(&Sorts::new(defs.to_vec()), p).unwrap_or_else(|| panic!("{p:?} relates nothing"))
}

/// The value each variable of a store of `k` variables has in the solved
/// exclusion `b`.
fn values(k: usize, b: &Binds) -> Vec<P> {
    (0..k).map(|i| b.iter().find(|(y, _)| *y == i).map_or(pv(i), |(_, q)| q.clone())).collect()
}

/// A representative in the store, its exclusions in the order given or in
/// the opposite order.
fn put_rep(f: &mut Fx, r: &Raw, backwards: bool) -> Rep {
    let (l, rt) = sides(r);
    let l = put_pat(&mut f.s, &l);
    let rt = put_pat(&mut f.s, &rt);
    let nil = f.s.alloc(Node::Nil);
    let h = f.s.alloc(Node::App(nil, l));
    let t = f.s.alloc(Node::App(h, rt));
    let mut c = f.s.alloc(Node::Nil);
    for cj in r.c.iter().rev() {
        let names: Vec<Name> = cj.iter().copied().collect();
        let h = f.conj(&names);
        c = f.s.alloc(Node::App(h, c));
    }
    let mut xs: Vec<&Binds> = r.x.iter().collect();
    if !backwards {
        xs.reverse();
    }
    let mut x = f.s.alloc(Node::Nil);
    for b in xs {
        let h = put_pats(&mut f.s, &values(r.c.len(), b));
        x = f.s.alloc(Node::App(h, x));
    }
    Rep { t, c, x }
}

/// A representative read back: its two sides, the conjunction of each
/// variable as a sorted list, and the exclusions, each the list of the
/// values of the variables, as a sorted list of their printed forms.
type Shape = (T, T, Vec<Vec<Name>>, Vec<String>);

fn sorted<X: Ord>(mut l: Vec<X>) -> Vec<X> {
    l.sort();
    l
}

fn shape(r: &Raw) -> Shape {
    let (l, rt) = sides(r);
    let x = r
        .x
        .iter()
        .map(|b| {
            let vals: Vec<T> = values(r.c.len(), b).iter().map(P::tree).collect();
            format!("{vals:?}")
        })
        .collect();
    (l.tree(), rt.tree(), r.c.iter().map(|c| c.iter().copied().collect()).collect(), sorted(x))
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

fn get_rep(f: &mut Fx, r: Rep) -> Shape {
    let (h, rt) = match f.s.read(r.t) {
        Node::App(h, rt) => (h, rt),
        _ => panic!("the pattern is not a pair"),
    };
    let l = match f.s.read(h) {
        Node::App(nil, l) => {
            assert!(matches!(f.s.read(nil), Node::Nil), "the pair has another head");
            l
        }
        _ => panic!("the pattern is not a pair"),
    };
    let l = get(&mut f.s, l);
    let rt = get(&mut f.s, rt);
    let cs = get_conjs(&mut f.s, r.c).into_iter().map(sorted).collect();
    let xs = get_lists(f, r.x).iter().map(|l| format!("{l:?}")).collect();
    (l, rt, cs, sorted(xs))
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

/// How an operation is run: with the exclusions of its arguments in the
/// opposite order, and with the tables left dirty by earlier work.
#[derive(Clone, Copy)]
struct Run {
    backwards: bool,
    soiled: bool,
}

const RUNS: [Run; 3] = [
    Run { backwards: false, soiled: false },
    Run { backwards: true, soiled: false },
    Run { backwards: false, soiled: true },
];

/// Run an operation of one representative in the store.
fn run1<R>(defs: &[(Name, Def)], a: &Raw, run: Run, op: impl FnOnce(&mut Fx, Rep) -> R) -> (R, Fx) {
    let mut f = fixture(defs.to_vec());
    let ra = put_rep(&mut f, a, run.backwards);
    if run.soiled {
        dirty(&mut f);
    }
    let got = op(&mut f, ra);
    f.empty_stack();
    (got, f)
}

/// Run an operation of two representatives in the store.
fn run2<R>(
    defs: &[(Name, Def)],
    a: &Raw,
    b: &Raw,
    run: Run,
    op: impl FnOnce(&mut Fx, Rep, Rep) -> R,
) -> (R, Fx) {
    let mut f = fixture(defs.to_vec());
    let ra = put_rep(&mut f, a, run.backwards);
    let rb = put_rep(&mut f, b, run.backwards);
    if run.soiled {
        dirty(&mut f);
    }
    let got = op(&mut f, ra, rb);
    f.empty_stack();
    (got, f)
}

fn read(got: Option<Rep>, mut f: Fx) -> Option<Shape> {
    got.map(|r| get_rep(&mut f, r))
}

/// `dom::one` on the representative of `p` gives the representative of
/// the reference, and there is one.
fn one_same(defs: Vec<(Name, Def)>, p: &Prob, u: &P, w: &P) -> Raw {
    let a = rep(&defs, p);
    let want = ref_one(&Sorts::new(defs.clone()), &a, u, w).unwrap_or_else(|| panic!("the reference has nothing for {p:?}"));
    for run in RUNS {
        let (got, f) = run1(&defs, &a, run, |f, ra| {
            let u = put_pat(&mut f.s, u);
            let w = put_pat(&mut f.s, w);
            dom::one(&mut f.s, f.decls, f.names, ra, u, w)
        });
        assert_eq!(read(got, f), Some(shape(&want)), "{p:?} with {u:?} and {w:?}");
    }
    want
}

/// `dom::compose` gives the representative of the reference, and there is
/// one. Returned is that of the reference.
fn compose_same(defs: Vec<(Name, Def)>, p: &Prob, q: &Prob) -> Raw {
    let (a, b) = (rep(&defs, p), rep(&defs, q));
    let want = ref_compose(&Sorts::new(defs.clone()), &a, &b).unwrap_or_else(|| panic!("the reference composes {p:?} and {q:?} to nothing"));
    for run in RUNS {
        let (got, f) = run2(&defs, &a, &b, run, |f, ra, rb| dom::compose(&mut f.s, f.decls, f.names, ra, rb));
        assert_eq!(read(got, f), Some(shape(&want)), "{p:?} then {q:?}");
    }
    want
}

/// Neither `dom::compose` nor the reference has a representative.
fn compose_none(defs: Vec<(Name, Def)>, p: &Prob, q: &Prob) {
    let (a, b) = (rep(&defs, p), rep(&defs, q));
    assert!(ref_compose(&Sorts::new(defs.clone()), &a, &b).is_none(), "the reference composes {p:?} and {q:?}");
    for run in RUNS {
        let (got, f) = run2(&defs, &a, &b, run, |f, ra, rb| dom::compose(&mut f.s, f.decls, f.names, ra, rb));
        assert_eq!(read(got, f), None, "{p:?} then {q:?}");
    }
}

/// `dom::meet` gives the representative of the reference, and there is
/// one. Returned is that of the reference.
fn meet_same(defs: Vec<(Name, Def)>, p: &Prob, q: &Prob) -> Raw {
    let (a, b) = (rep(&defs, p), rep(&defs, q));
    let want = ref_meet(&Sorts::new(defs.clone()), &a, &b).unwrap_or_else(|| panic!("the reference meets {p:?} and {q:?} in nothing"));
    for run in RUNS {
        let (got, f) = run2(&defs, &a, &b, run, |f, ra, rb| dom::meet(&mut f.s, f.decls, f.names, ra, rb));
        assert_eq!(read(got, f), Some(shape(&want)), "{p:?} and {q:?}");
    }
    want
}

/// Neither `dom::meet` nor the reference has a representative.
fn meet_none(defs: Vec<(Name, Def)>, p: &Prob, q: &Prob) {
    let (a, b) = (rep(&defs, p), rep(&defs, q));
    assert!(ref_meet(&Sorts::new(defs.clone()), &a, &b).is_none(), "the reference meets {p:?} and {q:?}");
    for run in RUNS {
        let (got, f) = run2(&defs, &a, &b, run, |f, ra, rb| dom::meet(&mut f.s, f.decls, f.names, ra, rb));
        assert_eq!(read(got, f), None, "{p:?} and {q:?}");
    }
}

/// `dom::right` gives the representative of the reference, and there is
/// one. Returned is that of the reference.
fn right_same(defs: Vec<(Name, Def)>, p: &Prob) -> Raw {
    let a = rep(&defs, p);
    let want = ref_right(&Sorts::new(defs.clone()), &a).unwrap_or_else(|| panic!("the reference has no right interface of {p:?}"));
    for run in RUNS {
        let (got, f) = run1(&defs, &a, run, |f, ra| dom::right(&mut f.s, f.decls, f.names, ra));
        assert_eq!(read(got, f), Some(shape(&want)), "{p:?}");
    }
    want
}

/// `dom::conv` gives the representative of the reference. Returned is that
/// of the reference.
fn conv_same(defs: Vec<(Name, Def)>, p: &Prob) -> Raw {
    let a = rep(&defs, p);
    let want = ref_conv(&Sorts::new(defs.clone()), &a);
    for run in RUNS {
        let (got, mut f) = run1(&defs, &a, run, |f, ra| dom::conv(&mut f.s, f.decls, f.names, ra));
        assert_eq!(get_rep(&mut f, got), shape(&want), "{p:?}");
    }
    want
}

/// `dom::is_bound` says whether the two sides of the representative are
/// the same pattern.
fn bound_is(defs: Vec<(Name, Def)>, p: &Prob, want: bool) {
    let a = rep(&defs, p);
    let (l, r) = sides(&a);
    assert_eq!(l == r, want, "the reference on {p:?}");
    for run in RUNS {
        let (got, _) = run1(&defs, &a, run, |f, ra| dom::is_bound(&mut f.s, ra));
        assert_eq!(got, want, "{p:?}");
    }
}

/// `dom::covers` says whether the conjunction of the two is the second.
fn covers_is(defs: Vec<(Name, Def)>, p: &Prob, q: &Prob, want: bool) {
    let (a, b) = (rep(&defs, p), rep(&defs, q));
    let m = ref_meet(&Sorts::new(defs.clone()), &a, &b);
    assert_eq!(m.as_ref() == Some(&b), want, "the reference on {p:?} and {q:?}");
    for run in RUNS {
        let (got, _) = run2(&defs, &a, &b, run, |f, ra, rb| dom::covers(&mut f.s, f.decls, f.names, ra, rb));
        assert_eq!(got, want, "{p:?} and {q:?}");
    }
}

/// `dom::same_rep` on the store of `p` and of `q`, the exclusions of the
/// second in the order given or the opposite one.
fn same_is(defs: Vec<(Name, Def)>, p: &Prob, q: &Prob, want: bool) {
    let (a, b) = (rep(&defs, p), rep(&defs, q));
    assert_eq!(a == b, want, "the reference on {p:?} and {q:?}");
    for backwards in [false, true] {
        let mut f = fixture(defs.clone());
        let ra = put_rep(&mut f, &a, false);
        let rb = put_rep(&mut f, &b, backwards);
        dirty(&mut f);
        assert_eq!(dom::same_rep(&mut f.s, ra, rb), want, "{p:?} and {q:?}");
        assert_eq!(dom::same_rep(&mut f.s, rb, ra), want, "{q:?} and {p:?}");
    }
}

/// The sorted patterns `dom::atoms_onto` puts in front of nothing, for the
/// conjunctions `cs` of the variables `vs`: each the name and the variable.
fn atoms(cs: &[Vec<Name>], vs: &[usize]) -> Vec<(Name, T)> {
    let mut f = fixture(wf());
    let mut c = f.s.alloc(Node::Nil);
    for cj in cs.iter().rev() {
        let h = f.conj(cj);
        c = f.s.alloc(Node::App(h, c));
    }
    let vars: Vec<P> = vs.iter().map(|i| pv(*i)).collect();
    let vl = put_pats(&mut f.s, &vars);
    let nil = f.s.alloc(Node::Nil);
    let mut p = dom::atoms_onto(&mut f.s, c, vl, nil);
    f.empty_stack();
    let mut out = Vec::new();
    loop {
        match f.s.read(p) {
            Node::Nil => return out,
            Node::App(h, rest) => {
                match f.s.read(h) {
                    Node::App(n, q) => match f.s.read(n) {
                        Node::Sym(n) => out.push((n, get(&mut f.s, q))),
                        _ => panic!("the sort is not a name"),
                    },
                    _ => panic!("not a sorted pattern"),
                }
                p = rest;
            }
            _ => panic!("a term where a list was expected"),
        }
    }
}

/// The exclusions `dom::excls_onto` puts in front of nothing, for the
/// solved exclusions `xs` over the variables `vs`: each the list of its
/// equations, an equation the application of its two sides.
fn excls(vs: &[usize], xs: &[Vec<P>]) -> Vec<Vec<T>> {
    let mut f = fixture(wf());
    let vars: Vec<P> = vs.iter().map(|i| pv(*i)).collect();
    let vl = put_pats(&mut f.s, &vars);
    let mut x = f.s.alloc(Node::Nil);
    for vals in xs.iter().rev() {
        let h = put_pats(&mut f.s, vals);
        x = f.s.alloc(Node::App(h, x));
    }
    let nil = f.s.alloc(Node::Nil);
    let p = dom::excls_onto(&mut f.s, vl, x, nil);
    f.empty_stack();
    get_lists(&mut f, p)
}

fn eq(l: P, r: P) -> T {
    ap(l.tree(), r.tree())
}

// ---------------------------------------------------------------------
// `one`
// ---------------------------------------------------------------------

#[test]
fn one_with_the_sides_of_the_rep_gives_the_rep_back() {
    let p = plain(su(pv(0)), pv(0));
    let got = one_same(wf(), &p, &su(pv(0)), &pv(0));
    assert_eq!(got, rep(&wf(), &p));
}

#[test]
fn one_with_swapped_sides_renumbers_by_first_occurrence() {
    let p = plain(f2(pv(0), pv(1)), pv(0));
    let got = one_same(wf(), &p, &pv(1), &f2(pv(1), pv(0)));
    assert_eq!(sides(&got), (pv(0), f2(pv(0), pv(1))));
    assert_eq!(got.c.len(), 2);
}

#[test]
fn one_ground_patterns_over_a_rep_without_variables() {
    let got = one_same(wf(), &plain(z(), z()), &su(z()), &a());
    assert_eq!(sides(&got), (su(z()), a()));
    assert!(got.c.is_empty());
    assert!(got.x.is_empty());
}

#[test]
fn one_ground_patterns_forget_the_variables_of_the_rep() {
    let p = rel(pv(0), pv(1), vec![(NAT, pv(0))], vec![vec![(pv(1), z())]]);
    let got = one_same(wf(), &p, &z(), &su(z()));
    assert_eq!(sides(&got), (z(), su(z())));
    assert!(got.c.is_empty());
    assert!(got.x.is_empty());
}

#[test]
fn one_drops_a_variable_the_patterns_do_not_mention() {
    let got = one_same(wf(), &plain(f2(pv(0), pv(1)), pv(1)), &pv(1), &pv(1));
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert_eq!(got.c.len(), 1);
}

#[test]
fn one_repeated_variable_stays_shared() {
    let got = one_same(wf(), &plain(pv(0), pv(1)), &f2(pv(1), pv(1)), &pv(1));
    assert_eq!(sides(&got), (f2(pv(0), pv(0)), pv(0)));
    assert_eq!(got.c.len(), 1);
}

#[test]
fn one_sort_follows_its_variable_to_its_new_number() {
    let p = rel(pv(0), pv(1), vec![(NAT, pv(1))], vec![]);
    let got = one_same(wf(), &p, &pv(1), &pv(0));
    assert_eq!(sides(&got), (pv(0), pv(1)));
    assert!(got.c[0].contains(&NAT));
    assert!(got.c[1].is_empty());
}

#[test]
fn one_variable_outside_the_rep_is_unconstrained() {
    let p = rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![vec![(pv(0), su(z()))]]);
    let got = one_same(wf(), &p, &pv(0), &pv(5));
    assert_eq!(sides(&got), (pv(0), pv(1)));
    assert!(got.c[0].contains(&NAT));
    assert!(got.c[1].is_empty());
    assert_eq!(got.x, vec![vec![(0, su(z()))]]);
}

#[test]
fn one_fresh_variables_over_a_rep_without_variables() {
    let got = one_same(wf(), &plain(z(), z()), &pv(0), &su(pv(0)));
    assert_eq!(sides(&got), (pv(0), su(pv(0))));
    assert_eq!(got.c.len(), 1);
    assert!(got.c[0].is_empty());
}

#[test]
fn one_keeps_exclusion_of_a_variable_that_stays() {
    let p = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), z())]]);
    let got = one_same(wf(), &p, &pv(0), &pv(0));
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert_eq!(got.x, vec![vec![(0, z())]]);
}

#[test]
fn one_drops_exclusion_of_a_variable_that_disappears() {
    let p = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), z())]]);
    let got = one_same(wf(), &p, &pv(1), &pv(1));
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert!(got.x.is_empty());
}

#[test]
fn one_drops_disequality_when_one_of_its_variables_disappears() {
    let p = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), pv(1))]]);
    let got = one_same(wf(), &p, &pv(0), &z());
    assert_eq!(sides(&got), (pv(0), z()));
    assert!(got.x.is_empty());
}

#[test]
fn one_exclusion_is_rewritten_when_its_variable_is_renumbered() {
    let p = rel(pv(0), pv(1), vec![], vec![vec![(pv(1), z())]]);
    let got = one_same(wf(), &p, &pv(1), &pv(0));
    assert_eq!(sides(&got), (pv(0), pv(1)));
    assert_eq!(got.x, vec![vec![(0, z())]]);
}

#[test]
fn one_over_a_rep_whose_sorted_variable_was_opened() {
    // The representative is `s $0` on both sides with `$0` a `nat`.
    let p = rel(pv(0), pv(0), vec![(SUC, pv(0))], vec![]);
    let got = one_same(wf(), &p, &pv(0), &su(pv(0)));
    assert_eq!(sides(&got), (pv(0), su(pv(0))));
    assert!(got.c[0].contains(&NAT));
}

#[test]
fn one_over_a_rep_whose_variable_was_grounded_uses_the_variable_left() {
    // The representative is `z` and `$0`: the `unit` variable is gone.
    let p = rel(pv(0), pv(1), vec![(UNIT, pv(0))], vec![]);
    let got = one_same(wf(), &p, &pv(0), &pv(0));
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert!(got.c[0].is_empty());
}

// ---------------------------------------------------------------------
// `compose`
// ---------------------------------------------------------------------

#[test]
fn compose_identity_with_identity_is_identity() {
    let got = compose_same(wf(), &plain(pv(0), pv(0)), &plain(pv(0), pv(0)));
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert_eq!(got.c.len(), 1);
}

#[test]
fn compose_identity_on_the_left_changes_nothing() {
    let q = rel(f2(pv(0), pv(1)), pv(1), vec![(NAT, pv(0))], vec![vec![(pv(1), z())]]);
    let got = compose_same(wf(), &plain(pv(0), pv(0)), &q);
    assert_eq!(got, rep(&wf(), &q));
}

#[test]
fn compose_identity_on_the_right_changes_nothing() {
    let p = rel(f2(pv(0), pv(1)), pv(1), vec![(NAT, pv(0))], vec![vec![(pv(1), z())]]);
    let got = compose_same(wf(), &p, &plain(pv(0), pv(0)));
    assert_eq!(got, rep(&wf(), &p));
}

#[test]
fn compose_successor_twice_adds_two() {
    let p = plain(pv(0), su(pv(0)));
    let got = compose_same(wf(), &p, &p);
    assert_eq!(sides(&got), (pv(0), su(su(pv(0)))));
}

#[test]
fn compose_decrement_of_first_component_twice() {
    let p = plain(f2(su(pv(0)), pv(1)), f2(pv(0), pv(1)));
    let got = compose_same(wf(), &p, &p);
    assert_eq!(sides(&got), (f2(su(su(pv(0))), pv(1)), f2(pv(0), pv(1))));
}

#[test]
fn compose_ground_sides_that_agree_at_the_interface() {
    let got = compose_same(wf(), &plain(z(), su(z())), &plain(su(z()), a()));
    assert_eq!(sides(&got), (z(), a()));
    assert!(got.c.is_empty());
}

#[test]
fn compose_ground_sides_that_differ_at_the_interface_is_none() {
    compose_none(wf(), &plain(z(), su(z())), &plain(z(), a()));
}

#[test]
fn compose_symbol_clash_at_the_interface_is_none() {
    compose_none(wf(), &plain(pv(0), k1(pv(0))), &plain(su(pv(0)), pv(0)));
}

#[test]
fn compose_occurs_check_at_the_interface_is_none() {
    compose_none(wf(), &plain(pv(0), f2(pv(0), su(pv(0)))), &plain(f2(pv(0), pv(0)), z()));
}

#[test]
fn compose_renames_the_variables_of_the_two_apart() {
    // `$0` of the first is not `$0` of the second: without renaming apart
    // the interface `s $0 = $0` would fail the occurs check.
    let got = compose_same(wf(), &plain(pv(0), su(pv(0))), &plain(pv(0), f2(pv(0), pv(0))));
    assert_eq!(sides(&got), (pv(0), f2(su(pv(0)), su(pv(0)))));
}

#[test]
fn compose_interface_instantiates_the_left_side() {
    let got = compose_same(wf(), &plain(f2(pv(0), pv(0)), pv(0)), &plain(su(pv(0)), pv(0)));
    assert_eq!(sides(&got), (f2(su(pv(0)), su(pv(0))), pv(0)));
}

#[test]
fn compose_interface_grounds_both_sides() {
    let got = compose_same(wf(), &plain(pv(0), pv(0)), &plain(z(), su(z())));
    assert_eq!(sides(&got), (z(), su(z())));
    assert!(got.c.is_empty());
}

#[test]
fn compose_variable_only_on_the_left_side_stays_free() {
    let got = compose_same(wf(), &plain(f2(pv(0), pv(1)), pv(0)), &plain(pv(0), su(pv(0))));
    assert_eq!(sides(&got), (f2(pv(0), pv(1)), su(pv(0))));
    assert_eq!(got.c.len(), 2);
}

#[test]
fn compose_variable_only_on_the_right_side_stays_free() {
    let got = compose_same(wf(), &plain(pv(0), pv(0)), &plain(pv(0), f2(pv(1), pv(0))));
    assert_eq!(sides(&got), (pv(0), f2(pv(1), pv(0))));
    assert_eq!(got.c.len(), 2);
}

#[test]
fn compose_variable_only_at_the_interface_disappears() {
    let got = compose_same(wf(), &plain(z(), pv(0)), &plain(pv(0), su(z())));
    assert_eq!(sides(&got), (z(), su(z())));
    assert!(got.c.is_empty());
}

#[test]
fn compose_numbers_result_variables_by_first_occurrence() {
    let got = compose_same(wf(), &plain(z(), pv(0)), &plain(f2(pv(0), pv(1)), f2(pv(1), pv(0))));
    assert_eq!(sides(&got), (z(), f2(pv(0), pv(1))));
    assert_eq!(got.c.len(), 2);
}

#[test]
fn compose_swap_twice_is_identity_on_pairs() {
    let p = plain(f2(pv(0), pv(1)), f2(pv(1), pv(0)));
    let got = compose_same(wf(), &p, &p);
    assert_eq!(sides(&got), (f2(pv(0), pv(1)), f2(pv(0), pv(1))));
}

#[test]
fn compose_right_sort_flows_to_left_variable() {
    let got = compose_same(wf(), &plain(pv(0), pv(0)), &rel(pv(0), z(), vec![(NAT, pv(0))], vec![]));
    assert_eq!(sides(&got), (pv(0), z()));
    assert!(got.c[0].contains(&NAT));
}

#[test]
fn compose_left_sort_flows_to_right_variable() {
    let got = compose_same(wf(), &rel(z(), pv(0), vec![(NAT, pv(0))], vec![]), &plain(pv(0), pv(0)));
    assert_eq!(sides(&got), (z(), pv(0)));
    assert!(got.c[0].contains(&NAT));
}

#[test]
fn compose_sort_is_pushed_through_the_interface_pattern() {
    let got = compose_same(wf(), &plain(pv(0), su(pv(0))), &rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]));
    assert_eq!(sides(&got), (pv(0), su(pv(0))));
    assert!(got.c[0].contains(&NAT));
}

#[test]
fn compose_sort_rejecting_the_interface_pattern_is_none() {
    compose_none(wf(), &plain(pv(0), k1(pv(0))), &rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]));
}

#[test]
fn compose_sort_does_not_reach_a_variable_off_the_interface() {
    let got = compose_same(wf(), &plain(f2(pv(0), pv(1)), pv(0)), &rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]));
    assert_eq!(sides(&got), (f2(pv(0), pv(1)), pv(0)));
    assert!(got.c[0].contains(&NAT));
    assert!(got.c[1].is_empty());
}

#[test]
fn compose_compatible_sorts_are_conjoined() {
    let p = rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]);
    let q = rel(pv(0), pv(0), vec![(ANY, pv(0))], vec![]);
    let got = compose_same(wf(), &p, &q);
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert!(got.c[0].contains(&NAT) && got.c[0].contains(&ANY));
}

#[test]
fn compose_incompatible_sorts_is_none() {
    let p = rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]);
    compose_none(wf(), &p, &rel(pv(0), pv(0), vec![(BOX, pv(0))], vec![]));
    compose_none(wf(), &p, &rel(pv(0), pv(0), vec![(PAIR, pv(0))], vec![]));
}

#[test]
fn compose_sort_excluding_a_ground_interface_is_none() {
    compose_none(wf(), &plain(a(), a()), &rel(pv(0), pv(0), vec![(ANY, pv(0))], vec![]));
}

#[test]
fn compose_sort_accepting_a_ground_interface_adds_nothing() {
    let got = compose_same(wf(), &plain(su(z()), su(z())), &rel(pv(0), z(), vec![(NAT, pv(0))], vec![]));
    assert_eq!(sides(&got), (su(z()), z()));
    assert!(got.c.is_empty());
}

#[test]
fn compose_one_member_sort_grounds_the_left_variable() {
    let got = compose_same(wf(), &plain(f2(pv(0), pv(1)), pv(0)), &rel(pv(0), pv(1), vec![(UNIT, pv(0))], vec![]));
    assert_eq!(sides(&got), (f2(z(), pv(0)), pv(1)));
    assert_eq!(got.c.len(), 2);
}

#[test]
fn compose_sorts_meeting_in_one_member_ground_the_variable() {
    // `za` is `z` or `a`: with `nat` only `z` is left.
    const ZA: Name = 120;
    let mut defs = wf();
    defs.push((ZA, Def { cases: vec![(Z, vec![]), (A, vec![])], rest: None }));
    let p = rel(f2(pv(0), pv(1)), pv(0), vec![(NAT, pv(0))], vec![]);
    let q = rel(pv(0), pv(0), vec![(ZA, pv(0))], vec![]);
    let got = compose_same(defs, &p, &q);
    assert_eq!(sides(&got), (f2(z(), pv(0)), z()));
    assert_eq!(got.c.len(), 1);
}

#[test]
fn compose_sorts_meeting_in_one_root_open_the_variable() {
    // `sa` is `s` of anything or `a`: with `nat` only `s` of a `nat` is left.
    const SA: Name = 121;
    let mut defs = wf();
    defs.push((SA, Def { cases: vec![(SU, vec![None]), (A, vec![])], rest: None }));
    let p = rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]);
    let q = rel(pv(0), z(), vec![(SA, pv(0))], vec![]);
    let got = compose_same(defs, &p, &q);
    assert_eq!(sides(&got), (su(pv(0)), z()));
    assert!(got.c[0].contains(&NAT));
}

#[test]
fn compose_single_root_sort_opens_the_left_variable() {
    let got = compose_same(wf(), &plain(pv(0), pv(0)), &rel(pv(0), z(), vec![(C2, pv(0))], vec![]));
    assert_eq!(sides(&got), (k1(k1(pv(0))), z()));
    assert!(got.c[0].contains(&NAT));
}

#[test]
fn compose_opened_sort_against_one_member_sort_is_none() {
    let p = rel(pv(0), pv(0), vec![(SUC, pv(0))], vec![]);
    compose_none(wf(), &p, &rel(pv(0), pv(0), vec![(UNIT, pv(0))], vec![]));
}

#[test]
fn compose_exclusion_is_carried_to_the_result() {
    let p = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())]]);
    let got = compose_same(wf(), &p, &plain(pv(0), su(pv(0))));
    assert_eq!(sides(&got), (pv(0), su(pv(0))));
    assert_eq!(got.x, vec![vec![(0, z())]]);
}

#[test]
fn compose_exclusion_of_the_right_argument_is_carried_to_the_result() {
    let q = rel(pv(0), su(pv(0)), vec![], vec![vec![(pv(0), z())]]);
    let got = compose_same(wf(), &plain(f2(pv(0), pv(1)), pv(1)), &q);
    assert_eq!(sides(&got), (f2(pv(0), pv(1)), su(pv(1))));
    assert_eq!(got.x, vec![vec![(1, z())]]);
}

#[test]
fn compose_exclusion_made_vacuous_by_the_interface_is_dropped() {
    let p = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())]]);
    let got = compose_same(wf(), &p, &plain(su(pv(0)), pv(0)));
    assert_eq!(sides(&got), (su(pv(0)), pv(0)));
    assert!(got.x.is_empty());
}

#[test]
fn compose_exclusion_is_instantiated_by_the_interface() {
    let p = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), su(z()))]]);
    let got = compose_same(wf(), &p, &plain(su(pv(0)), pv(0)));
    assert_eq!(sides(&got), (su(pv(0)), pv(0)));
    assert_eq!(got.x, vec![vec![(0, z())]]);
}

#[test]
fn compose_exclusion_of_the_interface_value_is_none() {
    let p = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())]]);
    compose_none(wf(), &p, &plain(z(), z()));
    compose_none(wf(), &plain(z(), z()), &p);
}

#[test]
fn compose_disequality_made_false_by_the_interface_is_none() {
    let p = rel(f2(pv(0), pv(1)), f2(pv(0), pv(1)), vec![], vec![vec![(pv(0), pv(1))]]);
    compose_none(wf(), &p, &plain(f2(pv(0), pv(0)), pv(0)));
}

#[test]
fn compose_disequality_of_two_result_variables_is_kept() {
    let p = rel(f2(pv(0), pv(1)), f2(pv(0), pv(1)), vec![], vec![vec![(pv(0), pv(1))]]);
    let got = compose_same(wf(), &p, &plain(f2(pv(0), pv(1)), pv(0)));
    assert_eq!(sides(&got), (f2(pv(0), pv(1)), pv(0)));
    assert_eq!(got.x, vec![vec![(1, pv(0))]]);
}

#[test]
fn compose_exclusion_of_a_variable_only_at_the_interface_is_dropped() {
    let p = rel(z(), pv(0), vec![], vec![vec![(pv(0), z())]]);
    let got = compose_same(wf(), &p, &plain(pv(0), a()));
    assert_eq!(sides(&got), (z(), a()));
    assert!(got.c.is_empty());
    assert!(got.x.is_empty());
}

#[test]
fn compose_disequality_with_a_variable_that_disappears_is_dropped() {
    let p = rel(pv(0), f2(pv(0), pv(1)), vec![], vec![vec![(pv(0), pv(1))]]);
    let got = compose_same(wf(), &p, &plain(f2(pv(0), pv(1)), pv(0)));
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert_eq!(got.c.len(), 1);
    assert!(got.x.is_empty());
}

#[test]
fn compose_exclusion_of_a_variable_off_the_interface_is_kept() {
    let p = rel(f2(pv(0), pv(1)), pv(0), vec![], vec![vec![(pv(1), z())]]);
    let got = compose_same(wf(), &p, &plain(pv(0), su(pv(0))));
    assert_eq!(sides(&got), (f2(pv(0), pv(1)), su(pv(0))));
    assert_eq!(got.x, vec![vec![(1, z())]]);
}

#[test]
fn compose_exclusions_of_both_arguments_are_kept() {
    let p = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())]]);
    let q = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), su(z()))]]);
    let got = compose_same(wf(), &p, &q);
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert_eq!(got.x.len(), 2);
    assert!(got.x.contains(&vec![(0, z())]) && got.x.contains(&vec![(0, su(z()))]));
}

#[test]
fn compose_same_exclusion_in_both_arguments_is_kept_once() {
    let p = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())]]);
    let got = compose_same(wf(), &p, &p);
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert_eq!(got.x, vec![vec![(0, z())]]);
}

#[test]
fn compose_exclusion_implied_by_one_of_the_other_argument_is_pruned() {
    let id = f2(pv(0), pv(1));
    let p = rel(id.clone(), id.clone(), vec![], vec![vec![(pv(0), z())]]);
    let q = rel(id.clone(), id.clone(), vec![], vec![vec![(pv(0), z()), (pv(1), z())]]);
    let got = compose_same(wf(), &p, &q);
    assert_eq!(sides(&got), (id.clone(), id));
    assert_eq!(got.x, vec![vec![(0, z())]]);
}

#[test]
fn compose_exclusion_of_zero_from_a_nat_opens_the_variable() {
    let p = rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]);
    let q = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())]]);
    let got = compose_same(wf(), &p, &q);
    assert_eq!(sides(&got), (su(pv(0)), su(pv(0))));
    assert!(got.c[0].contains(&NAT));
    assert!(got.x.is_empty());
}

#[test]
fn compose_exclusion_ruled_out_by_the_sort_of_the_other_argument_is_dropped() {
    let p = rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]);
    let q = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), a())]]);
    let got = compose_same(wf(), &p, &q);
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert!(got.x.is_empty());
}

#[test]
fn compose_exclusions_of_both_arguments_emptying_a_sort_is_none() {
    // `za` is `z` or `a`; the first is left with `a`, which the second excludes.
    const ZA: Name = 120;
    let mut defs = wf();
    defs.push((ZA, Def { cases: vec![(Z, vec![]), (A, vec![])], rest: None }));
    let p = rel(pv(0), pv(0), vec![(ZA, pv(0))], vec![vec![(pv(0), z())]]);
    let q = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), a())]]);
    compose_none(defs, &p, &q);
}

// ---------------------------------------------------------------------
// `meet`
// ---------------------------------------------------------------------

#[test]
fn meet_of_a_relation_with_itself_is_itself() {
    let p = rel(f2(pv(0), pv(1)), su(pv(0)), vec![(NAT, pv(1))], vec![vec![(pv(0), z())]]);
    let got = meet_same(wf(), &p, &p);
    assert_eq!(got, rep(&wf(), &p));
}

#[test]
fn meet_does_not_depend_on_the_variable_names_of_one_side() {
    let got = meet_same(wf(), &plain(f2(pv(0), pv(1)), pv(1)), &plain(f2(pv(7), pv(3)), pv(3)));
    assert_eq!(sides(&got), (f2(pv(0), pv(1)), pv(1)));
    assert_eq!(got.c.len(), 2);
}

#[test]
fn meet_of_everything_with_identity_is_identity() {
    let got = meet_same(wf(), &plain(pv(0), pv(1)), &plain(pv(0), pv(0)));
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert_eq!(got.c.len(), 1);
}

#[test]
fn meet_instantiates_both_sides() {
    let got = meet_same(wf(), &plain(pv(0), pv(1)), &plain(su(pv(0)), z()));
    assert_eq!(sides(&got), (su(pv(0)), z()));
}

#[test]
fn meet_takes_the_left_side_of_one_and_the_right_side_of_the_other() {
    let got = meet_same(wf(), &plain(su(pv(0)), pv(1)), &plain(pv(0), k1(pv(1))));
    assert_eq!(sides(&got), (su(pv(0)), k1(pv(1))));
    assert_eq!(got.c.len(), 2);
}

#[test]
fn meet_binding_on_the_left_side_flows_to_the_right_side() {
    let got = meet_same(wf(), &plain(pv(0), pv(0)), &plain(z(), pv(0)));
    assert_eq!(sides(&got), (z(), z()));
    assert!(got.c.is_empty());
}

#[test]
fn meet_repeated_variable_forces_equal_components() {
    let got = meet_same(wf(), &plain(f2(pv(0), pv(0)), pv(1)), &plain(f2(z(), pv(0)), pv(0)));
    assert_eq!(sides(&got), (f2(z(), z()), z()));
}

#[test]
fn meet_of_equal_ground_relations_is_that_relation() {
    let got = meet_same(wf(), &plain(z(), su(z())), &plain(z(), su(z())));
    assert_eq!(sides(&got), (z(), su(z())));
    assert!(got.c.is_empty());
}

#[test]
fn meet_of_ground_relation_with_a_pattern_it_matches() {
    let got = meet_same(wf(), &plain(z(), su(z())), &plain(pv(0), su(pv(0))));
    assert_eq!(sides(&got), (z(), su(z())));
}

#[test]
fn meet_clash_on_the_left_side_is_none() {
    meet_none(wf(), &plain(z(), pv(0)), &plain(su(pv(0)), pv(1)));
}

#[test]
fn meet_clash_on_the_right_side_is_none() {
    meet_none(wf(), &plain(pv(0), z()), &plain(pv(0), su(pv(1))));
}

#[test]
fn meet_occurs_check_across_the_two_sides_is_none() {
    meet_none(wf(), &plain(pv(0), pv(0)), &plain(pv(0), su(pv(0))));
}

#[test]
fn meet_of_different_ground_relations_is_none() {
    meet_none(wf(), &plain(z(), z()), &plain(z(), su(z())));
}

#[test]
fn meet_sorts_of_the_same_variable_are_conjoined() {
    let p = rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]);
    let q = rel(pv(0), pv(0), vec![(ANY, pv(0))], vec![]);
    let got = meet_same(wf(), &p, &q);
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert!(got.c[0].contains(&NAT) && got.c[0].contains(&ANY));
}

#[test]
fn meet_sorts_of_different_sides_each_reach_their_variable() {
    let p = rel(pv(0), pv(1), vec![(NAT, pv(0))], vec![]);
    let q = rel(pv(0), pv(1), vec![(ANY, pv(1))], vec![]);
    let got = meet_same(wf(), &p, &q);
    assert_eq!(sides(&got), (pv(0), pv(1)));
    assert!(got.c[0].contains(&NAT));
    assert!(got.c[1].contains(&ANY) && !got.c[1].contains(&NAT));
}

#[test]
fn meet_incompatible_sorts_is_none() {
    let p = rel(pv(0), pv(1), vec![(NAT, pv(0))], vec![]);
    meet_none(wf(), &p, &rel(pv(0), pv(1), vec![(BOX, pv(0))], vec![]));
    meet_none(wf(), &p, &rel(pv(0), pv(1), vec![(MIX, pv(0))], vec![]));
}

#[test]
fn meet_sort_rejecting_the_pattern_of_the_other_is_none() {
    meet_none(wf(), &rel(pv(0), pv(1), vec![(NAT, pv(1))], vec![]), &plain(pv(0), k1(pv(0))));
}

#[test]
fn meet_sort_is_pushed_into_the_pattern_of_the_other() {
    let got = meet_same(wf(), &rel(pv(0), pv(1), vec![(PAIR, pv(1))], vec![]), &plain(pv(0), pr(pv(0), z())));
    assert_eq!(sides(&got), (pv(0), pr(pv(0), z())));
    assert!(got.c[0].contains(&NAT));
}

#[test]
fn meet_one_member_sort_grounds_the_variable_of_the_other() {
    let got = meet_same(wf(), &plain(pv(0), su(pv(0))), &rel(pv(0), pv(1), vec![(UNIT, pv(0))], vec![]));
    assert_eq!(sides(&got), (z(), su(z())));
    assert!(got.c.is_empty());
}

#[test]
fn meet_sorts_meeting_in_one_member_ground_the_variable() {
    const ZA: Name = 120;
    let mut defs = wf();
    defs.push((ZA, Def { cases: vec![(Z, vec![]), (A, vec![])], rest: None }));
    let p = rel(pv(0), f2(pv(0), pv(1)), vec![(NAT, pv(0))], vec![]);
    let q = rel(pv(0), pv(1), vec![(ZA, pv(0))], vec![]);
    let got = meet_same(defs, &p, &q);
    assert_eq!(sides(&got), (z(), f2(z(), pv(0))));
    assert_eq!(got.c.len(), 1);
}

#[test]
fn meet_sorts_meeting_in_one_root_open_the_variable() {
    const SA: Name = 121;
    let mut defs = wf();
    defs.push((SA, Def { cases: vec![(SU, vec![None]), (A, vec![])], rest: None }));
    let p = rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]);
    let q = rel(pv(0), pv(1), vec![(SA, pv(1))], vec![]);
    let got = meet_same(defs, &p, &q);
    assert_eq!(sides(&got), (su(pv(0)), su(pv(0))));
    assert!(got.c[0].contains(&NAT));
}

#[test]
fn meet_single_root_sort_opens_the_variable_of_the_other() {
    let got = meet_same(wf(), &plain(pv(0), pv(0)), &rel(pv(0), pv(1), vec![(BOX, pv(1))], vec![]));
    assert_eq!(sides(&got), (k1(pv(0)), k1(pv(0))));
    assert!(got.c[0].contains(&NAT));
}

#[test]
fn meet_exclusions_of_both_arguments_are_kept() {
    let p = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), z())]]);
    let q = rel(pv(0), pv(1), vec![], vec![vec![(pv(1), su(z()))]]);
    let got = meet_same(wf(), &p, &q);
    assert_eq!(sides(&got), (pv(0), pv(1)));
    assert_eq!(got.x.len(), 2);
    assert!(got.x.contains(&vec![(0, z())]) && got.x.contains(&vec![(1, su(z()))]));
}

#[test]
fn meet_same_exclusion_in_both_arguments_is_kept_once() {
    let p = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), pv(1))]]);
    let q = rel(pv(0), pv(1), vec![], vec![vec![(pv(1), pv(0))]]);
    let got = meet_same(wf(), &p, &q);
    assert_eq!(got.x, vec![vec![(1, pv(0))]]);
}

#[test]
fn meet_exclusion_implied_by_one_of_the_other_argument_is_pruned() {
    let p = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), z()), (pv(1), z())]]);
    let q = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), z())]]);
    let got = meet_same(wf(), &p, &q);
    assert_eq!(got.x, vec![vec![(0, z())]]);
}

#[test]
fn meet_exclusion_is_kept_on_the_instantiated_pattern() {
    let p = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), z())]]);
    let got = meet_same(wf(), &p, &plain(pv(0), su(pv(1))));
    assert_eq!(sides(&got), (pv(0), su(pv(1))));
    assert_eq!(got.x, vec![vec![(0, z())]]);
}

#[test]
fn meet_exclusion_made_vacuous_by_the_other_is_dropped() {
    let p = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())]]);
    let got = meet_same(wf(), &p, &plain(su(pv(0)), pv(1)));
    assert_eq!(sides(&got), (su(pv(0)), su(pv(0))));
    assert!(got.x.is_empty());
}

#[test]
fn meet_exclusion_of_the_value_the_other_fixes_is_none() {
    let p = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), z())]]);
    meet_none(wf(), &p, &plain(z(), pv(0)));
}

#[test]
fn meet_disequality_with_identity_is_none() {
    let p = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), pv(1))]]);
    meet_none(wf(), &p, &plain(pv(0), pv(0)));
}

#[test]
fn meet_disequality_becomes_exclusion_of_a_value() {
    let p = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), pv(1))]]);
    let got = meet_same(wf(), &p, &plain(z(), pv(0)));
    assert_eq!(sides(&got), (z(), pv(0)));
    assert_eq!(got.x, vec![vec![(0, z())]]);
}

#[test]
fn meet_exclusion_of_zero_from_a_nat_opens_the_variable() {
    let p = rel(pv(0), pv(1), vec![(NAT, pv(0))], vec![]);
    let q = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), z())]]);
    let got = meet_same(wf(), &p, &q);
    assert_eq!(sides(&got), (su(pv(0)), pv(1)));
    assert!(got.c[0].contains(&NAT));
    assert!(got.x.is_empty());
}

#[test]
fn meet_exclusion_of_the_only_member_of_the_sort_of_the_other_is_none() {
    // The second is `z` related to anything; the first excludes `z` there.
    let p = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), z())]]);
    meet_none(wf(), &p, &rel(pv(0), pv(1), vec![(UNIT, pv(0))], vec![]));
}

// ---------------------------------------------------------------------
// `right` and `conv`
// ---------------------------------------------------------------------

#[test]
fn right_relates_the_right_side_to_itself() {
    let got = right_same(wf(), &plain(pv(0), su(pv(0))));
    assert_eq!(sides(&got), (su(pv(0)), su(pv(0))));
}

#[test]
fn right_of_ground_relation_is_ground() {
    let got = right_same(wf(), &plain(z(), su(z())));
    assert_eq!(sides(&got), (su(z()), su(z())));
    assert!(got.c.is_empty());
}

#[test]
fn right_drops_variables_only_on_the_left_side_and_renumbers() {
    let got = right_same(wf(), &plain(f2(pv(0), pv(1)), pv(1)));
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert_eq!(got.c.len(), 1);
}

#[test]
fn right_keeps_the_sort_of_a_right_variable() {
    let got = right_same(wf(), &rel(pv(0), pv(1), vec![(NAT, pv(1))], vec![]));
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert!(got.c[0].contains(&NAT));
}

#[test]
fn right_drops_the_sort_of_a_left_only_variable() {
    let got = right_same(wf(), &rel(pv(0), pv(1), vec![(NAT, pv(0))], vec![]));
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert!(got.c[0].is_empty());
}

#[test]
fn right_keeps_the_exclusion_of_a_right_variable() {
    let got = right_same(wf(), &rel(pv(0), pv(1), vec![], vec![vec![(pv(1), z())]]));
    assert_eq!(got.x, vec![vec![(0, z())]]);
}

#[test]
fn right_drops_the_exclusion_of_a_left_only_variable() {
    let got = right_same(wf(), &rel(pv(0), pv(1), vec![], vec![vec![(pv(0), z())]]));
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert!(got.x.is_empty());
}

#[test]
fn right_drops_a_disequality_between_a_left_and_a_right_variable() {
    let got = right_same(wf(), &rel(pv(0), pv(1), vec![], vec![vec![(pv(0), pv(1))]]));
    assert_eq!(sides(&got), (pv(0), pv(0)));
    assert!(got.x.is_empty());
}

#[test]
fn right_of_a_bound_is_itself() {
    let p = rel(f2(pv(0), pv(1)), f2(pv(0), pv(1)), vec![(NAT, pv(0))], vec![vec![(pv(1), pv(0))]]);
    let got = right_same(wf(), &p);
    assert_eq!(got, rep(&wf(), &p));
}

#[test]
fn right_of_right_is_right() {
    let p = rel(f2(pv(0), pv(1)), su(pv(1)), vec![(NAT, pv(1))], vec![vec![(pv(1), su(z()))]]);
    let once = right_same(wf(), &p);
    let twice = right_same(wf(), &once.prob());
    assert_eq!(twice, once);
}

#[test]
fn conv_swaps_the_two_sides() {
    let got = conv_same(wf(), &plain(pv(0), su(pv(0))));
    assert_eq!(sides(&got), (su(pv(0)), pv(0)));
}

#[test]
fn conv_of_ground_relation_swaps_the_ground_sides() {
    let got = conv_same(wf(), &plain(z(), su(z())));
    assert_eq!(sides(&got), (su(z()), z()));
    assert!(got.c.is_empty());
}

#[test]
fn conv_numbers_variables_by_first_occurrence_in_the_new_order() {
    let got = conv_same(wf(), &plain(f2(pv(0), pv(1)), pv(1)));
    assert_eq!(sides(&got), (pv(0), f2(pv(1), pv(0))));
    assert_eq!(got.c.len(), 2);
}

#[test]
fn conv_moves_sorts_and_exclusions_with_their_variables() {
    let p = rel(f2(pv(0), pv(1)), pv(1), vec![(NAT, pv(0))], vec![vec![(pv(1), z())]]);
    let got = conv_same(wf(), &p);
    assert_eq!(sides(&got), (pv(0), f2(pv(1), pv(0))));
    assert!(got.c[0].is_empty());
    assert!(got.c[1].contains(&NAT));
    assert_eq!(got.x, vec![vec![(0, z())]]);
}

#[test]
fn conv_keeps_a_disequality_of_two_variables() {
    let got = conv_same(wf(), &rel(pv(0), pv(1), vec![], vec![vec![(pv(0), pv(1))]]));
    assert_eq!(sides(&got), (pv(0), pv(1)));
    assert_eq!(got.x, vec![vec![(1, pv(0))]]);
}

#[test]
fn conv_of_a_bound_is_itself() {
    let p = rel(su(pv(0)), su(pv(0)), vec![(NAT, pv(0))], vec![vec![(pv(0), z())]]);
    let got = conv_same(wf(), &p);
    assert_eq!(got, rep(&wf(), &p));
}

#[test]
fn conv_of_conv_is_the_relation() {
    let p = rel(f2(pv(0), pv(1)), f2(pv(1), pv(2)), vec![(NAT, pv(2))], vec![vec![(pv(0), pv(2))], vec![(pv(1), z())]]);
    let once = conv_same(wf(), &p);
    let twice = conv_same(wf(), &once.prob());
    assert_eq!(twice, rep(&wf(), &p));
}

// ---------------------------------------------------------------------
// `is_bound`
// ---------------------------------------------------------------------

#[test]
fn is_bound_identity_on_a_variable() {
    bound_is(wf(), &plain(pv(0), pv(0)), true);
}

#[test]
fn is_bound_same_ground_sides() {
    bound_is(wf(), &plain(su(z()), su(z())), true);
}

#[test]
fn is_bound_same_sides_with_sorts_and_exclusions() {
    bound_is(wf(), &rel(f2(pv(0), pv(1)), f2(pv(0), pv(1)), vec![(NAT, pv(0))], vec![vec![(pv(1), pv(0))]]), true);
}

#[test]
fn is_bound_not_for_two_different_variables() {
    bound_is(wf(), &plain(pv(0), pv(1)), false);
}

#[test]
fn is_bound_not_for_two_variables_of_the_same_sort() {
    bound_is(wf(), &rel(pv(0), pv(1), vec![(NAT, pv(0)), (NAT, pv(1))], vec![]), false);
}

#[test]
fn is_bound_not_for_different_ground_sides() {
    bound_is(wf(), &plain(z(), su(z())), false);
}

#[test]
fn is_bound_not_for_a_side_under_a_symbol() {
    bound_is(wf(), &plain(pv(0), su(pv(0))), false);
}

#[test]
fn is_bound_not_for_swapped_components() {
    bound_is(wf(), &plain(f2(pv(0), pv(1)), f2(pv(1), pv(0))), false);
}

#[test]
fn is_bound_when_one_member_sorts_ground_both_variables() {
    bound_is(wf(), &rel(pv(0), pv(1), vec![(UNIT, pv(0)), (UNIT, pv(1))], vec![]), true);
}

#[test]
fn is_bound_when_one_member_sort_grounds_a_variable_to_the_other_side() {
    bound_is(wf(), &rel(pv(0), pr(z(), z()), vec![(TWO, pv(0))], vec![]), true);
}

#[test]
fn is_bound_not_when_a_one_member_sort_grounds_only_one_side() {
    bound_is(wf(), &rel(pv(0), pv(1), vec![(UNIT, pv(0))], vec![]), false);
}

// ---------------------------------------------------------------------
// `covers`
// ---------------------------------------------------------------------

#[test]
fn covers_is_reflexive() {
    let p = plain(f2(pv(0), pv(1)), pv(1));
    covers_is(wf(), &p, &p, true);
}

#[test]
fn covers_is_reflexive_with_sorts_and_exclusions() {
    let p = rel(pv(0), pv(1), vec![(NAT, pv(0))], vec![vec![(pv(0), su(z()))], vec![(pv(1), pv(0))]]);
    covers_is(wf(), &p, &p, true);
}

#[test]
fn covers_does_not_depend_on_variable_names() {
    covers_is(wf(), &plain(f2(pv(3), pv(1)), pv(1)), &plain(f2(pv(0), pv(2)), pv(2)), true);
}

#[test]
fn covers_everything_covers_identity_but_not_the_reverse() {
    covers_is(wf(), &plain(pv(0), pv(1)), &plain(pv(0), pv(0)), true);
    covers_is(wf(), &plain(pv(0), pv(0)), &plain(pv(0), pv(1)), false);
}

#[test]
fn covers_a_pattern_covers_its_instance_but_not_the_reverse() {
    covers_is(wf(), &plain(pv(0), pv(0)), &plain(su(pv(0)), su(pv(0))), true);
    covers_is(wf(), &plain(su(pv(0)), su(pv(0))), &plain(pv(0), pv(0)), false);
}

#[test]
fn covers_a_pattern_covers_a_ground_instance() {
    covers_is(wf(), &plain(pv(0), su(pv(0))), &plain(z(), su(z())), true);
    covers_is(wf(), &plain(z(), su(z())), &plain(pv(0), su(pv(0))), false);
}

#[test]
fn covers_not_for_overlapping_relations_neither_inside_the_other() {
    covers_is(wf(), &plain(pv(0), z()), &plain(z(), pv(0)), false);
    covers_is(wf(), &plain(z(), pv(0)), &plain(pv(0), z()), false);
}

#[test]
fn covers_not_for_relations_with_nothing_in_common() {
    covers_is(wf(), &plain(z(), z()), &plain(su(z()), su(z())), false);
    covers_is(wf(), &plain(pv(0), pv(0)), &plain(pv(0), su(pv(0))), false);
}

#[test]
fn covers_unsorted_covers_sorted_but_not_the_reverse() {
    let s = rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]);
    covers_is(wf(), &plain(pv(0), pv(0)), &s, true);
    covers_is(wf(), &s, &plain(pv(0), pv(0)), false);
}

#[test]
fn covers_wider_sort_covers_narrower_but_not_the_reverse() {
    let any = rel(pv(0), pv(0), vec![(ANY, pv(0))], vec![]);
    let nat = rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]);
    let suc = rel(pv(0), pv(0), vec![(SUC, pv(0))], vec![]);
    covers_is(wf(), &any, &nat, true);
    covers_is(wf(), &nat, &any, false);
    covers_is(wf(), &nat, &suc, true);
    covers_is(wf(), &suc, &nat, false);
}

#[test]
fn covers_not_for_disjoint_sorts() {
    let nat = rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]);
    let bx = rel(pv(0), pv(0), vec![(BOX, pv(0))], vec![]);
    covers_is(wf(), &nat, &bx, false);
    covers_is(wf(), &bx, &nat, false);
}

#[test]
fn covers_sort_covers_a_ground_member_and_not_a_non_member() {
    let nat = rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]);
    covers_is(wf(), &nat, &plain(su(z()), su(z())), true);
    covers_is(wf(), &nat, &plain(a(), a()), false);
}

#[test]
fn covers_without_exclusion_covers_with_exclusion_but_not_the_reverse() {
    let x = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())]]);
    covers_is(wf(), &plain(pv(0), pv(0)), &x, true);
    covers_is(wf(), &x, &plain(pv(0), pv(0)), false);
}

#[test]
fn covers_fewer_exclusions_cover_more_but_not_the_reverse() {
    let one = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())]]);
    let two = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())], vec![(pv(0), su(z()))]]);
    covers_is(wf(), &one, &two, true);
    covers_is(wf(), &two, &one, false);
}

#[test]
fn covers_not_for_different_exclusions() {
    let p = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())]]);
    let q = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), su(z()))]]);
    covers_is(wf(), &p, &q, false);
    covers_is(wf(), &q, &p, false);
}

#[test]
fn covers_exclusion_covers_a_pattern_that_cannot_take_the_value() {
    let x = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())]]);
    covers_is(wf(), &x, &plain(su(pv(0)), su(pv(0))), true);
    covers_is(wf(), &x, &rel(pv(0), pv(0), vec![(SUC, pv(0))], vec![]), true);
    covers_is(wf(), &x, &rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]), false);
    covers_is(wf(), &x, &plain(z(), z()), false);
}

#[test]
fn covers_weaker_exclusion_covers_stronger_but_not_the_reverse() {
    let weak = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), z()), (pv(1), z())]]);
    let strong = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), z())]]);
    covers_is(wf(), &weak, &strong, true);
    covers_is(wf(), &strong, &weak, false);
}

// ---------------------------------------------------------------------
// `same_rep`
// ---------------------------------------------------------------------

#[test]
fn same_rep_of_a_plain_relation_with_itself() {
    let p = plain(f2(pv(0), pv(1)), su(pv(0)));
    same_is(wf(), &p, &p, true);
}

#[test]
fn same_rep_of_reps_without_variables() {
    same_is(wf(), &plain(z(), su(z())), &plain(z(), su(z())), true);
    same_is(wf(), &plain(z(), su(z())), &plain(su(z()), z()), false);
}

#[test]
fn same_rep_for_the_same_relation_written_with_other_variables() {
    same_is(wf(), &plain(f2(pv(4), pv(2)), pv(2)), &plain(f2(pv(0), pv(1)), pv(1)), true);
}

#[test]
fn same_rep_with_exclusions_in_another_order() {
    let xs = vec![vec![(pv(0), z())], vec![(pv(1), pv(0))], vec![(pv(1), su(z()))]];
    let mut ys = xs.clone();
    ys.rotate_left(1);
    let p = rel(pv(0), pv(1), vec![(NAT, pv(0))], xs);
    let q = rel(pv(0), pv(1), vec![(NAT, pv(0))], ys);
    same_is(wf(), &p, &q, true);
}

#[test]
fn same_rep_not_for_different_left_sides() {
    same_is(wf(), &plain(pv(0), pv(0)), &plain(su(pv(0)), pv(0)), false);
}

#[test]
fn same_rep_not_for_different_right_sides() {
    same_is(wf(), &plain(pv(0), z()), &plain(pv(0), su(z())), false);
}

#[test]
fn same_rep_not_for_shared_against_distinct_variables() {
    same_is(wf(), &plain(pv(0), pv(0)), &plain(pv(0), pv(1)), false);
}

#[test]
fn same_rep_not_for_sorted_against_unsorted() {
    same_is(wf(), &rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]), &plain(pv(0), pv(0)), false);
}

#[test]
fn same_rep_not_for_different_conjunctions() {
    let nat = rel(pv(0), pv(0), vec![(NAT, pv(0))], vec![]);
    let any = rel(pv(0), pv(0), vec![(ANY, pv(0))], vec![]);
    same_is(wf(), &nat, &any, false);
}

#[test]
fn same_rep_not_for_the_sort_on_another_variable() {
    let p = rel(pv(0), pv(1), vec![(NAT, pv(0))], vec![]);
    let q = rel(pv(0), pv(1), vec![(NAT, pv(1))], vec![]);
    same_is(wf(), &p, &q, false);
}

#[test]
fn same_rep_not_for_exclusion_against_none() {
    same_is(wf(), &rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())]]), &plain(pv(0), pv(0)), false);
}

#[test]
fn same_rep_not_when_one_exclusion_list_is_a_strict_part_of_the_other() {
    let p = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())]]);
    let q = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())], vec![(pv(0), su(z()))]]);
    same_is(wf(), &p, &q, false);
}

#[test]
fn same_rep_not_for_as_many_exclusions_of_which_one_differs() {
    let p = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())], vec![(pv(0), su(z()))]]);
    let q = rel(pv(0), pv(0), vec![], vec![vec![(pv(0), z())], vec![(pv(0), a())]]);
    same_is(wf(), &p, &q, false);
}

#[test]
fn same_rep_not_for_the_exclusion_on_another_variable() {
    let p = rel(pv(0), pv(1), vec![], vec![vec![(pv(0), z())]]);
    let q = rel(pv(0), pv(1), vec![], vec![vec![(pv(1), z())]]);
    same_is(wf(), &p, &q, false);
}

// ---------------------------------------------------------------------
// `atoms_onto` and `excls_onto`
// ---------------------------------------------------------------------

#[test]
fn atoms_onto_no_variables_gives_nothing() {
    assert_eq!(atoms(&[], &[]), vec![]);
}

#[test]
fn atoms_onto_empty_conjunctions_give_nothing() {
    assert_eq!(atoms(&[vec![], vec![]], &[0, 1]), vec![]);
}

#[test]
fn atoms_onto_one_name_gives_one_sorted_variable() {
    assert_eq!(atoms(&[vec![NAT]], &[0]), vec![(NAT, v(0))]);
}

#[test]
fn atoms_onto_several_names_give_one_sorted_pattern_each() {
    let mut got = atoms(&[vec![NAT, ANY, SUC]], &[0]);
    got.sort_by_key(|(n, _)| *n);
    assert_eq!(got, vec![(NAT, v(0)), (SUC, v(0)), (ANY, v(0))]);
}

#[test]
fn atoms_onto_pairs_each_conjunction_with_its_variable() {
    let mut got = atoms(&[vec![NAT], vec![], vec![BOX, ANY]], &[0, 1, 2]);
    got.sort_by_key(|(n, _)| *n);
    assert_eq!(got, vec![(NAT, v(0)), (BOX, v(2)), (ANY, v(2))]);
}

#[test]
fn atoms_onto_uses_the_variables_given_not_their_positions() {
    let mut got = atoms(&[vec![UNIT], vec![NAT]], &[5, 3]);
    got.sort_by_key(|(n, _)| *n);
    assert_eq!(got, vec![(UNIT, v(5)), (NAT, v(3))]);
}

#[test]
fn excls_onto_no_exclusions_gives_nothing() {
    assert_eq!(excls(&[0, 1], &[]), Vec::<Vec<T>>::new());
}

#[test]
fn excls_onto_no_variables_and_no_exclusions_gives_nothing() {
    assert_eq!(excls(&[], &[]), Vec::<Vec<T>>::new());
}

#[test]
fn excls_onto_one_variable_gives_one_equation() {
    assert_eq!(excls(&[0], &[vec![z()]]), vec![vec![eq(pv(0), z())]]);
}

#[test]
fn excls_onto_writes_a_variable_that_is_its_own_value_as_an_equation() {
    assert_eq!(excls(&[0, 1], &[vec![pv(0), z()]]), vec![vec![eq(pv(0), pv(0)), eq(pv(1), z())]]);
}

#[test]
fn excls_onto_value_that_is_another_variable() {
    assert_eq!(excls(&[0, 1], &[vec![pv(0), su(pv(0))]]), vec![vec![eq(pv(0), pv(0)), eq(pv(1), su(pv(0)))]]);
}

#[test]
fn excls_onto_uses_the_variables_given_not_their_positions() {
    assert_eq!(excls(&[2, 3], &[vec![pv(2), pv(2)]]), vec![vec![eq(pv(2), pv(2)), eq(pv(3), pv(2))]]);
}

#[test]
fn excls_onto_several_exclusions_give_one_equation_list_each() {
    let mut got = excls(&[0, 1], &[vec![z(), pv(1)], vec![pv(0), pv(0)], vec![su(z()), a()]]);
    got.sort_by_key(|l| format!("{l:?}"));
    let mut want = vec![
        vec![eq(pv(0), z()), eq(pv(1), pv(1))],
        vec![eq(pv(0), pv(0)), eq(pv(1), pv(0))],
        vec![eq(pv(0), su(z())), eq(pv(1), a())],
    ];
    want.sort_by_key(|l| format!("{l:?}"));
    assert_eq!(got, want);
}

#[test]
fn excls_onto_an_exclusion_over_no_variables_has_no_equations() {
    assert_eq!(excls(&[], &[vec![]]), vec![Vec::<T>::new()]);
}
