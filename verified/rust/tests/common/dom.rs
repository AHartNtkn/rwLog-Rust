//! Representatives of the domain of sorts on trees and in the store: the
//! operations of the specification (`lean/RwLog/Sorts/Dom.lean`) as written
//! on trees, each a problem and its canonical store (`sorts::normal`), and
//! the helpers that write a representative to the store and read one back.
//!
//! A relation is written as a problem whose pattern is the pair of its two
//! sides. In the reference the pair is the symbol `PSYM` applied to the two
//! sides; in the store it is `Nil` applied to them.

use super::sorts::*;
use super::{get, get_list, T};
use rwlog_core::dom::{self, Oriented, Rep};
use rwlog_core::store::{Node, Tbl, TermId};

/// The pair of the reference.
pub const PSYM: u32 = 99;

pub fn pair(l: P, r: P) -> P {
    pf(PSYM, vec![l, r])
}

/// The relation of the sides `l` and `r` under the sorts `a` of patterns
/// and the exclusions `x`.
pub fn rel(l: P, r: P, a: Vec<(Name, P)>, x: Excls) -> Prob {
    Prob { t: pair(l, r), e: vec![], a, x }
}

/// The relation of the sides `l` and `r` with nothing said of the variables.
pub fn plain(l: P, r: P) -> Prob {
    rel(l, r, vec![], vec![])
}

pub fn sides(r: &Raw) -> (P, P) {
    match &r.t {
        P::F(f, args) if *f == PSYM && args.len() == 2 => (args[0].clone(), args[1].clone()),
        _ => panic!("the pattern of a representative is not a pair"),
    }
}

pub fn shift(p: &P, k: usize) -> P {
    match p {
        P::V(x) => pv(x + k),
        P::F(f, args) => pf(*f, args.iter().map(|q| shift(q, k)).collect()),
    }
}

/// `Rep.one`: the pair of `u` and `w` over the solutions of `r`.
pub fn ref_one(ss: &Sorts, r: &Raw, u: &P, w: &P) -> Option<Raw> {
    normal(ss, &Prob { t: pair(u.clone(), w.clone()), ..r.prob() })
}

/// `Rep.two`: the pair of `u` and `w` and the equations `e` over the
/// solutions of `a` and, its variables moved above those of `a`, of `b`.
pub fn ref_two(ss: &Sorts, a: &Raw, b: &Raw, u: &P, w: &P, e: Vec<(P, P)>) -> Option<Raw> {
    let k = a.c.len();
    let (pa, pb) = (a.prob(), b.prob());
    let mut at = pa.a;
    at.extend(pb.a.iter().map(|(n, p)| (*n, shift(p, k))));
    let mut x = pa.x;
    x.extend(pb.x.iter().map(|e| e.iter().map(|(l, r)| (shift(l, k), shift(r, k))).collect::<Vec<_>>()));
    normal(ss, &Prob { t: pair(u.clone(), w.clone()), e, a: at, x })
}

pub fn ref_compose(ss: &Sorts, a: &Raw, b: &Raw) -> Option<Raw> {
    let k = a.c.len();
    let ((al, ar), (bl, br)) = (sides(a), sides(b));
    ref_two(ss, a, b, &al, &shift(&br, k), vec![(ar, shift(&bl, k))])
}

pub fn ref_meet(ss: &Sorts, a: &Raw, b: &Raw) -> Option<Raw> {
    let k = a.c.len();
    let ((al, ar), (bl, br)) = (sides(a), sides(b));
    ref_two(ss, a, b, &al, &ar, vec![(al.clone(), shift(&bl, k)), (ar.clone(), shift(&br, k))])
}

pub fn ref_right(ss: &Sorts, a: &Raw) -> Option<Raw> {
    let (_, r) = sides(a);
    ref_one(ss, a, &r, &r)
}

pub fn ref_conv(ss: &Sorts, a: &Raw) -> Raw {
    let (l, r) = sides(a);
    ref_one(ss, a, &r, &l).unwrap_or_else(|| a.clone())
}

/// The representative of a relation; it relates something.
pub fn rep(defs: &[(Name, Def)], p: &Prob) -> Raw {
    normal(&Sorts::new(defs.to_vec()), p).unwrap_or_else(|| panic!("{p:?} relates nothing"))
}

/// The value each variable of a store of `k` variables has in the solved
/// exclusion `b`.
pub fn values(k: usize, b: &Binds) -> Vec<P> {
    (0..k).map(|i| b.iter().find(|(y, _)| *y == i).map_or(pv(i), |(_, q)| q.clone())).collect()
}

/// A representative in the store, its exclusions in the order given or in
/// the opposite order.
pub fn put_rep(f: &mut Fx, r: &Raw, backwards: bool) -> Rep {
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
pub type Shape = (T, T, Vec<Vec<Name>>, Vec<String>);

pub fn sorted<X: Ord>(mut l: Vec<X>) -> Vec<X> {
    l.sort();
    l
}

pub fn shape(r: &Raw) -> Shape {
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

pub fn get_lists(f: &mut Fx, mut p: TermId) -> Vec<Vec<T>> {
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

pub fn get_rep(f: &mut Fx, r: Rep) -> Shape {
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
pub fn dirty(f: &mut Fx) {
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
/// opposite order, with the tables left dirty by earlier work, and with
/// each argument held as itself or as its converse with the mark set.
#[derive(Clone, Copy)]
pub struct Run {
    pub backwards: bool,
    pub soiled: bool,
    pub fa: bool,
    pub fb: bool,
}

/// The runs of an operation on stores, which has no orientation.
pub const PLAIN: [Run; 3] = [
    Run { backwards: false, soiled: false, fa: false, fb: false },
    Run { backwards: true, soiled: false, fa: false, fb: false },
    Run { backwards: false, soiled: true, fa: false, fb: false },
];

pub const RUNS: [Run; 6] = [
    PLAIN[0],
    PLAIN[1],
    PLAIN[2],
    Run { backwards: false, soiled: false, fa: false, fb: true },
    Run { backwards: true, soiled: false, fa: true, fb: false },
    Run { backwards: false, soiled: true, fa: true, fb: true },
];

/// The representative `a` as the machine holds it: its store, or when
/// `flip` the store of its converse with the mark set.
pub fn put_or(f: &mut Fx, ss: &Sorts, a: &Raw, flip: bool, backwards: bool) -> Oriented {
    let rep = if flip { put_rep(f, &ref_conv(ss, a), backwards) } else { put_rep(f, a, backwards) };
    Oriented { rep, flip }
}

/// What the store of a held representative of `want` reads as.
pub fn held(ss: &Sorts, want: &Raw, flip: bool) -> Shape {
    if flip {
        shape(&ref_conv(ss, want))
    } else {
        shape(want)
    }
}

/// The held representative `got` stands for `want`.
pub fn stands(ss: &Sorts, f: &mut Fx, got: Option<Oriented>, want: Option<&Raw>, what: &str) {
    match (got, want) {
        (None, None) => (),
        (Some(o), Some(w)) => assert_eq!(get_rep(f, o.rep), held(ss, w, o.flip), "{what}"),
        (Some(o), None) => panic!("{what}: a representative where there is none: {:?}", get_rep(f, o.rep)),
        (None, Some(w)) => panic!("{what}: nothing where there is {w:?}"),
    }
}

/// Run an operation of one store.
pub fn run_rep<R>(defs: &[(Name, Def)], a: &Raw, run: Run, op: impl FnOnce(&mut Fx, Rep) -> R) -> (R, Fx) {
    let mut f = fixture(defs.to_vec());
    let ra = put_rep(&mut f, a, run.backwards);
    if run.soiled {
        dirty(&mut f);
    }
    let got = op(&mut f, ra);
    f.empty_stack();
    (got, f)
}

/// Run an operation of one representative in the store.
pub fn run1<R>(defs: &[(Name, Def)], a: &Raw, run: Run, op: impl FnOnce(&mut Fx, Oriented) -> R) -> (R, Fx) {
    let ss = Sorts::new(defs.to_vec());
    let mut f = fixture(defs.to_vec());
    let ra = put_or(&mut f, &ss, a, run.fa, run.backwards);
    if run.soiled {
        dirty(&mut f);
    }
    let got = op(&mut f, ra);
    f.empty_stack();
    (got, f)
}

/// Run an operation of two representatives in the store.
pub fn run2<R>(
    defs: &[(Name, Def)],
    a: &Raw,
    b: &Raw,
    run: Run,
    op: impl FnOnce(&mut Fx, Oriented, Oriented) -> R,
) -> (R, Fx) {
    let ss = Sorts::new(defs.to_vec());
    let mut f = fixture(defs.to_vec());
    let ra = put_or(&mut f, &ss, a, run.fa, run.backwards);
    let rb = put_or(&mut f, &ss, b, run.fb, run.backwards);
    if run.soiled {
        dirty(&mut f);
    }
    let got = op(&mut f, ra, rb);
    f.empty_stack();
    (got, f)
}

pub fn read(got: Option<Rep>, mut f: Fx) -> Option<Shape> {
    got.map(|r| get_rep(&mut f, r))
}

/// A list of held representatives as one term, each packed by `dom::pack`.
pub fn put_chain(f: &mut Fx, xs: &[Oriented]) -> TermId {
    let mut l = f.s.alloc(Node::Nil);
    for x in xs.iter().rev() {
        let h = dom::pack(&mut f.s, *x);
        l = f.s.alloc(Node::App(h, l));
    }
    l
}
