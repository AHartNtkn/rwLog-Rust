//! The sorts as the constraint domain of the engine: the representative of
//! a relation between terms, and the operations of a domain on it.
//!
//! # Representatives
//!
//! A relation has one canonical store whose pattern is a pair, the one
//! `sorts::normal` returns: the pair of its two sides (`Nil` applied to
//! the left side and then to the right side), with the variables numbered
//! in the order they first occur; the list of the conjunctions of the
//! variables, in their order; and the list of the exclusions, each the list
//! of the values of the variables, in their order. It is the folded store
//! (`FoldOf`, `lean/RwLog/Sorts/FoldRaw.lean`) of the `Rep` of
//! `lean/RwLog/Sorts/Rep.lean`. It relates the two sides under every value
//! of the variables in their sorts that no exclusion excludes.
//!
//! A representative (`Oriented`) is a canonical store and a mark. Without
//! the mark it stands for the relation of the store; with the mark it
//! stands for the converse of that relation, the right side of the store
//! related to the left side. So the converse (`swap`) changes the mark and
//! touches no store. The canonical store of a relation is not that of its
//! converse with the sides exchanged, because the variables are numbered
//! from the left side.
//!
//! Every operation states a problem (`Prob` of
//! `lean/RwLog/Sorts/Reduce.lean`) whose solutions are those of its
//! arguments, reading the two sides of each argument as its mark says, and
//! returns the canonical store of that problem without the mark.

pub use crate::sorts::Rep;
use crate::sorts::{among, excls_onto, is_var, normal, places, uncons};
use crate::span::Span;
use crate::store::{Frame, Node, Store, Tbl, TermId};
use crate::term::{node_of, rebuild, Leaf};

/// The sorted patterns that say the pattern `v` is in each sort of the
/// list `c0`, in front of the list `out0`.
fn sorted_onto(s: &mut Store, c0: TermId, v: TermId, out0: TermId) -> TermId {
    let mut out = out0;
    let mut c = c0;
    while let Some((n, rest)) = uncons(s, c) {
        let e = s.alloc(Node::App(n, v));
        out = s.alloc(Node::App(e, out));
        c = rest;
    }
    out
}

/// The sorted patterns that say each variable of the list `vs0` is in each
/// sort of its conjunction in the list `cs0`, in front of the list `out0`.
pub fn atoms_onto(s: &mut Store, cs0: TermId, vs0: TermId, out0: TermId) -> TermId {
    let mut out = out0;
    let mut cs = cs0;
    let mut vs = vs0;
    let mut go = true;
    while go {
        match uncons(s, cs) {
            Some((c, crest)) => match uncons(s, vs) {
                Some((v, vrest)) => {
                    out = sorted_onto(s, c, v, out);
                    cs = crest;
                    vs = vrest;
                }
                None => panic!(),
            },
            None => go = false,
        }
    }
    out
}

/// The two sides of the pair `t`.
fn sides(s: &mut Store, t: TermId) -> (TermId, TermId) {
    match uncons(s, t) {
        Some((h, r)) => match uncons(s, h) {
            Some((_, l)) => (l, r),
            None => panic!(),
        },
        None => panic!(),
    }
}

/// The pair of `u` and `w`.
fn pair(s: &mut Store, u: TermId, w: TermId) -> TermId {
    let nil = s.alloc(Node::Nil);
    let h = s.alloc(Node::App(nil, u));
    s.alloc(Node::App(h, w))
}

/// The representative of the pair of the patterns `u` and `w` under the
/// values of the variables of the representative `a`; nothing when there
/// is no such value. Tables `A` and `B` are used; the stack is empty at
/// entry.
pub fn one(s: &mut Store, decls: TermId, names: TermId, a: Rep, u: TermId, w: TermId) -> Option<Rep> {
    let vs = places(s, a.c);
    let nil = s.alloc(Node::Nil);
    let atoms = atoms_onto(s, a.c, vs, nil);
    let excl = excls_onto(s, vs, a.x, nil);
    let t = pair(s, u, w);
    normal(s, decls, names, t, nil, atoms, excl)
}

/// A canonical store and a mark: the relation of the store, or with the
/// mark its converse.
#[derive(Clone, Copy)]
pub struct Oriented {
    pub rep: Rep,
    pub flip: bool,
}

/// The converse.
pub fn swap(a: Oriented) -> Oriented {
    Oriented { rep: a.rep, flip: !a.flip }
}

/// The representative of the relation of a store, if there is one. It is
/// written without a closure, which the translation to Lean does not take.
#[allow(clippy::manual_map)]
fn unmarked(o: Option<Rep>) -> Option<Oriented> {
    match o {
        Some(rep) => Some(Oriented { rep, flip: false }),
        None => None,
    }
}

/// The left side and the right side of the representative `a`.
fn ends(s: &mut Store, a: Oriented) -> (TermId, TermId) {
    let (l, r) = sides(s, a.rep.t);
    if a.flip {
        (r, l)
    } else {
        (l, r)
    }
}

/// A representative with its variables renamed: its two sides, its
/// variables, their conjunctions and its exclusions.
#[derive(Clone, Copy)]
struct Half {
    l: TermId,
    r: TermId,
    vs: TermId,
    c: TermId,
    x: TermId,
}

/// The representative `a` with each variable replaced as `f` says, its two
/// sides as its mark says. Table
/// `A` is used; the stack is empty at entry.
fn half(s: &mut Store, f: Leaf, a: Oriented) -> Half {
    let vs0 = places(s, a.rep.c);
    s.clear(Tbl::A);
    let t = rebuild(s, f, a.rep.t);
    let vs = rebuild(s, f, vs0);
    let x = rebuild(s, f, a.rep.x);
    let (l0, r0) = sides(s, t);
    let (l, r) = if a.flip { (r0, l0) } else { (l0, r0) };
    Half { l, r, vs, c: a.rep.c, x }
}

/// The representative of the pair `t` under the values of the variables
/// of the two renamed representatives `a` and `b` that satisfy the
/// equations `e`.
fn two(
    s: &mut Store,
    decls: TermId,
    names: TermId,
    a: Half,
    b: Half,
    t: TermId,
    e: TermId,
) -> Option<Rep> {
    let nil = s.alloc(Node::Nil);
    let atoms_b = atoms_onto(s, b.c, b.vs, nil);
    let atoms = atoms_onto(s, a.c, a.vs, atoms_b);
    let excl_b = excls_onto(s, b.vs, b.x, nil);
    let excl = excls_onto(s, a.vs, a.x, excl_b);
    normal(s, decls, names, t, e, atoms, excl)
}

/// Sequential composition: the left side of `a` with the right side of `b`
/// where the right side of `a` is the left side of `b`; nothing when they
/// never are the same. Tables `A` and `B` are used; the stack is empty at
/// entry.
pub fn compose(s: &mut Store, decls: TermId, names: TermId, a: Oriented, b: Oriented) -> Option<Oriented> {
    let ha = half(s, Leaf::Left, a);
    let hb = half(s, Leaf::Right, b);
    let nil = s.alloc(Node::Nil);
    let e0 = s.alloc(Node::App(ha.r, hb.l));
    let e = s.alloc(Node::App(e0, nil));
    let t = pair(s, ha.l, hb.r);
    let o = two(s, decls, names, ha, hb, t, e);
    unmarked(o)
}

/// Conjunction: the pairs both `a` and `b` relate; nothing when there is
/// none. Tables `A` and `B` are used; the stack is empty at entry.
pub fn meet(s: &mut Store, decls: TermId, names: TermId, a: Oriented, b: Oriented) -> Option<Oriented> {
    let ha = half(s, Leaf::Left, a);
    let hb = half(s, Leaf::Right, b);
    let nil = s.alloc(Node::Nil);
    let e2 = s.alloc(Node::App(ha.r, hb.r));
    let r2 = s.alloc(Node::App(e2, nil));
    let e1 = s.alloc(Node::App(ha.l, hb.l));
    let e = s.alloc(Node::App(e1, r2));
    let t = pair(s, ha.l, ha.r);
    let o = two(s, decls, names, ha, hb, t, e);
    unmarked(o)
}

/// The right interface: each right side of `a` related to itself. Tables
/// `A` and `B` are used; the stack is empty at entry.
pub fn right(s: &mut Store, decls: TermId, names: TermId, a: Oriented) -> Option<Oriented> {
    let (_, r) = ends(s, a);
    let o = one(s, decls, names, a.rep, r, r);
    unmarked(o)
}

/// The left interface: each left side of `a` related to itself. Tables
/// `A` and `B` are used; the stack is empty at entry.
pub fn left(s: &mut Store, decls: TermId, names: TermId, a: Oriented) -> Option<Oriented> {
    right(s, decls, names, swap(a))
}

/// The canonical store of the converse of the relation of the store `a`:
/// its right side related to its left side. Tables `A` and `B` are used;
/// the stack is empty at entry.
pub fn conv(s: &mut Store, decls: TermId, names: TermId, a: Rep) -> Rep {
    let (l, r) = sides(s, a.t);
    match one(s, decls, names, a, r, l) {
        Some(b) => b,
        None => a,
    }
}

/// Is the representative an interface: are its two sides the same?
pub fn is_bound(s: &mut Store, a: Oriented) -> bool {
    let (l, r) = sides(s, a.rep.t);
    s.same(l, r)
}

/// Is every member of the list `a0` a member of the list `b0`? Table `B`
/// is used.
fn subset(s: &mut Store, a0: TermId, b0: TermId) -> bool {
    s.clear(Tbl::B);
    let mut b = b0;
    while let Some((p, rest)) = uncons(s, b) {
        s.set_flag(Tbl::B, p, true);
        b = rest;
    }
    let mut all = true;
    let mut a = a0;
    let mut go = true;
    while go {
        match uncons(s, a) {
            Some((p, rest)) => match s.get_flag(Tbl::B, p) {
                Some(_) => a = rest,
                None => {
                    all = false;
                    go = false;
                }
            },
            None => go = false,
        }
    }
    all
}

/// Are the two stores the same: the same pair, the same conjunctions and
/// the same exclusions in any order? Table `B` is used.
pub fn same_rep(s: &mut Store, a: Rep, b: Rep) -> bool {
    if s.same(a.t, b.t) {
        if s.same(a.c, b.c) {
            if subset(s, a.x, b.x) {
                subset(s, b.x, a.x)
            } else {
                false
            }
        } else {
            false
        }
    } else {
        false
    }
}

/// Are the two representatives the same relation? Marked alike, they are
/// when their stores are the same; otherwise the store of the converse of
/// the second is compared. Tables `A` and `B` are used; the stack is empty
/// at entry.
pub fn eq(s: &mut Store, decls: TermId, names: TermId, a: Oriented, b: Oriented) -> bool {
    if a.flip == b.flip {
        same_rep(s, a.rep, b.rep)
    } else {
        let c = conv(s, decls, names, b.rep);
        same_rep(s, a.rep, c)
    }
}

/// Does `a` relate every pair `b` relates: is the conjunction of the two
/// `b`? The conjunction is taken as the store of `b` reads its sides, so
/// it is compared with that store. Tables `A` and `B` are used; the stack
/// is empty at entry.
pub fn covers(s: &mut Store, decls: TermId, names: TermId, a: Oriented, b: Oriented) -> bool {
    let a1 = Oriented { rep: a.rep, flip: a.flip != b.flip };
    let b1 = Oriented { rep: b.rep, flip: false };
    match meet(s, decls, names, a1, b1) {
        Some(m) => same_rep(s, m.rep, b.rep),
        None => false,
    }
}

/// Is the term `p` first-order: is no variable applied anywhere in it?
/// Table `B` flags the nodes already visited; the stack is empty at entry.
fn first_order(s: &mut Store, p: TermId) -> bool {
    let mut ok = true;
    s.clear(Tbl::B);
    s.push(Frame::Visit(p, p));
    while let Some(fr) = s.pop() {
        let q = node_of(fr);
        match s.get_flag(Tbl::B, q) {
            Some(_) => (),
            None => {
                s.set_flag(Tbl::B, q, true);
                if let Node::App(a, b) = s.read(q) {
                    if is_var(s, a) {
                        ok = false;
                        s.drop_stack();
                    } else {
                        s.push(Frame::Visit(b, b));
                        s.push(Frame::Visit(a, a));
                    }
                }
            }
        }
    }
    ok
}

/// Can the term `p` be a constraint: is it first-order and not a variable?
fn is_atom(s: &mut Store, p: TermId) -> bool {
    if is_var(s, p) {
        false
    } else {
        first_order(s, p)
    }
}

/// What a constraint says.
enum Con {
    /// Its argument is in the sort its head names.
    Sort(TermId),
    /// The two terms differ.
    Differ(TermId, TermId),
    /// Nothing that can hold.
    Never,
}

/// What the constraint `c` says, where `ne` is the word of the symbol of
/// disequality: a symbol applied to one term puts the term in the sort of
/// that name; the symbol of disequality applied to two terms says they
/// differ; any other term never holds.
fn con(s: &mut Store, ne: u32, c: TermId) -> Con {
    match s.read(c) {
        Node::App(h, q) => match s.read(h) {
            Node::Sym(_) => Con::Sort(h),
            Node::Nil => Con::Sort(h),
            Node::App(f, p) => match s.read(f) {
                Node::Sym(w) => {
                    if s.word_eq(w, ne) {
                        Con::Differ(p, q)
                    } else {
                        Con::Never
                    }
                }
                _ => Con::Never,
            },
            _ => Con::Never,
        },
        _ => Con::Never,
    }
}

/// The sorted patterns and the exclusions of the list of constraints `c0`;
/// nothing when one of them is not first-order, is a variable, names a sort
/// that is not in the list `names`, or never holds. Table `B` is used; the
/// stack is empty at entry.
fn parts(s: &mut Store, names: TermId, ne: u32, c0: TermId) -> Option<(TermId, TermId)> {
    let nil = s.alloc(Node::Nil);
    let mut atoms = nil;
    let mut excl = nil;
    let mut c = c0;
    let mut ok = true;
    let mut go = true;
    while go {
        match uncons(s, c) {
            Some((k, rest)) => {
                if is_atom(s, k) {
                    match con(s, ne, k) {
                        Con::Sort(h) => {
                            if among(s, h, names) {
                                atoms = s.alloc(Node::App(k, atoms));
                                c = rest;
                            } else {
                                ok = false;
                                go = false;
                            }
                        }
                        Con::Differ(p, q) => {
                            let e = s.alloc(Node::App(p, q));
                            let l = s.alloc(Node::App(e, nil));
                            excl = s.alloc(Node::App(l, excl));
                            c = rest;
                        }
                        Con::Never => {
                            ok = false;
                            go = false;
                        }
                    }
                } else {
                    ok = false;
                    go = false;
                }
            }
            None => go = false,
        }
    }
    if ok {
        Some((atoms, excl))
    } else {
        None
    }
}

/// The representative of the span `x` as written, where `ne` is the word
/// of the symbol of disequality: the normal store of the pair of its two
/// sides under its constraints. Nothing when a side or a constraint is not
/// first-order, a constraint is a variable, or the span relates nothing.
/// Tables `A` and `B` are used; the stack is empty at entry.
pub fn rep(s: &mut Store, decls: TermId, names: TermId, ne: u32, x: Span) -> Option<Oriented> {
    if first_order(s, x.l) {
        if first_order(s, x.r) {
            match parts(s, names, ne, x.c) {
                Some((a, e)) => {
                    let t = pair(s, x.l, x.r);
                    let nil = s.alloc(Node::Nil);
                    let o = normal(s, decls, names, t, nil, a, e);
                    unmarked(o)
                }
                None => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}

/// The mark as a node: `Nil`, or with the mark `Nil` applied to `Nil`.
fn mark(s: &mut Store, flip: bool) -> TermId {
    let nil = s.alloc(Node::Nil);
    if flip {
        s.alloc(Node::App(nil, nil))
    } else {
        nil
    }
}

/// A representative as one node: its mark, `Nil` or with the mark `Nil`
/// applied to `Nil`, applied to its pattern, its conjunctions and its
/// exclusions.
pub fn pack(s: &mut Store, a: Oriented) -> TermId {
    let m = mark(s, a.flip);
    let h = s.alloc(Node::App(m, a.rep.t));
    let g = s.alloc(Node::App(h, a.rep.c));
    s.alloc(Node::App(g, a.rep.x))
}

fn unpack(s: &mut Store, p: TermId) -> Oriented {
    match s.read(p) {
        Node::App(g, x) => match s.read(g) {
            Node::App(h, c) => match s.read(h) {
                Node::App(m, t) => match s.read(m) {
                    Node::Nil => Oriented { rep: Rep { t, c, x }, flip: false },
                    Node::App(_, _) => Oriented { rep: Rep { t, c, x }, flip: true },
                    _ => panic!(),
                },
                _ => panic!(),
            },
            _ => panic!(),
        },
        _ => panic!(),
    }
}

/// Does the chain compose? `xs` is a list of representatives, each packed
/// by `pack`. Tables `A` and `B` are used; the stack is empty at entry.
pub fn composable(s: &mut Store, decls: TermId, names: TermId, xs: TermId) -> bool {
    match s.read(xs) {
        Node::App(h, t) => {
            let mut acc = unpack(s, h);
            let mut rest = t;
            let mut ok = true;
            let mut go = true;
            while go {
                match s.read(rest) {
                    Node::App(h2, t2) => {
                        let y = unpack(s, h2);
                        match compose(s, decls, names, acc, y) {
                            Some(z) => {
                                acc = z;
                                rest = t2;
                            }
                            None => {
                                ok = false;
                                go = false;
                            }
                        }
                    }
                    _ => go = false,
                }
            }
            ok
        }
        _ => true,
    }
}
