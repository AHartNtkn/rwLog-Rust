//! The sorts as the constraint domain of the engine: the representative of
//! a relation between terms, and the operations of a domain on it.
//!
//! # Representatives
//!
//! A representative is a normal store whose pattern is a pair, as
//! `sorts::normal` returns it: the pair of its two sides (`Nil` applied to
//! the left side and then to the right side), with the variables numbered
//! in the order they first occur; the list of the conjunctions of the
//! variables, in their order; and the list of the exclusions, each the list
//! of the values of the variables, in their order. This is `Rep` of
//! `lean/RwLog/Sorts/Rep.lean`. It relates the two sides under every value
//! of the variables in their sorts that no exclusion excludes.
//!
//! Every operation states a problem (`Prob` of
//! `lean/RwLog/Sorts/Reduce.lean`) whose solutions are those of its
//! arguments, and returns the normal store of that problem.

pub use crate::sorts::Rep;
use crate::sorts::{is_var, normal, places, rev_onto, uncons};
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

/// The equations of each variable of the list `vs0` with its value in the
/// list `vals0`, in order.
fn eqns_of(s: &mut Store, vs0: TermId, vals0: TermId) -> TermId {
    let nil = s.alloc(Node::Nil);
    let mut out = nil;
    let mut vs = vs0;
    let mut l = vals0;
    let mut go = true;
    while go {
        match uncons(s, vs) {
            Some((v, vrest)) => match uncons(s, l) {
                Some((p, lrest)) => {
                    let e = s.alloc(Node::App(v, p));
                    out = s.alloc(Node::App(e, out));
                    vs = vrest;
                    l = lrest;
                }
                None => panic!(),
            },
            None => go = false,
        }
    }
    rev_onto(s, out, nil)
}

/// Each solved exclusion of the list `xs0` as the list of the equations of
/// each variable of the list `vs` with its value, in front of the list
/// `out0`.
pub fn excls_onto(s: &mut Store, vs: TermId, xs0: TermId, out0: TermId) -> TermId {
    let mut out = out0;
    let mut xs = xs0;
    while let Some((vals, rest)) = uncons(s, xs) {
        let e = eqns_of(s, vs, vals);
        out = s.alloc(Node::App(e, out));
        xs = rest;
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

/// The representative `a` with each variable replaced as `f` says. Table
/// `A` is used; the stack is empty at entry.
fn half(s: &mut Store, f: Leaf, a: Rep) -> Half {
    let vs0 = places(s, a.c);
    s.clear(Tbl::A);
    let t = rebuild(s, f, a.t);
    let vs = rebuild(s, f, vs0);
    let x = rebuild(s, f, a.x);
    let (l, r) = sides(s, t);
    Half { l, r, vs, c: a.c, x }
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
pub fn compose(s: &mut Store, decls: TermId, names: TermId, a: Rep, b: Rep) -> Option<Rep> {
    let ha = half(s, Leaf::Left, a);
    let hb = half(s, Leaf::Right, b);
    let nil = s.alloc(Node::Nil);
    let e0 = s.alloc(Node::App(ha.r, hb.l));
    let e = s.alloc(Node::App(e0, nil));
    let t = pair(s, ha.l, hb.r);
    two(s, decls, names, ha, hb, t, e)
}

/// Conjunction: the pairs both `a` and `b` relate; nothing when there is
/// none. Tables `A` and `B` are used; the stack is empty at entry.
pub fn meet(s: &mut Store, decls: TermId, names: TermId, a: Rep, b: Rep) -> Option<Rep> {
    let ha = half(s, Leaf::Left, a);
    let hb = half(s, Leaf::Right, b);
    let nil = s.alloc(Node::Nil);
    let e2 = s.alloc(Node::App(ha.r, hb.r));
    let r2 = s.alloc(Node::App(e2, nil));
    let e1 = s.alloc(Node::App(ha.l, hb.l));
    let e = s.alloc(Node::App(e1, r2));
    let t = pair(s, ha.l, ha.r);
    two(s, decls, names, ha, hb, t, e)
}

/// The right interface: each right side of `a` related to itself. Tables
/// `A` and `B` are used; the stack is empty at entry.
pub fn right(s: &mut Store, decls: TermId, names: TermId, a: Rep) -> Option<Rep> {
    let (_, r) = sides(s, a.t);
    one(s, decls, names, a, r, r)
}

/// The converse: the right side of `a` related to its left side. Tables
/// `A` and `B` are used; the stack is empty at entry.
pub fn conv(s: &mut Store, decls: TermId, names: TermId, a: Rep) -> Rep {
    let (l, r) = sides(s, a.t);
    match one(s, decls, names, a, r, l) {
        Some(b) => b,
        None => a,
    }
}

/// Is the representative an interface: are its two sides the same?
pub fn is_bound(s: &mut Store, a: Rep) -> bool {
    let (l, r) = sides(s, a.t);
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

/// Are the two representatives the same: the same pair, the same
/// conjunctions and the same exclusions in any order? Table `B` is used.
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

/// Does `a` relate every pair `b` relates: is the conjunction of the two
/// `b`? Tables `A` and `B` are used; the stack is empty at entry.
pub fn covers(s: &mut Store, decls: TermId, names: TermId, a: Rep, b: Rep) -> bool {
    match meet(s, decls, names, a, b) {
        Some(m) => same_rep(s, m, b),
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

/// Is `n` a member of the list `l0`?
fn among(s: &mut Store, n: TermId, l0: TermId) -> bool {
    let mut found = false;
    let mut l = l0;
    let mut go = true;
    while go {
        match uncons(s, l) {
            Some((m, rest)) => {
                if s.same(m, n) {
                    found = true;
                    go = false;
                } else {
                    l = rest;
                }
            }
            None => go = false,
        }
    }
    found
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
pub fn rep(s: &mut Store, decls: TermId, names: TermId, ne: u32, x: Span) -> Option<Rep> {
    if first_order(s, x.l) {
        if first_order(s, x.r) {
            match parts(s, names, ne, x.c) {
                Some((a, e)) => {
                    let t = pair(s, x.l, x.r);
                    let nil = s.alloc(Node::Nil);
                    normal(s, decls, names, t, nil, a, e)
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
