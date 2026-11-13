//! Composition and conjunction of spans, by two-sided matching.

use crate::store::{Node, Store, Tbl, TermId};
use crate::term::{append, occurs, rebuild, Leaf};

/// A span: its two terms and the list of its constraints.
#[derive(Clone, Copy)]
pub struct Span {
    pub l: TermId,
    pub r: TermId,
    pub c: TermId,
}

/// What to do with an equation.
pub enum Act {
    /// The two sides are the same term.
    Skip,
    /// No substitution makes them equal.
    Fail,
    /// Two applications: equate the first parts, and the second parts.
    Split(TermId, TermId, TermId, TermId),
    /// Replace the variable by the term.
    Elim(TermId, TermId),
}

/// What a node is, for the purpose of solving an equation.
enum Kind {
    Var,
    Atom,
    App(TermId, TermId),
}

fn kind(s: &mut Store, p: TermId) -> Kind {
    match s.read(p) {
        Node::V0 => Kind::Var,
        Node::VL(_) => Kind::Var,
        Node::VR(_) => Kind::Var,
        Node::Sym(_) => Kind::Atom,
        Node::Nil => Kind::Atom,
        Node::App(a, b) => Kind::App(a, b),
    }
}

/// Decide what to do with the equation between `p` and `q`. Two different
/// identifiers are different terms, so two symbols need no comparison.
pub fn act(s: &mut Store, p: TermId, q: TermId) -> Act {
    if s.same(p, q) {
        Act::Skip
    } else {
        match kind(s, p) {
            Kind::Var => match kind(s, q) {
                Kind::App(_, _) => {
                    s.clear(Tbl::B);
                    if occurs(s, p, q) {
                        Act::Fail
                    } else {
                        Act::Elim(p, q)
                    }
                }
                _ => Act::Elim(p, q),
            },
            Kind::Atom => match kind(s, q) {
                Kind::Var => Act::Elim(q, p),
                _ => Act::Fail,
            },
            Kind::App(a, b) => match kind(s, q) {
                Kind::Var => {
                    s.clear(Tbl::B);
                    if occurs(s, q, p) {
                        Act::Fail
                    } else {
                        Act::Elim(q, p)
                    }
                }
                Kind::Atom => Act::Fail,
                Kind::App(c, d) => Act::Split(a, c, b, d),
            },
        }
    }
}

/// Solve the equations of the list `eqs` (each an application of its two
/// sides). The result says whether there is a solution, and if so holds
/// `out` with the solution applied. Eliminating a variable rebuilds the
/// equations that are left and `out`, sharing one table.
pub fn solve_into(s: &mut Store, eqs0: TermId, out0: TermId) -> (bool, TermId) {
    let mut eqs = eqs0;
    let mut out = out0;
    let mut ok = true;
    let mut go = true;
    while go {
        match s.read(eqs) {
            Node::App(e, rest) => match s.read(e) {
                Node::App(p, q) => match act(s, p, q) {
                    Act::Skip => eqs = rest,
                    Act::Fail => {
                        ok = false;
                        go = false;
                    }
                    Act::Split(a, c, b, d) => {
                        let e2 = s.alloc(Node::App(b, d));
                        let r2 = s.alloc(Node::App(e2, rest));
                        let e1 = s.alloc(Node::App(a, c));
                        eqs = s.alloc(Node::App(e1, r2));
                    }
                    Act::Elim(x, u) => {
                        s.clear(Tbl::A);
                        eqs = rebuild(s, Leaf::Sub(x, u), rest);
                        out = rebuild(s, Leaf::Sub(x, u), out);
                    }
                },
                _ => panic!(),
            },
            _ => go = false,
        }
    }
    (ok, out)
}

fn rename(s: &mut Store, f: Leaf, x: Span) -> Span {
    s.clear(Tbl::A);
    let l = rebuild(s, f, x.l);
    let r = rebuild(s, f, x.r);
    let c = rebuild(s, f, x.c);
    Span { l, r, c }
}

/// A span as one node.
pub fn pack_span(s: &mut Store, x: Span) -> TermId {
    pack(s, x.l, x.r, x.c)
}

fn pack(s: &mut Store, l: TermId, r: TermId, c: TermId) -> TermId {
    let rc = s.alloc(Node::App(r, c));
    s.alloc(Node::App(l, rc))
}

fn unpack(s: &mut Store, o: TermId) -> Span {
    match s.read(o) {
        Node::App(l, rc) => match s.read(rc) {
            Node::App(r, c) => Span { l, r, c },
            _ => panic!(),
        },
        _ => panic!(),
    }
}

fn finish(s: &mut Store, eqs: TermId, out: TermId) -> Option<Span> {
    let (ok, o) = solve_into(s, eqs, out);
    if ok {
        Some(unpack(s, o))
    } else {
        None
    }
}

/// Sequential composition: match the right of `x` against the left of `y`.
pub fn compose(s: &mut Store, x: Span, y: Span) -> Option<Span> {
    let a = rename(s, Leaf::Left, x);
    let b = rename(s, Leaf::Right, y);
    let c = append(s, a.c, b.c);
    let out = pack(s, a.l, b.r, c);
    let nil = s.alloc(Node::Nil);
    let e = s.alloc(Node::App(a.r, b.l));
    let eqs = s.alloc(Node::App(e, nil));
    finish(s, eqs, out)
}

/// Conjunction: match both sides.
pub fn meet(s: &mut Store, x: Span, y: Span) -> Option<Span> {
    let a = rename(s, Leaf::Left, x);
    let b = rename(s, Leaf::Right, y);
    let c = append(s, a.c, b.c);
    let out = pack(s, a.l, a.r, c);
    let nil = s.alloc(Node::Nil);
    let e2 = s.alloc(Node::App(a.r, b.r));
    let r2 = s.alloc(Node::App(e2, nil));
    let e1 = s.alloc(Node::App(a.l, b.l));
    let eqs = s.alloc(Node::App(e1, r2));
    finish(s, eqs, out)
}

/// Does the chain compose? `xs` is a list of spans, each packed by
/// `pack_span`.
pub fn composable(s: &mut Store, xs: TermId) -> bool {
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
                        match compose(s, acc, y) {
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
