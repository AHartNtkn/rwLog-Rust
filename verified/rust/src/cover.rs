//! Coverage by one-way matching, the interfaces of a span, and equality.

use crate::span::Span;
use crate::store::{Frame, Node, Store, Tbl, TermId};
use crate::term::{node_of, unstack};

/// Does the pattern `p`, with its variables bound as table `A` says, match
/// the term `t`? The variables of `t` are rigid. Table `A` holds what each
/// node of the pattern already matched: for a variable that is its binding.
/// A match that succeeds adds to the table.
///
/// An application of the pattern waits on the stack, as a `Build` frame
/// under its two parts, and gets its entry when both parts have matched.
pub fn mmatch(s: &mut Store, p: TermId, t: TermId) -> bool {
    let mut ok = true;
    s.push(Frame::Visit(p, t));
    while let Some(fr) = s.pop() {
        match fr {
            Frame::Visit(q, u) => match s.get(Tbl::A, q) {
                Some(w) => {
                    if !s.same(w, u) {
                        ok = false;
                        s.drop_stack();
                    }
                }
                None => match s.read(q) {
                    Node::App(q1, q2) => match s.read(u) {
                        Node::App(u1, u2) => {
                            s.push(Frame::Build(q, u));
                            s.push(Frame::Visit(q2, u2));
                            s.push(Frame::Visit(q1, u1));
                        }
                        _ => {
                            ok = false;
                            s.drop_stack();
                        }
                    },
                    Node::Sym(_) => {
                        if s.same(q, u) {
                            s.set(Tbl::A, q, u);
                        } else {
                            ok = false;
                            s.drop_stack();
                        }
                    }
                    Node::Nil => {
                        if s.same(q, u) {
                            s.set(Tbl::A, q, u);
                        } else {
                            ok = false;
                            s.drop_stack();
                        }
                    }
                    _ => s.set(Tbl::A, q, u),
                },
            },
            Frame::Build(q, u) => s.set(Tbl::A, q, u),
        }
    }
    ok
}

/// Does `a`, which has no constraints, cover `x`?
pub fn covers_plain(s: &mut Store, a: Span, x: Span) -> bool {
    s.clear(Tbl::A);
    mmatch(s, a.l, x.l) && mmatch(s, a.r, x.r)
}

/// Are the two spans the same, as written? Equal lists are the same node.
pub fn span_eq(s: &mut Store, x: Span, y: Span) -> bool {
    s.same(x.l, y.l) && s.same(x.r, y.r) && s.same(x.c, y.c)
}

/// Flag every node of the term `p` in table `A`.
fn mark(s: &mut Store, p: TermId) {
    s.push(Frame::Visit(p, p));
    while let Some(fr) = s.pop() {
        let q = node_of(fr);
        match s.get_flag(Tbl::A, q) {
            Some(_) => (),
            None => {
                s.set_flag(Tbl::A, q, true);
                if let Node::App(a, b) = s.read(q) {
                    s.push(Frame::Visit(b, b));
                    s.push(Frame::Visit(a, a));
                }
            }
        }
    }
}

/// Is the flag set?
fn is_set(o: Option<bool>) -> bool {
    o.unwrap_or(false)
}

/// Is every variable of the term `p` flagged in table `A`? Table `B` holds
/// the answer for each node already visited.
///
/// An application waits on the stack, as a `Build` frame under its two
/// parts, until both parts have their answer.
fn all_marked(s: &mut Store, p: TermId) -> bool {
    s.push(Frame::Visit(p, p));
    while let Some(fr) = s.pop() {
        match fr {
            Frame::Visit(q, _) => match s.get_flag(Tbl::B, q) {
                Some(_) => (),
                None => match s.read(q) {
                    Node::App(a, b) => {
                        s.push(Frame::Build(q, q));
                        s.push(Frame::Visit(b, b));
                        s.push(Frame::Visit(a, a));
                    }
                    Node::Sym(_) => s.set_flag(Tbl::B, q, true),
                    Node::Nil => s.set_flag(Tbl::B, q, true),
                    _ => {
                        let m = s.get_flag(Tbl::A, q).is_some();
                        s.set_flag(Tbl::B, q, m);
                    }
                },
            },
            Frame::Build(q, _) => match s.read(q) {
                Node::App(a, b) => {
                    let fa = is_set(s.get_flag(Tbl::B, a));
                    let fb = is_set(s.get_flag(Tbl::B, b));
                    s.set_flag(Tbl::B, q, fa && fb);
                }
                _ => panic!(),
            },
        }
    }
    is_set(s.get_flag(Tbl::B, p))
}

/// The members of the list `c` whose variables are all flagged. The first
/// pass decides each member, the second puts the members to keep on the
/// stack, and the third takes them off it in front of the end of the list.
fn keep(s: &mut Store, c: TermId) -> TermId {
    let mut l = c;
    while let Node::App(h, t) = s.read(l) {
        all_marked(s, h);
        l = t;
    }
    let mut l = c;
    while let Node::App(h, t) = s.read(l) {
        if is_set(s.get_flag(Tbl::B, h)) {
            s.push(Frame::Visit(h, h));
        }
        l = t;
    }
    unstack(s, l)
}

fn is_var(s: &mut Store, p: TermId) -> bool {
    matches!(s.read(p), Node::V0 | Node::VL(_) | Node::VR(_))
}

fn is_nil(s: &mut Store, p: TermId) -> bool {
    matches!(s.read(p), Node::Nil)
}

/// The interface at the term `p` of a span with constraints `c`: the span
/// from `p` to `p` with the constraints that only mention variables of `p`.
/// Nothing, when that is a variable with no constraints.
fn iface(s: &mut Store, p: TermId, c: TermId) -> Option<Span> {
    s.clear(Tbl::A);
    mark(s, p);
    s.clear(Tbl::B);
    let c2 = keep(s, c);
    let trivial = is_var(s, p) && is_nil(s, c2);
    if trivial {
        None
    } else {
        Some(Span { l: p, r: p, c: c2 })
    }
}

/// The interface on the right of a span.
pub fn right_bound(s: &mut Store, x: Span) -> Option<Span> {
    iface(s, x.r, x.c)
}

/// The interface on the left of a span.
pub fn left_bound(s: &mut Store, x: Span) -> Option<Span> {
    iface(s, x.l, x.c)
}
