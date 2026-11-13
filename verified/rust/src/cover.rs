//! Coverage by one-way matching, the interfaces of a span, and equality.

use crate::span::Span;
use crate::store::{Node, Store, Tbl, TermId};

/// Does the pattern `p`, with its variables bound as table `A` says, match
/// the term `t`? The variables of `t` are rigid. Table `A` holds what each
/// node of the pattern already matched: for a variable that is its binding.
/// A match that succeeds adds to the table.
pub fn mmatch(s: &mut Store, p: TermId, t: TermId) -> bool {
    match s.get(Tbl::A, p) {
        Some(u) => s.same(u, t),
        None => {
            let ok = match s.read(p) {
                Node::V0 => true,
                Node::VL(_) => true,
                Node::VR(_) => true,
                Node::Sym(_) => s.same(p, t),
                Node::Nil => s.same(p, t),
                Node::App(p1, p2) => match s.read(t) {
                    Node::App(t1, t2) => mmatch(s, p1, t1) && mmatch(s, p2, t2),
                    _ => false,
                },
            };
            if ok {
                s.set(Tbl::A, p, t);
            }
            ok
        }
    }
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

/// Flag every node of the term `p` in table `A`. A variable is not entered.
fn mark(s: &mut Store, p: TermId) {
    match s.get_flag(Tbl::A, p) {
        Some(_) => (),
        None => {
            s.set_flag(Tbl::A, p, true);
            if let Node::App(a, b) = s.read(p) {
                mark(s, a);
                mark(s, b);
            }
        }
    }
}

/// Is every variable of the term `p` flagged in table `A`? Table `B` holds
/// the answer for each node already visited.
fn all_marked(s: &mut Store, p: TermId) -> bool {
    match s.get_flag(Tbl::B, p) {
        Some(b) => b,
        None => {
            let b = match s.read(p) {
                Node::V0 => s.get_flag(Tbl::A, p).is_some(),
                Node::VL(_) => s.get_flag(Tbl::A, p).is_some(),
                Node::VR(_) => s.get_flag(Tbl::A, p).is_some(),
                Node::Sym(_) => true,
                Node::Nil => true,
                Node::App(a, c) => all_marked(s, a) && all_marked(s, c),
            };
            s.set_flag(Tbl::B, p, b);
            b
        }
    }
}

/// The members of the list `c` whose variables are all flagged.
fn keep(s: &mut Store, c: TermId) -> TermId {
    match s.read(c) {
        Node::App(h, t) => {
            let r = keep(s, t);
            if all_marked(s, h) {
                s.alloc(Node::App(h, r))
            } else {
                r
            }
        }
        _ => c,
    }
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
