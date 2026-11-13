//! Copying a term with its variables replaced, and the occurs check.

use crate::store::{Node, Store, Tbl, TermId};

/// What a variable becomes when a term is rebuilt.
#[derive(Clone, Copy)]
pub enum Leaf {
    /// The variable `v` becomes `2 v`.
    Left,
    /// The variable `v` becomes `2 v + 1`.
    Right,
    /// The variable `x` becomes the term `u`; any other stays.
    Sub(TermId, TermId),
}

fn leaf(s: &mut Store, f: Leaf, p: TermId) -> TermId {
    match f {
        Leaf::Left => s.alloc(Node::VL(p)),
        Leaf::Right => s.alloc(Node::VR(p)),
        Leaf::Sub(x, u) => {
            if s.same(p, x) {
                u
            } else {
                p
            }
        }
    }
}

/// The term `p` with each variable replaced as `f` says. Table `A` holds
/// what each node already visited became, so a node that occurs many times
/// is rebuilt once. Clear the table before the first call with a given `f`.
pub fn rebuild(s: &mut Store, f: Leaf, p: TermId) -> TermId {
    match s.get(Tbl::A, p) {
        Some(r) => r,
        None => {
            let r = match s.read(p) {
                Node::V0 => leaf(s, f, p),
                Node::VL(_) => leaf(s, f, p),
                Node::VR(_) => leaf(s, f, p),
                Node::Sym(_) => p,
                Node::Nil => p,
                Node::App(a, b) => {
                    let ra = rebuild(s, f, a);
                    let rb = rebuild(s, f, b);
                    s.alloc(Node::App(ra, rb))
                }
            };
            s.set(Tbl::A, p, r);
            r
        }
    }
}

/// Does the variable `x` occur in the term `p`? Table `B` holds the answer
/// for each node already visited. Clear it before the first call with a
/// given `x`.
pub fn occurs(s: &mut Store, x: TermId, p: TermId) -> bool {
    match s.get_flag(Tbl::B, p) {
        Some(b) => b,
        None => {
            let b = match s.read(p) {
                Node::V0 => s.same(p, x),
                Node::VL(_) => s.same(p, x),
                Node::VR(_) => s.same(p, x),
                Node::Sym(_) => false,
                Node::Nil => false,
                Node::App(a, c) => occurs(s, x, a) || occurs(s, x, c),
            };
            s.set_flag(Tbl::B, p, b);
            b
        }
    }
}

/// The list `a` followed by the list `b`.
pub fn append(s: &mut Store, a: TermId, b: TermId) -> TermId {
    match s.read(a) {
        Node::App(h, t) => {
            let r = append(s, t, b);
            s.alloc(Node::App(h, r))
        }
        _ => b,
    }
}
