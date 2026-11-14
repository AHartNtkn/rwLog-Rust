//! Copying a term with its variables replaced, and the occurs check.

use crate::store::{Frame, Node, Store, Tbl, TermId};

/// What a variable becomes when a term is rebuilt.
#[derive(Clone, Copy)]
pub enum Leaf {
    /// The variable `v` becomes `2 v`.
    Left,
    /// The variable `v` becomes `2 v + 1`.
    Right,
    /// The variable `x` becomes the term `u`; any other stays.
    Sub(TermId, TermId),
    /// A variable with an entry in table `B` becomes that entry; any other
    /// stays.
    Map,
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
        Leaf::Map => match s.get(Tbl::B, p) {
            Some(u) => u,
            None => p,
        },
    }
}

/// The node a frame names.
pub fn node_of(fr: Frame) -> TermId {
    match fr {
        Frame::Visit(q, _) => q,
        Frame::Build(q, _) => q,
    }
}

/// The term `p` with each variable replaced as `f` says. Table `A` holds
/// what each node already visited became, so a node that occurs many times
/// is rebuilt once. Clear the table before the first call with a given `f`.
///
/// An application waits on the stack, as a `Build` frame under its two
/// parts, until both parts have an entry in the table.
pub fn rebuild(s: &mut Store, f: Leaf, p: TermId) -> TermId {
    s.push(Frame::Visit(p, p));
    while let Some(fr) = s.pop() {
        match fr {
            Frame::Visit(q, _) => match s.get(Tbl::A, q) {
                Some(_) => (),
                None => match s.read(q) {
                    Node::App(a, b) => {
                        s.push(Frame::Build(q, q));
                        s.push(Frame::Visit(b, b));
                        s.push(Frame::Visit(a, a));
                    }
                    Node::Sym(_) => s.set(Tbl::A, q, q),
                    Node::Nil => s.set(Tbl::A, q, q),
                    _ => {
                        let r = leaf(s, f, q);
                        s.set(Tbl::A, q, r);
                    }
                },
            },
            Frame::Build(q, _) => match s.read(q) {
                Node::App(a, b) => match s.get(Tbl::A, a) {
                    Some(ra) => match s.get(Tbl::A, b) {
                        Some(rb) => {
                            let r = s.alloc(Node::App(ra, rb));
                            s.set(Tbl::A, q, r);
                        }
                        None => panic!(),
                    },
                    None => panic!(),
                },
                _ => panic!(),
            },
        }
    }
    match s.get(Tbl::A, p) {
        Some(r) => r,
        None => panic!(),
    }
}

/// Does the variable `x` occur in the term `p`? Table `B` flags the nodes
/// already visited. Clear it before the call.
pub fn occurs(s: &mut Store, x: TermId, p: TermId) -> bool {
    let mut found = false;
    s.push(Frame::Visit(p, p));
    while let Some(fr) = s.pop() {
        let q = node_of(fr);
        match s.get_flag(Tbl::B, q) {
            Some(_) => (),
            None => {
                s.set_flag(Tbl::B, q, true);
                match s.read(q) {
                    Node::App(a, b) => {
                        s.push(Frame::Visit(b, b));
                        s.push(Frame::Visit(a, a));
                    }
                    Node::Sym(_) => (),
                    Node::Nil => (),
                    _ => {
                        if s.same(q, x) {
                            found = true;
                            s.drop_stack();
                        }
                    }
                }
            }
        }
    }
    found
}

/// The nodes on the stack as a list in front of the list `r`: the node at
/// the top of the stack comes last. The stack is left empty.
pub fn unstack(s: &mut Store, r: TermId) -> TermId {
    let mut r = r;
    while let Some(fr) = s.pop() {
        r = s.alloc(Node::App(node_of(fr), r));
    }
    r
}

/// The list `a` followed by the list `b`. The members of `a` go on the
/// stack, and come off it in front of `b`.
pub fn append(s: &mut Store, a: TermId, b: TermId) -> TermId {
    let mut l = a;
    while let Node::App(h, t) = s.read(l) {
        s.push(Frame::Visit(h, h));
        l = t;
    }
    unstack(s, b)
}
