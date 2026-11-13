//! Sorts: the declarations of a program in the store, and membership.
//!
//! # Declarations in the store
//!
//! The name of a sort is a symbol. *A sort or any term* is the name, or
//! `Nil` for any term. The sorts of a program are a list of declarations:
//!
//! ```text
//! declaration := App(name, App(cases, rest))
//! cases       := list of App(symbol, list of (sort or any term))
//! rest        := Nil                                  no other symbol
//!              | App(list of exclusion, sort or any term)
//! exclusion   := App(symbol, list with one member for each argument)
//! ```
//!
//! This is `Sorts` of `lean/RwLog/Trusted/Syntax.lean`. A number of
//! arguments is the length of a list, so two of them are compared by walking
//! the two lists together.

use crate::store::{Frame, Node, Store, Tbl, TermId};

/// The symbol at the head of a term and the list of its arguments, in
/// order.
pub fn spine(s: &mut Store, t: TermId) -> (TermId, TermId) {
    let mut args = s.alloc(Node::Nil);
    let mut h = t;
    while let Node::App(g, u) = s.read(h) {
        args = s.alloc(Node::App(u, args));
        h = g;
    }
    (h, args)
}

/// Have the two lists the same length?
pub fn same_len(s: &mut Store, a0: TermId, b0: TermId) -> bool {
    let mut a = a0;
    let mut b = b0;
    let mut same = true;
    let mut go = true;
    while go {
        match s.read(a) {
            Node::App(_, ta) => match s.read(b) {
                Node::App(_, tb) => {
                    a = ta;
                    b = tb;
                }
                _ => {
                    same = false;
                    go = false;
                }
            },
            _ => {
                go = false;
                match s.read(b) {
                    Node::App(_, _) => same = false,
                    _ => (),
                }
            }
        }
    }
    same
}

/// The second part of the first member of the list whose first part is
/// `key` and whose second part is a list as long as `args`.
fn find(s: &mut Store, list0: TermId, key: TermId, args: TermId) -> Option<TermId> {
    let mut list = list0;
    let mut found = None;
    let mut go = true;
    while go {
        match s.read(list) {
            Node::App(e, rest) => match s.read(e) {
                Node::App(k, v) => {
                    if s.same(k, key) && same_len(s, v, args) {
                        found = Some(v);
                        go = false;
                    } else {
                        list = rest;
                    }
                }
                _ => panic!(),
            },
            _ => go = false,
        }
    }
    found
}

/// The declaration of the sort `name`: its cases and its rest.
pub fn lookup(s: &mut Store, sorts0: TermId, name: TermId) -> Option<(TermId, TermId)> {
    let mut sorts = sorts0;
    let mut found = None;
    let mut go = true;
    while go {
        match s.read(sorts) {
            Node::App(e, more) => match s.read(e) {
                Node::App(n, d) => {
                    if s.same(n, name) {
                        match s.read(d) {
                            Node::App(cases, rest) => found = Some((cases, rest)),
                            _ => panic!(),
                        }
                        go = false;
                    } else {
                        sorts = more;
                    }
                }
                _ => panic!(),
            },
            _ => go = false,
        }
    }
    found
}

/// A list with `kid` for each member of `args`.
fn fill(s: &mut Store, args0: TermId, kid: TermId) -> TermId {
    let mut out = s.alloc(Node::Nil);
    let mut args = args0;
    while let Node::App(_, t) = s.read(args) {
        out = s.alloc(Node::App(kid, out));
        args = t;
    }
    out
}

/// One step of the sort `name` on a term with the symbol `head` and the
/// arguments `args`: the sort of each argument, or nothing when the sort has
/// no term with that symbol and that number of arguments. A name with no
/// declaration is the empty sort.
pub fn step(s: &mut Store, sorts: TermId, name: TermId, head: TermId, args: TermId) -> Option<TermId> {
    match lookup(s, sorts, name) {
        None => None,
        Some((cases, rest)) => match find(s, cases, head, args) {
            Some(kids) => Some(kids),
            None => match s.read(rest) {
                Node::App(excluded, kid) => match find(s, excluded, head, args) {
                    Some(_) => None,
                    None => Some(fill(s, args, kid)),
                },
                _ => None,
            },
        },
    }
}

/// Is the ground term `t` in the sort `name`? Table `B` flags each pair of a
/// sort and a term already asked about, so a term that occurs many times is
/// read once for each sort. Clear it before the call.
///
/// A pair still to do waits on the stack as a `Visit` frame.
pub fn member(s: &mut Store, sorts: TermId, name: TermId, t: TermId) -> bool {
    let mut ok = true;
    s.push(Frame::Visit(name, t));
    while let Some(fr) = s.pop() {
        match fr {
            Frame::Visit(n, u) => {
                let pair = s.alloc(Node::App(n, u));
                match s.get_flag(Tbl::B, pair) {
                    Some(_) => (),
                    None => {
                        s.set_flag(Tbl::B, pair, true);
                        let (head, args) = spine(s, u);
                        match step(s, sorts, n, head, args) {
                            None => {
                                ok = false;
                                s.drop_stack();
                            }
                            Some(kids) => push_args(s, kids, args),
                        }
                    }
                }
            }
            Frame::Build(_, _) => panic!(),
        }
    }
    ok
}

/// Put on the stack each argument with the sort it must be in. An argument
/// that may be any term is left out. The two lists have the same length.
fn push_args(s: &mut Store, kids0: TermId, args0: TermId) {
    let mut kids = kids0;
    let mut args = args0;
    let mut go = true;
    while go {
        match s.read(kids) {
            Node::App(k, kt) => match s.read(args) {
                Node::App(a, at) => {
                    match s.read(k) {
                        Node::Nil => (),
                        _ => s.push(Frame::Visit(k, a)),
                    }
                    kids = kt;
                    args = at;
                }
                _ => panic!(),
            },
            _ => go = false,
        }
    }
}
