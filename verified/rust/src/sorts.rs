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
use crate::term::unstack;

/// The first member of a list and the rest, or nothing when the node is not
/// an application. One tick.
pub fn uncons(s: &mut Store, l: TermId) -> Option<(TermId, TermId)> {
    match s.read(l) {
        Node::App(h, t) => Some((h, t)),
        _ => None,
    }
}

/// The symbol at the head of a term and the list of its arguments, in
/// order.
pub fn spine(s: &mut Store, t: TermId) -> (TermId, TermId) {
    let mut args = s.alloc(Node::Nil);
    let mut h = t;
    while let Some((g, u)) = uncons(s, h) {
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
        match uncons(s, a) {
            Some((_, ta)) => match uncons(s, b) {
                Some((_, tb)) => {
                    a = ta;
                    b = tb;
                }
                None => {
                    same = false;
                    go = false;
                }
            },
            None => {
                go = false;
                same = uncons(s, b).is_none();
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
        match uncons(s, list) {
            Some((e, rest)) => match uncons(s, e) {
                Some((k, v)) => {
                    if s.same(k, key) && same_len(s, v, args) {
                        found = Some(v);
                        go = false;
                    } else {
                        list = rest;
                    }
                }
                None => panic!(),
            },
            None => go = false,
        }
    }
    found
}

/// The declaration of the sort `name`: its cases and its rest.
pub fn lookup(s: &mut Store, decls0: TermId, name: TermId) -> Option<(TermId, TermId)> {
    let mut decls = decls0;
    let mut found = None;
    let mut go = true;
    while go {
        match uncons(s, decls) {
            Some((e, more)) => match uncons(s, e) {
                Some((n, d)) => {
                    if s.same(n, name) {
                        match uncons(s, d) {
                            Some(def) => found = Some(def),
                            None => panic!(),
                        }
                        go = false;
                    } else {
                        decls = more;
                    }
                }
                None => panic!(),
            },
            None => go = false,
        }
    }
    found
}

/// A list with `kid` for each member of `args`.
fn fill(s: &mut Store, args0: TermId, kid: TermId) -> TermId {
    let mut out = s.alloc(Node::Nil);
    let mut args = args0;
    while let Some((_, t)) = uncons(s, args) {
        out = s.alloc(Node::App(kid, out));
        args = t;
    }
    out
}

/// One step of the sort `name` on a term with the symbol `head` and the
/// arguments `args`: the sort of each argument, or nothing when the sort has
/// no term with that symbol and that number of arguments. A name with no
/// declaration is the empty sort.
pub fn step(s: &mut Store, decls: TermId, name: TermId, head: TermId, args: TermId) -> Option<TermId> {
    match lookup(s, decls, name) {
        None => None,
        Some((cases, rest)) => match find(s, cases, head, args) {
            Some(kids) => Some(kids),
            None => match uncons(s, rest) {
                Some((excluded, kid)) => match find(s, excluded, head, args) {
                    Some(_) => None,
                    None => Some(fill(s, args, kid)),
                },
                None => None,
            },
        },
    }
}

/// Is the node the end of a list?
fn is_nil(s: &mut Store, p: TermId) -> bool {
    matches!(s.read(p), Node::Nil)
}

/// Put on the stack each argument with the sort it must be in. An argument
/// that may be any term is left out. The two lists have the same length.
fn push_args(s: &mut Store, kids0: TermId, args0: TermId) {
    let mut kids = kids0;
    let mut args = args0;
    while let Some((k, kt)) = uncons(s, kids) {
        match uncons(s, args) {
            Some((a, at)) => {
                if !is_nil(s, k) {
                    s.push(Frame::Visit(k, a));
                }
                kids = kt;
                args = at;
            }
            None => panic!(),
        }
    }
}

/// Is the ground term `t` in the sort `name`? Table `B` flags each pair of a
/// sort and a term already asked about, so a term that occurs many times is
/// read once for each sort. Clear it before the call.
///
/// A pair still to do waits on the stack as a `Visit` frame.
pub fn member(s: &mut Store, decls: TermId, name: TermId, t: TermId) -> bool {
    let mut ok = true;
    s.push(Frame::Visit(name, t));
    while let Some(fr) = s.pop() {
        let (n, u) = match fr {
            Frame::Visit(n, u) => (n, u),
            Frame::Build(n, u) => (n, u),
        };
        let pair = s.alloc(Node::App(n, u));
        match s.get_flag(Tbl::B, pair) {
            Some(_) => (),
            None => {
                s.set_flag(Tbl::B, pair, true);
                let (head, args) = spine(s, u);
                match step(s, decls, n, head, args) {
                    None => {
                        ok = false;
                        s.drop_stack();
                    }
                    Some(kids) => push_args(s, kids, args),
                }
            }
        }
    }
    ok
}

/// Put the name `n` in front of the list `acc` unless table `A` flags it,
/// and flag it. Any term is not a name and is left out.
fn note(s: &mut Store, acc: TermId, n: TermId) -> TermId {
    if is_nil(s, n) {
        acc
    } else {
        match s.get_flag(Tbl::A, n) {
            Some(_) => acc,
            None => {
                s.set_flag(Tbl::A, n, true);
                s.alloc(Node::App(n, acc))
            }
        }
    }
}

/// `note` each sort of the list `kids0`.
fn note_kids(s: &mut Store, acc0: TermId, kids0: TermId) -> TermId {
    let mut acc = acc0;
    let mut kids = kids0;
    while let Some((k, t)) = uncons(s, kids) {
        acc = note(s, acc, k);
        kids = t;
    }
    acc
}

/// `note` each sort the cases give an argument.
fn note_cases(s: &mut Store, acc0: TermId, cases0: TermId) -> TermId {
    let mut acc = acc0;
    let mut cases = cases0;
    while let Some((e, t)) = uncons(s, cases) {
        match uncons(s, e) {
            Some((_, kids)) => acc = note_kids(s, acc, kids),
            None => panic!(),
        }
        cases = t;
    }
    acc
}

/// Every name the declarations declare or say of an argument, each once:
/// the first to occur comes last. Table `A` flags the names already seen.
pub fn names(s: &mut Store, decls0: TermId) -> TermId {
    s.clear(Tbl::A);
    let mut acc = s.alloc(Node::Nil);
    let mut decls = decls0;
    while let Some((e, more)) = uncons(s, decls) {
        match uncons(s, e) {
            Some((n, d)) => match uncons(s, d) {
                Some((cases, rest)) => {
                    acc = note(s, acc, n);
                    acc = note_cases(s, acc, cases);
                    if let Some((_, kid)) = uncons(s, rest) {
                        acc = note(s, acc, kid);
                    }
                }
                None => panic!(),
            },
            None => panic!(),
        }
        decls = more;
    }
    acc
}

/// Flag in table `A` each member of the list.
fn mark(s: &mut Store, list0: TermId) {
    let mut list = list0;
    while let Some((h, t)) = uncons(s, list) {
        s.set_flag(Tbl::A, h, true);
        list = t;
    }
}

/// The members of `names0` that table `A` flags, the first last.
fn pick(s: &mut Store, names0: TermId) -> TermId {
    let mut out = s.alloc(Node::Nil);
    let mut names = names0;
    while let Some((h, t)) = uncons(s, names) {
        out = match s.get_flag(Tbl::A, h) {
            Some(_) => s.alloc(Node::App(h, out)),
            None => out,
        };
        names = t;
    }
    out
}

/// The conjunction of the sorts in the list `list`, whose members are
/// members of `names`: its members once each, in the order of `names` from
/// its end. So one set of sorts is one node. Table `A` flags the members.
pub fn conj_of(s: &mut Store, names: TermId, list: TermId) -> TermId {
    s.clear(Tbl::A);
    mark(s, list);
    pick(s, names)
}

/// The conjunction of two conjunctions: the sorts of either.
pub fn conj_meet(s: &mut Store, names: TermId, a: TermId, b: TermId) -> TermId {
    s.clear(Tbl::A);
    mark(s, a);
    mark(s, b);
    pick(s, names)
}

/// The step of each member of the list `c0` of sorts, the first last, or
/// nothing when one of them has none.
fn rows(s: &mut Store, decls: TermId, c0: TermId, head: TermId, args: TermId) -> Option<TermId> {
    let mut out = s.alloc(Node::Nil);
    let mut c = c0;
    let mut ok = true;
    let mut go = true;
    while go {
        match uncons(s, c) {
            Some((n, t)) => match step(s, decls, n, head, args) {
                Some(kids) => {
                    out = s.alloc(Node::App(kids, out));
                    c = t;
                }
                None => {
                    ok = false;
                    go = false;
                }
            },
            None => go = false,
        }
    }
    if ok {
        Some(out)
    } else {
        None
    }
}

/// Flag in table `A` the first member of each row, unless it is any term.
/// The rows without their first members. No row is empty.
fn heads(s: &mut Store, rows0: TermId) -> TermId {
    let mut out = s.alloc(Node::Nil);
    let mut rows = rows0;
    while let Some((r, more)) = uncons(s, rows) {
        match uncons(s, r) {
            Some((k, kt)) => {
                if !is_nil(s, k) {
                    s.set_flag(Tbl::A, k, true);
                }
                out = s.alloc(Node::App(kt, out));
            }
            None => panic!(),
        }
        rows = more;
    }
    out
}

/// One step of the conjunction `c` on a term with the symbol `head` and the
/// arguments `args0`: for each argument the conjunction of the sorts the
/// members of `c` give it, or nothing when one of them has no term with that
/// symbol and that number of arguments.
///
/// The conjunction of an argument waits on the stack until the last is
/// found.
pub fn step_conj(
    s: &mut Store,
    decls: TermId,
    names: TermId,
    c: TermId,
    head: TermId,
    args0: TermId,
) -> Option<TermId> {
    match rows(s, decls, c, head, args0) {
        None => None,
        Some(rows0) => {
            let mut rows = rows0;
            let mut args = args0;
            while let Some((_, t)) = uncons(s, args) {
                s.clear(Tbl::A);
                rows = heads(s, rows);
                let k = pick(s, names);
                s.push(Frame::Visit(k, k));
                args = t;
            }
            let nil = s.alloc(Node::Nil);
            Some(unstack(s, nil))
        }
    }
}

/// Has every sort of the list `c0` a rest? A name with no declaration has
/// none.
fn rest_ok(s: &mut Store, decls: TermId, c0: TermId) -> bool {
    let mut c = c0;
    let mut ok = true;
    let mut go = true;
    while go {
        match uncons(s, c) {
            Some((n, t)) => match lookup(s, decls, n) {
                Some((_, rest)) => {
                    if is_nil(s, rest) {
                        ok = false;
                        go = false;
                    } else {
                        c = t;
                    }
                }
                None => {
                    ok = false;
                    go = false;
                }
            },
            None => go = false,
        }
    }
    ok
}

/// Put in front of `todo0` each member of `kids0` that table `B` does not
/// flag, and flag it as not known to have a member.
fn enqueue(s: &mut Store, todo0: TermId, kids0: TermId) -> TermId {
    let mut todo = todo0;
    let mut kids = kids0;
    while let Some((k, t)) = uncons(s, kids) {
        todo = match s.get_flag(Tbl::B, k) {
            Some(_) => todo,
            None => {
                s.set_flag(Tbl::B, k, false);
                s.alloc(Node::App(k, todo))
            }
        };
        kids = t;
    }
    todo
}

/// For each case of the list `cases0`, the step of the conjunction `c` at
/// its symbol and its number of arguments. When `c` has one, the symbol
/// with the conjunctions of the arguments is put in front of `alts0` as one
/// alternative, and the conjunctions table `B` does not flag in front of
/// `todo0`.
fn expand_cases(
    s: &mut Store,
    decls: TermId,
    names: TermId,
    c: TermId,
    cases0: TermId,
    alts0: TermId,
    todo0: TermId,
) -> (TermId, TermId) {
    let mut alts = alts0;
    let mut todo = todo0;
    let mut cases = cases0;
    while let Some((case, t)) = uncons(s, cases) {
        match uncons(s, case) {
            Some((f, ks)) => {
                if let Some(args) = step_conj(s, decls, names, c, f, ks) {
                    let alt = s.alloc(Node::App(f, args));
                    alts = s.alloc(Node::App(alt, alts));
                    todo = enqueue(s, todo, args);
                }
            }
            None => panic!(),
        }
        cases = t;
    }
    (alts, todo)
}

/// The alternatives of the conjunction `c`: for each case of each of its
/// sorts that `c` has a step at, the symbol of the case with the
/// conjunctions of the arguments. Those table `B` does not flag are put in
/// front of `todo0`.
///
/// Two alternatives are one node exactly when they have the same symbol and
/// the same number of arguments.
fn expand(s: &mut Store, decls: TermId, names: TermId, c: TermId, todo0: TermId) -> (TermId, TermId) {
    let mut alts = s.alloc(Node::Nil);
    let mut todo = todo0;
    let mut ns = c;
    while let Some((n, t)) = uncons(s, ns) {
        if let Some((cases, _)) = lookup(s, decls, n) {
            let (a, td) = expand_cases(s, decls, names, c, cases, alts, todo);
            alts = a;
            todo = td;
        }
        ns = t;
    }
    (alts, todo)
}

/// The conjunctions `c` reaches, each with its alternatives. Table `B`
/// flags each of them: with yes when every sort of it has a rest (it has a
/// member, and its alternatives are not looked for), and with no otherwise.
fn reach(s: &mut Store, decls: TermId, names: TermId, c: TermId) -> TermId {
    let nil = s.alloc(Node::Nil);
    s.set_flag(Tbl::B, c, false);
    let mut todo = s.alloc(Node::App(c, nil));
    let mut graph = nil;
    while let Some((d, t)) = uncons(s, todo) {
        if rest_ok(s, decls, d) {
            s.set_flag(Tbl::B, d, true);
            todo = t;
        } else {
            let (alts, td) = expand(s, decls, names, d, t);
            let entry = s.alloc(Node::App(d, alts));
            graph = s.alloc(Node::App(entry, graph));
            todo = td;
        }
    }
    graph
}

/// Does table `B` flag every member of the list with yes?
fn all_live(s: &mut Store, kids0: TermId) -> bool {
    let mut kids = kids0;
    let mut ok = true;
    let mut go = true;
    while go {
        match uncons(s, kids) {
            Some((k, t)) => match s.get_flag(Tbl::B, k) {
                Some(true) => kids = t,
                _ => {
                    ok = false;
                    go = false;
                }
            },
            None => go = false,
        }
    }
    ok
}

/// Are the conjunctions of the alternative `a` all flagged with yes?
fn alt_live(s: &mut Store, a: TermId) -> bool {
    match uncons(s, a) {
        Some((_, kids)) => all_live(s, kids),
        None => panic!(),
    }
}

/// Is some alternative of the list all flagged with yes?
fn any_alt(s: &mut Store, alts0: TermId) -> bool {
    let mut alts = alts0;
    let mut found = false;
    let mut go = true;
    while go {
        match uncons(s, alts) {
            Some((a, t)) => {
                if alt_live(s, a) {
                    found = true;
                    go = false;
                } else {
                    alts = t;
                }
            }
            None => go = false,
        }
    }
    found
}

/// One round over the conjunctions with their alternatives: one flagged
/// with no that has an alternative all flagged with yes is flagged with
/// yes. Was any?
fn pass(s: &mut Store, graph0: TermId) -> bool {
    let mut graph = graph0;
    let mut changed = false;
    while let Some((e, t)) = uncons(s, graph) {
        match uncons(s, e) {
            Some((d, alts)) => match s.get_flag(Tbl::B, d) {
                Some(true) => {}
                _ => {
                    if any_alt(s, alts) {
                        s.set_flag(Tbl::B, d, true);
                        changed = true;
                    }
                }
            },
            None => panic!(),
        }
        graph = t;
    }
    changed
}

/// The conjunctions `c` reaches, each with its alternatives, with table `B`
/// flagging with yes those of them that have a member, and the others with
/// no. `c` and the conjunctions it reaches are gone through once for their
/// alternatives, and then in rounds until a round finds no new one with a
/// member. Tables `A` and `B` are used.
fn flag_live(s: &mut Store, decls: TermId, names: TermId, c: TermId) -> TermId {
    s.clear(Tbl::B);
    let graph = reach(s, decls, names, c);
    let mut go = true;
    while go {
        go = pass(s, graph);
    }
    graph
}

/// Has the conjunction `c` a member? Tables `A` and `B` are used.
pub fn live(s: &mut Store, decls: TermId, names: TermId, c: TermId) -> bool {
    flag_live(s, decls, names, c);
    matches!(s.get_flag(Tbl::B, c), Some(true))
}

/// How many members a conjunction of sorts has.
#[derive(Clone, Copy)]
pub enum Count {
    /// No member.
    None,
    /// This term and no other.
    One(TermId),
    /// More than one member.
    Many,
}

/// The alternative of the list that is all flagged with yes, when all of
/// those that are, are one node.
fn sole_alt(s: &mut Store, alts0: TermId) -> Option<TermId> {
    let mut alts = alts0;
    let mut sole = None;
    let mut go = true;
    while go {
        match uncons(s, alts) {
            Some((a, t)) => {
                if alt_live(s, a) {
                    match sole {
                        Some(b) => {
                            if s.same(a, b) {
                                alts = t;
                            } else {
                                sole = None;
                                go = false;
                            }
                        }
                        None => {
                            sole = Some(a);
                            alts = t;
                        }
                    }
                } else {
                    alts = t;
                }
            }
            None => go = false,
        }
    }
    sole
}

/// The term with the symbol `f` whose arguments are what table `A` has for
/// the members of the list `kids0`, in order, or nothing when it has
/// nothing for one of them.
fn apply_members(s: &mut Store, f: TermId, kids0: TermId) -> Option<TermId> {
    let mut term = f;
    let mut kids = kids0;
    let mut ok = true;
    let mut go = true;
    while go {
        match uncons(s, kids) {
            Some((k, t)) => match s.get(Tbl::A, k) {
                Some(m) => {
                    term = s.alloc(Node::App(term, m));
                    kids = t;
                }
                None => {
                    ok = false;
                    go = false;
                }
            },
            None => go = false,
        }
    }
    if ok {
        Some(term)
    } else {
        None
    }
}

/// One round over the conjunctions with their alternatives. Table `B`
/// flags with yes those with a member, and table `A` has the member of some
/// that have just one. One that table `A` has nothing for, with just one
/// alternative all flagged with yes whose conjunctions table `A` has all a
/// member for, gets its member in table `A`. Did any?
fn pass_one(s: &mut Store, graph0: TermId) -> bool {
    let mut graph = graph0;
    let mut changed = false;
    while let Some((e, t)) = uncons(s, graph) {
        match uncons(s, e) {
            Some((d, alts)) => match s.get(Tbl::A, d) {
                Some(_) => {}
                None => {
                    if let Some(a) = sole_alt(s, alts) {
                        match uncons(s, a) {
                            Some((f, kids)) => {
                                if let Some(m) = apply_members(s, f, kids) {
                                    s.set(Tbl::A, d, m);
                                    changed = true;
                                }
                            }
                            None => panic!(),
                        }
                    }
                }
            },
            None => panic!(),
        }
        graph = t;
    }
    changed
}

/// How many members the conjunction `c` has, with the member when there is
/// one. After table `B` flags the conjunctions `c` reaches that have a
/// member, they are gone through in rounds until a round finds no new one
/// with just one member. Tables `A` and `B` are used.
pub fn count(s: &mut Store, decls: TermId, names: TermId, c: TermId) -> Count {
    let graph = flag_live(s, decls, names, c);
    match s.get_flag(Tbl::B, c) {
        Some(true) => {
            s.clear(Tbl::A);
            let mut go = true;
            while go {
                go = pass_one(s, graph);
            }
            match s.get(Tbl::A, c) {
                Some(m) => Count::One(m),
                None => Count::Many,
            }
        }
        _ => Count::None,
    }
}
