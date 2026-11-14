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

/// Is the node a variable?
fn is_var(s: &mut Store, p: TermId) -> bool {
    matches!(s.read(p), Node::V0 | Node::VL(_) | Node::VR(_))
}

/// The sorts the variables of the first-order pattern `p` must be in for an
/// instance of `p` to be in the sort `name`: a list of `App(variable, sort)`
/// that an instance of `p` is in the sort exactly when it satisfies, or
/// nothing when the sort, or the sort of an argument on the way, has no term
/// with a symbol of `p` and its number of arguments. A variable gets its
/// sort whether or not the sort has a declaration or a member.
///
/// Table `B` is cleared, and then flags each pair of a sort and a subterm
/// already asked about, so a subterm that occurs many times is read once for
/// each sort, and each atom is listed once. A pair still to do waits on the
/// stack as a `Visit` frame.
pub fn push_sort(s: &mut Store, decls: TermId, name: TermId, p: TermId) -> Option<TermId> {
    let mut atoms = s.alloc(Node::Nil);
    let mut ok = true;
    s.clear(Tbl::B);
    s.push(Frame::Visit(name, p));
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
                if is_var(s, u) {
                    let atom = s.alloc(Node::App(u, n));
                    atoms = s.alloc(Node::App(atom, atoms));
                } else {
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
    }
    if ok {
        Some(atoms)
    } else {
        None
    }
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

// Inclusion.
//
// A *pair* is `App(conjunction, sort or any term)`. The pair of a
// conjunction with a sort is *out* when the conjunction has a member that
// is not in the sort, and the pair of a conjunction with any term (`Nil`,
// which no term is outside of, read here as the sort with no member) is out
// when the conjunction has a member. So whether the arguments of a root
// have members is asked with pairs too, and there is one kind of question.
//
// The alternatives of a pair are `App(nows, steps)`. A member of `nows` is
// a list of pairs: the pair is out when all of them are. A member of
// `steps` is `App(guards, edges)`, two lists of pairs: the pair is out when
// all the guards are and one of the edges is.

/// The pair of each member of the list with any term, the first last.
fn bare(s: &mut Store, args0: TermId) -> TermId {
    let nil = s.alloc(Node::Nil);
    let mut out = nil;
    let mut args = args0;
    while let Some((a, t)) = uncons(s, args) {
        let p = s.alloc(Node::App(a, nil));
        out = s.alloc(Node::App(p, out));
        args = t;
    }
    out
}

/// The pair of each member of `args0` with the member of `kids0` at its
/// place, unless that is any term; the first last. The lists have the same
/// length.
fn pair_up(s: &mut Store, args0: TermId, kids0: TermId) -> TermId {
    let mut out = s.alloc(Node::Nil);
    let mut args = args0;
    let mut kids = kids0;
    while let Some((a, ta)) = uncons(s, args) {
        match uncons(s, kids) {
            Some((k, tk)) => {
                if !is_nil(s, k) {
                    let p = s.alloc(Node::App(a, k));
                    out = s.alloc(Node::App(p, out));
                }
                kids = tk;
            }
            None => panic!(),
        }
        args = ta;
    }
    out
}

/// The conjunction of the sorts the rests of the sorts of the list `c0`
/// require of arguments. Table `A` is used.
fn rest_kids(s: &mut Store, decls: TermId, names: TermId, c0: TermId) -> TermId {
    let mut list = s.alloc(Node::Nil);
    let mut c = c0;
    while let Some((n, t)) = uncons(s, c) {
        if let Some((_, rest)) = lookup(s, decls, n) {
            if let Some((_, r)) = uncons(s, rest) {
                if !is_nil(s, r) {
                    list = s.alloc(Node::App(r, list));
                }
            }
        }
        c = t;
    }
    conj_of(s, names, list)
}

/// For each member of the list `keys0`, a symbol with a list as long as its
/// number of arguments: when the conjunction `d` has a step there, an
/// alternative of the pair of `d` with `m`. Its guards are the pairs of the
/// conjunctions of the arguments with any term. When `m` has no step there
/// it is put in front of `nows0`, and otherwise in front of `steps0` with
/// the pairs of the conjunctions of the arguments with what `m` requires of
/// them. The pairs table `B` does not flag are put in front of `todo0`.
#[allow(clippy::too_many_arguments)]
fn expand_keys(
    s: &mut Store,
    decls: TermId,
    names: TermId,
    d: TermId,
    m: TermId,
    keys0: TermId,
    nows0: TermId,
    steps0: TermId,
    todo0: TermId,
) -> (TermId, TermId, TermId) {
    let mut nows = nows0;
    let mut steps = steps0;
    let mut todo = todo0;
    let mut keys = keys0;
    while let Some((key, t)) = uncons(s, keys) {
        match uncons(s, key) {
            Some((f, ks)) => {
                if let Some(args) = step_conj(s, decls, names, d, f, ks) {
                    let guards = bare(s, args);
                    todo = enqueue(s, todo, guards);
                    match step(s, decls, m, f, ks) {
                        None => nows = s.alloc(Node::App(guards, nows)),
                        Some(kids) => {
                            let edges = pair_up(s, args, kids);
                            todo = enqueue(s, todo, edges);
                            let alt = s.alloc(Node::App(guards, edges));
                            steps = s.alloc(Node::App(alt, steps));
                        }
                    }
                }
            }
            None => panic!(),
        }
        keys = t;
    }
    (nows, steps, todo)
}

/// The rest of a declaration: the roots it excludes with the sort it
/// requires of arguments, or any term; nothing when there is no declaration
/// or it has no rest.
fn own_rest(s: &mut Store, own: Option<(TermId, TermId)>) -> Option<(TermId, TermId)> {
    match own {
        Some((_, rest)) => uncons(s, rest),
        None => None,
    }
}

/// What the roots no declaration names give the pair of the conjunction `d`
/// with a sort whose declaration is `own`: lists of guards, of guards with
/// edges, and the pairs table `B` does not flag in front of `todo0`.
///
/// Such roots are in `d` only when every sort of `d` has a rest. Then the
/// pair is out when the sort has no rest, and when its rest requires a sort
/// of arguments, it is out when the pair of the sorts the rests of `d`
/// require with that sort is.
fn rest_alts(
    s: &mut Store,
    decls: TermId,
    names: TermId,
    d: TermId,
    own: Option<(TermId, TermId)>,
    todo0: TermId,
) -> (TermId, TermId, TermId) {
    let nil = s.alloc(Node::Nil);
    if rest_ok(s, decls, d) {
        match own_rest(s, own) {
            None => {
                let nows = s.alloc(Node::App(nil, nil));
                (nows, nil, todo0)
            }
            Some((_, r)) => {
                if is_nil(s, r) {
                    (nil, nil, todo0)
                } else {
                    let dk = rest_kids(s, decls, names, d);
                    let q = s.alloc(Node::App(dk, r));
                    let edges = s.alloc(Node::App(q, nil));
                    let todo = enqueue(s, todo0, edges);
                    let alt = s.alloc(Node::App(nil, edges));
                    let steps = s.alloc(Node::App(alt, nil));
                    (nil, steps, todo)
                }
            }
        }
    } else {
        (nil, nil, todo0)
    }
}

/// `expand_keys` on the cases of each sort of the list `ns0`, for the pair
/// of the conjunction `d` with `m`.
#[allow(clippy::too_many_arguments)]
fn conj_keys(
    s: &mut Store,
    decls: TermId,
    names: TermId,
    d: TermId,
    m: TermId,
    ns0: TermId,
    nows0: TermId,
    steps0: TermId,
    todo0: TermId,
) -> (TermId, TermId, TermId) {
    let mut nows = nows0;
    let mut steps = steps0;
    let mut todo = todo0;
    let mut ns = ns0;
    while let Some((n, t)) = uncons(s, ns) {
        if let Some((cases, _)) = lookup(s, decls, n) {
            let (a, b, c) = expand_keys(s, decls, names, d, m, cases, nows, steps, todo);
            nows = a;
            steps = b;
            todo = c;
        }
        ns = t;
    }
    (nows, steps, todo)
}

/// `expand_keys` on the cases of the declaration `own` of `m` and on the
/// roots its rest excludes, for the pair of the conjunction `d` with `m`.
#[allow(clippy::too_many_arguments)]
fn own_keys(
    s: &mut Store,
    decls: TermId,
    names: TermId,
    d: TermId,
    m: TermId,
    own: Option<(TermId, TermId)>,
    nows0: TermId,
    steps0: TermId,
    todo0: TermId,
) -> (TermId, TermId, TermId) {
    match own {
        Some((cases, rest)) => {
            let (a, b, c) = expand_keys(s, decls, names, d, m, cases, nows0, steps0, todo0);
            match uncons(s, rest) {
                Some((excluded, _)) => expand_keys(s, decls, names, d, m, excluded, a, b, c),
                None => (a, b, c),
            }
        }
        None => (nows0, steps0, todo0),
    }
}

/// The alternatives of the pair of the conjunction `d` with `m`, and the
/// pairs they name that table `B` does not flag in front of `todo0`: what
/// the roots no declaration names give, then the roots that the sorts of
/// `d` have a case for, that `m` has a case for, and that the rest of `m`
/// excludes.
fn expand_pair(
    s: &mut Store,
    decls: TermId,
    names: TermId,
    d: TermId,
    m: TermId,
    todo0: TermId,
) -> (TermId, TermId) {
    let own = lookup(s, decls, m);
    let (n0, s0, t0) = rest_alts(s, decls, names, d, own, todo0);
    let (n1, s1, t1) = conj_keys(s, decls, names, d, m, d, n0, s0, t0);
    let (n2, s2, t2) = own_keys(s, decls, names, d, m, own, n1, s1, t1);
    (s.alloc(Node::App(n2, s2)), t2)
}

/// The pairs the pair `p0` reaches, each with its alternatives. Tables `A`
/// and `B` are used: table `B` flags the pairs reached.
fn out_graph(s: &mut Store, decls: TermId, names: TermId, p0: TermId) -> TermId {
    let nil = s.alloc(Node::Nil);
    s.clear(Tbl::B);
    s.set_flag(Tbl::B, p0, false);
    let mut todo = s.alloc(Node::App(p0, nil));
    let mut graph = nil;
    while let Some((p, t)) = uncons(s, todo) {
        match uncons(s, p) {
            Some((d, m)) => {
                let (alts, td) = expand_pair(s, decls, names, d, m, t);
                let entry = s.alloc(Node::App(p, alts));
                graph = s.alloc(Node::App(entry, graph));
                todo = td;
            }
            None => panic!(),
        }
    }
    graph
}

/// Does table `A` flag every member of the list?
fn all_out(s: &mut Store, pairs0: TermId) -> bool {
    let mut pairs = pairs0;
    let mut ok = true;
    let mut go = true;
    while go {
        match uncons(s, pairs) {
            Some((p, t)) => match s.get_flag(Tbl::A, p) {
                Some(_) => pairs = t,
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

/// Does table `A` flag some member of the list?
fn any_out(s: &mut Store, pairs0: TermId) -> bool {
    let mut pairs = pairs0;
    let mut found = false;
    let mut go = true;
    while go {
        match uncons(s, pairs) {
            Some((p, t)) => match s.get_flag(Tbl::A, p) {
                Some(_) => {
                    found = true;
                    go = false;
                }
                None => pairs = t,
            },
            None => go = false,
        }
    }
    found
}

/// Is some list of the list all flagged by table `A`?
fn any_now(s: &mut Store, nows0: TermId) -> bool {
    let mut nows = nows0;
    let mut found = false;
    let mut go = true;
    while go {
        match uncons(s, nows) {
            Some((g, t)) => {
                if all_out(s, g) {
                    found = true;
                    go = false;
                } else {
                    nows = t;
                }
            }
            None => go = false,
        }
    }
    found
}

/// Has some member of the list its guards all flagged by table `A`, and one
/// of its edges?
fn any_step(s: &mut Store, steps0: TermId) -> bool {
    let mut steps = steps0;
    let mut found = false;
    let mut go = true;
    while go {
        match uncons(s, steps) {
            Some((alt, t)) => match uncons(s, alt) {
                Some((guards, edges)) => {
                    if all_out(s, guards) && any_out(s, edges) {
                        found = true;
                        go = false;
                    } else {
                        steps = t;
                    }
                }
                None => panic!(),
            },
            None => go = false,
        }
    }
    found
}

/// One round over the pairs with their alternatives: a pair table `A` does
/// not flag, with an alternative that makes it out given the pairs flagged,
/// is flagged. Was any?
fn pass_out(s: &mut Store, graph0: TermId) -> bool {
    let mut graph = graph0;
    let mut changed = false;
    while let Some((e, t)) = uncons(s, graph) {
        match uncons(s, e) {
            Some((p, alts)) => match s.get_flag(Tbl::A, p) {
                Some(_) => {}
                None => match uncons(s, alts) {
                    Some((nows, steps)) => {
                        if any_now(s, nows) || any_step(s, steps) {
                            s.set_flag(Tbl::A, p, true);
                            changed = true;
                        }
                    }
                    None => panic!(),
                },
            },
            None => panic!(),
        }
        graph = t;
    }
    changed
}

/// Has the conjunction `c` a member that is not in the sort `n`? The pairs
/// the pair of `c` with `n` reaches are gone through once for their
/// alternatives, and then in rounds until a round finds no new pair that is
/// out. `n` is the name of a sort. Tables `A` and `B` are used.
pub fn out(s: &mut Store, decls: TermId, names: TermId, c: TermId, n: TermId) -> bool {
    let p0 = s.alloc(Node::App(c, n));
    let graph = out_graph(s, decls, names, p0);
    s.clear(Tbl::A);
    let mut go = true;
    while go {
        go = pass_out(s, graph);
    }
    matches!(s.get_flag(Tbl::A, p0), Some(true))
}

/// Is every member of the conjunction `c` in the sort `n`? `n` is the name
/// of a sort. Tables `A` and `B` are used.
pub fn included(s: &mut Store, decls: TermId, names: TermId, c: TermId, n: TermId) -> bool {
    !out(s, decls, names, c, n)
}

// Inclusion but for some terms.
//
// Whether every member of a conjunction, but for the ground terms of a
// list, is in a sort is asked root by root. Where the sort has no term with
// a root, the conjunction may have only one, and it must be in the list.
// Where the sort sorts the arguments, a member of the conjunction is outside
// the sort at one argument, so the same is asked of each argument that the
// sort sorts, with the arguments there of the terms of the list whose other
// arguments are each the one member of their conjunction. What is still to
// ask is a list of `App(conjunction, App(sort, terms))` with terms left.
//
// A *root* is `App(symbol, list with one member for each argument)`.

/// The list with its members in the other order.
fn rev(s: &mut Store, l0: TermId) -> TermId {
    let mut out = s.alloc(Node::Nil);
    let mut l = l0;
    while let Some((h, t)) = uncons(s, l) {
        out = s.alloc(Node::App(h, out));
        l = t;
    }
    out
}

/// The roots `keys` with the root of `head` and `args` in front, unless
/// they have it.
fn add_key(s: &mut Store, keys: TermId, head: TermId, args: TermId) -> TermId {
    match find(s, keys, head, args) {
        Some(_) => keys,
        None => {
            let k = s.alloc(Node::App(head, args));
            s.alloc(Node::App(k, keys))
        }
    }
}

/// The roots `keys0` with each root of the list `entries0` they have not.
fn add_keys(s: &mut Store, keys0: TermId, entries0: TermId) -> TermId {
    let mut keys = keys0;
    let mut entries = entries0;
    while let Some((e, t)) = uncons(s, entries) {
        match uncons(s, e) {
            Some((f, ks)) => keys = add_key(s, keys, f, ks),
            None => panic!(),
        }
        entries = t;
    }
    keys
}

/// The roots `keys0` with the roots of the cases of each sort of the list
/// `c0`.
fn add_conj_keys(s: &mut Store, decls: TermId, keys0: TermId, c0: TermId) -> TermId {
    let mut keys = keys0;
    let mut c = c0;
    while let Some((n, t)) = uncons(s, c) {
        if let Some((cases, _)) = lookup(s, decls, n) {
            keys = add_keys(s, keys, cases);
        }
        c = t;
    }
    keys
}

/// The roots `keys0` with the root of each term of the list `g0`.
fn add_term_keys(s: &mut Store, keys0: TermId, g0: TermId) -> TermId {
    let mut keys = keys0;
    let mut g = g0;
    while let Some((t, more)) = uncons(s, g) {
        let (h, args) = spine(s, t);
        keys = add_key(s, keys, h, args);
        g = more;
    }
    keys
}

/// The roots to ask about, each once: those of the cases of the sorts of
/// `c`, of the cases of `n`, those the rest of `n` excludes, and those of
/// the terms of `g`.
fn but_keys(s: &mut Store, decls: TermId, c: TermId, n: TermId, g: TermId) -> TermId {
    let nil = s.alloc(Node::Nil);
    let mut keys = add_conj_keys(s, decls, nil, c);
    if let Some((cases, rest)) = lookup(s, decls, n) {
        keys = add_keys(s, keys, cases);
        if let Some((excluded, _)) = uncons(s, rest) {
            keys = add_keys(s, keys, excluded);
        }
    }
    add_term_keys(s, keys, g)
}

/// Has the conjunction `c` a member outside the sort `n` at the roots no
/// declaration names? There are infinitely many of them. Tables `A` and `B`
/// are used.
fn fresh_out(s: &mut Store, decls: TermId, names: TermId, c: TermId, n: TermId) -> bool {
    if rest_ok(s, decls, c) {
        let own = lookup(s, decls, n);
        match own_rest(s, own) {
            None => true,
            Some((_, r)) => {
                if is_nil(s, r) {
                    false
                } else {
                    let dk = rest_kids(s, decls, names, c);
                    out(s, decls, names, dk, r)
                }
            }
        }
    } else {
        false
    }
}

/// For each conjunction of the list `kids0`, in order: `App(member, Nil)`
/// when it has one member, and `Nil` when it has more. Nothing when one of
/// them has no member. Tables `A` and `B` are used.
fn soles(s: &mut Store, decls: TermId, names: TermId, kids0: TermId) -> Option<TermId> {
    let nil = s.alloc(Node::Nil);
    let mut out = nil;
    let mut kids = kids0;
    let mut ok = true;
    let mut go = true;
    while go {
        match uncons(s, kids) {
            Some((k, t)) => match count(s, decls, names, k) {
                Count::None => {
                    ok = false;
                    go = false;
                }
                Count::One(m) => {
                    let e = s.alloc(Node::App(m, nil));
                    out = s.alloc(Node::App(e, out));
                    kids = t;
                }
                Count::Many => {
                    out = s.alloc(Node::App(nil, out));
                    kids = t;
                }
            },
            None => go = false,
        }
    }
    if ok {
        Some(rev(s, out))
    } else {
        None
    }
}

/// Is the term `a` the one member that `e` holds?
fn is_sole(s: &mut Store, e: TermId, a: TermId) -> bool {
    match uncons(s, e) {
        Some((m, _)) => s.same(m, a),
        None => false,
    }
}

/// Is some argument of the list `args0` not the one member of its
/// conjunction, and are two? `soles0` is what `soles` gives, and as long.
fn misses(s: &mut Store, soles0: TermId, args0: TermId) -> (bool, bool) {
    let mut any = false;
    let mut two = false;
    let mut so = soles0;
    let mut args = args0;
    while let Some((e, st)) = uncons(s, so) {
        match uncons(s, args) {
            Some((a, at)) => {
                let miss = !is_sole(s, e, a);
                two |= any & miss;
                any |= miss;
                so = st;
                args = at;
            }
            None => panic!(),
        }
    }
    (any, two)
}

/// Has the list `g0` a term with the symbol `f` and as many arguments as
/// `ks` has members, each the one member of its conjunction?
fn only_in(s: &mut Store, so: TermId, f: TermId, ks: TermId, g0: TermId) -> bool {
    let mut g = g0;
    let mut found = false;
    let mut go = true;
    while go {
        match uncons(s, g) {
            Some((t, more)) => {
                let (h, args) = spine(s, t);
                if s.same(h, f) && same_len(s, args, ks) {
                    let (any, _) = misses(s, so, args);
                    if any {
                        g = more;
                    } else {
                        found = true;
                        go = false;
                    }
                } else {
                    g = more;
                }
            }
            None => go = false,
        }
    }
    found
}

/// The lists `accs0`, one for each argument, each with its argument of
/// `args0` in front when every other argument is the one member of its
/// conjunction. `any` says that some argument is not, and no two are not.
fn contrib(s: &mut Store, soles0: TermId, args0: TermId, accs0: TermId, any: bool) -> TermId {
    let mut out = s.alloc(Node::Nil);
    let mut so = soles0;
    let mut args = args0;
    let mut accs = accs0;
    while let Some((e, st)) = uncons(s, so) {
        match uncons(s, args) {
            Some((a, at)) => match uncons(s, accs) {
                Some((acc, ct)) => {
                    let put = if any { !is_sole(s, e, a) } else { true };
                    let acc1 = if put { s.alloc(Node::App(a, acc)) } else { acc };
                    out = s.alloc(Node::App(acc1, out));
                    so = st;
                    args = at;
                    accs = ct;
                }
                None => panic!(),
            },
            None => panic!(),
        }
    }
    rev(s, out)
}

/// For each argument of the root of `f` and `ks`, in order: that argument
/// of the terms of the list `g0` with the root whose other arguments are
/// each the one member of their conjunction.
fn projs(s: &mut Store, so: TermId, f: TermId, ks: TermId, g0: TermId) -> TermId {
    let nil = s.alloc(Node::Nil);
    let mut accs = fill(s, ks, nil);
    let mut g = g0;
    while let Some((t, more)) = uncons(s, g) {
        let (h, args) = spine(s, t);
        if s.same(h, f) && same_len(s, args, ks) {
            let (any, two) = misses(s, so, args);
            if !two {
                accs = contrib(s, so, args, accs, any);
            }
        }
        g = more;
    }
    accs
}

/// What a root where the sort sorts the arguments leaves to ask: for each
/// argument the sort `kn0` gives a sort, whether its conjunction of `kids0`
/// but for the terms of `accs0` is in that sort. With no term it is asked
/// now, and nothing is given when it is not; otherwise it is put in front
/// of `todo0`. The three lists are as long. Tables `A` and `B` are used.
fn push_asks(
    s: &mut Store,
    decls: TermId,
    names: TermId,
    kids0: TermId,
    kn0: TermId,
    accs0: TermId,
    todo0: TermId,
) -> Option<TermId> {
    let mut todo = todo0;
    let mut kids = kids0;
    let mut kn = kn0;
    let mut accs = accs0;
    let mut ok = true;
    let mut go = true;
    while go {
        match uncons(s, kids) {
            Some((k, kt)) => match uncons(s, kn) {
                Some((m, mt)) => match uncons(s, accs) {
                    Some((acc, ct)) => {
                        kids = kt;
                        kn = mt;
                        accs = ct;
                        if !is_nil(s, m) {
                            if is_nil(s, acc) {
                                if !included(s, decls, names, k, m) {
                                    ok = false;
                                    go = false;
                                }
                            } else {
                                let r = s.alloc(Node::App(m, acc));
                                let ask = s.alloc(Node::App(k, r));
                                todo = s.alloc(Node::App(ask, todo));
                            }
                        }
                    }
                    None => panic!(),
                },
                None => panic!(),
            },
            None => go = false,
        }
    }
    if ok {
        Some(todo)
    } else {
        None
    }
}

/// What the root of `f` and `ks` leaves to ask of the conjunction `c`, the
/// sort `n` and the terms `g`, in front of `todo`; nothing when the
/// conjunction has a member with that root that is outside the sort and not
/// in `g`. Tables `A` and `B` are used.
#[allow(clippy::too_many_arguments)]
fn but_key(
    s: &mut Store,
    decls: TermId,
    names: TermId,
    c: TermId,
    n: TermId,
    g: TermId,
    f: TermId,
    ks: TermId,
    todo: TermId,
) -> Option<TermId> {
    match step_conj(s, decls, names, c, f, ks) {
        None => Some(todo),
        Some(kids) => match soles(s, decls, names, kids) {
            None => Some(todo),
            Some(so) => match step(s, decls, n, f, ks) {
                None => {
                    if only_in(s, so, f, ks, g) {
                        Some(todo)
                    } else {
                        None
                    }
                }
                Some(kn) => {
                    let accs = projs(s, so, f, ks, g);
                    push_asks(s, decls, names, kids, kn, accs, todo)
                }
            },
        },
    }
}

/// What is left to ask of the conjunction `c`, the sort `n` and the terms
/// `g`, of which there is one at least, in front of `todo0`; nothing when
/// the conjunction has a member outside the sort that is not in `g`. Tables
/// `A` and `B` are used.
fn but_one(
    s: &mut Store,
    decls: TermId,
    names: TermId,
    c: TermId,
    n: TermId,
    g: TermId,
    todo0: TermId,
) -> Option<TermId> {
    if fresh_out(s, decls, names, c, n) {
        None
    } else {
        let mut keys = but_keys(s, decls, c, n, g);
        let mut todo = todo0;
        let mut ok = true;
        let mut go = true;
        while go {
            match uncons(s, keys) {
                Some((key, t)) => match uncons(s, key) {
                    Some((f, ks)) => match but_key(s, decls, names, c, n, g, f, ks, todo) {
                        Some(td) => {
                            todo = td;
                            keys = t;
                        }
                        None => {
                            ok = false;
                            go = false;
                        }
                    },
                    None => panic!(),
                },
                None => go = false,
            }
        }
        if ok {
            Some(todo)
        } else {
            None
        }
    }
}

/// Is every member of the conjunction `c`, but for the ground terms of the
/// list `g`, in the sort `n`? `n` is the name of a sort. Tables `A` and `B`
/// are used.
pub fn included_but(
    s: &mut Store,
    decls: TermId,
    names: TermId,
    c: TermId,
    n: TermId,
    g: TermId,
) -> bool {
    if is_nil(s, g) {
        included(s, decls, names, c, n)
    } else {
        let nil = s.alloc(Node::Nil);
        let r = s.alloc(Node::App(n, g));
        let ask = s.alloc(Node::App(c, r));
        let mut todo = s.alloc(Node::App(ask, nil));
        let mut ok = true;
        let mut go = true;
        while go {
            match uncons(s, todo) {
                Some((a, t)) => match uncons(s, a) {
                    Some((c1, r1)) => match uncons(s, r1) {
                        Some((n1, g1)) => match but_one(s, decls, names, c1, n1, g1, t) {
                            Some(td) => todo = td,
                            None => {
                                ok = false;
                                go = false;
                            }
                        },
                        None => panic!(),
                    },
                    None => panic!(),
                },
                None => go = false,
            }
        }
        ok
    }
}

/// The conjunctions of the arguments at the root of `f` and `ks`, when the
/// conjunction `c` has a member with that root that is not in the list `g`
/// of ground terms; nothing otherwise. Tables `A` and `B` are used.
fn left_at(
    s: &mut Store,
    decls: TermId,
    names: TermId,
    c: TermId,
    g: TermId,
    f: TermId,
    ks: TermId,
) -> Option<TermId> {
    match step_conj(s, decls, names, c, f, ks) {
        None => None,
        Some(kids) => match soles(s, decls, names, kids) {
            None => None,
            Some(so) => {
                if only_in(s, so, f, ks, g) {
                    None
                } else {
                    Some(kids)
                }
            }
        },
    }
}

/// The one root of the members of the conjunction `c` that are not in the
/// list `g` of ground terms, with the conjunction of each of its arguments:
/// the symbol and the list of those conjunctions. Nothing when every sort of
/// `c` has a rest, when no member is left, or when two are left with
/// different roots. Tables `A` and `B` are used; the stack is empty at
/// entry.
pub fn sole_root(
    s: &mut Store,
    decls: TermId,
    names: TermId,
    c: TermId,
    g: TermId,
) -> Option<(TermId, TermId)> {
    if rest_ok(s, decls, c) {
        None
    } else {
        let nil = s.alloc(Node::Nil);
        let k0 = add_conj_keys(s, decls, nil, c);
        let mut keys = add_term_keys(s, k0, g);
        let mut found = None;
        let mut many = false;
        let mut go = true;
        while go {
            match uncons(s, keys) {
                Some((key, t)) => match uncons(s, key) {
                    Some((f, ks)) => {
                        match left_at(s, decls, names, c, g, f, ks) {
                            Some(kids) => {
                                if found.is_some() {
                                    many = true;
                                    go = false;
                                } else {
                                    found = Some((f, kids));
                                    keys = t;
                                }
                            }
                            None => keys = t,
                        }
                    }
                    None => panic!(),
                },
                None => go = false,
            }
        }
        if many {
            None
        } else {
            found
        }
    }
}
