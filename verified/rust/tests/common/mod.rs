//! A reference implementation of the specification on trees, and helpers to
//! move terms between trees and the store.
#![allow(dead_code)]

use rwlog_core::span::Span;
use rwlog_core::store::{Node, Store, TermId};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum T {
    V(u128),
    S(u32),
    A(Box<T>, Box<T>),
}

pub fn v(n: u128) -> T {
    T::V(n)
}
pub fn sy(f: u32) -> T {
    T::S(f)
}
pub fn ap(a: T, b: T) -> T {
    T::A(Box::new(a), Box::new(b))
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TSpan {
    pub l: T,
    pub r: T,
    pub c: Vec<T>,
}

pub fn put_var(s: &mut Store, n: u128) -> TermId {
    if n == 0 {
        s.alloc(Node::V0)
    } else {
        let p = put_var(s, n / 2);
        if n.is_multiple_of(2) {
            s.alloc(Node::VL(p))
        } else {
            s.alloc(Node::VR(p))
        }
    }
}

pub fn put(s: &mut Store, t: &T) -> TermId {
    match t {
        T::V(n) => put_var(s, *n),
        T::S(f) => s.alloc(Node::Sym(*f)),
        T::A(a, b) => {
            let x = put(s, a);
            let y = put(s, b);
            s.alloc(Node::App(x, y))
        }
    }
}

pub fn put_list(s: &mut Store, ts: &[T]) -> TermId {
    match ts.split_first() {
        None => s.alloc(Node::Nil),
        Some((h, rest)) => {
            let r = put_list(s, rest);
            let x = put(s, h);
            s.alloc(Node::App(x, r))
        }
    }
}

pub fn put_span(s: &mut Store, x: &TSpan) -> Span {
    let l = put(s, &x.l);
    let r = put(s, &x.r);
    let c = put_list(s, &x.c);
    Span { l, r, c }
}

pub fn get(s: &mut Store, p: TermId) -> T {
    match s.read(p) {
        Node::V0 => T::V(0),
        Node::VL(a) => match get(s, a) {
            T::V(n) => T::V(2 * n),
            _ => panic!("the part of a variable is not a variable"),
        },
        Node::VR(a) => match get(s, a) {
            T::V(n) => T::V(2 * n + 1),
            _ => panic!("the part of a variable is not a variable"),
        },
        Node::Sym(f) => T::S(f),
        Node::App(a, b) => {
            let x = get(s, a);
            let y = get(s, b);
            ap(x, y)
        }
        Node::Nil => panic!("a list where a term was expected"),
    }
}

pub fn get_list(s: &mut Store, p: TermId) -> Vec<T> {
    let mut out = Vec::new();
    let mut p = p;
    loop {
        match s.read(p) {
            Node::Nil => return out,
            Node::App(h, t) => {
                out.push(get(s, h));
                p = t;
            }
            _ => panic!("a term where a list was expected"),
        }
    }
}

pub fn get_span(s: &mut Store, x: Span) -> TSpan {
    TSpan { l: get(s, x.l), r: get(s, x.r), c: get_list(s, x.c) }
}

/// Ticks spent by `f`.
pub fn spent<R>(s: &mut Store, f: impl FnOnce(&mut Store) -> R) -> (R, u64) {
    let before = s.ticks();
    let r = f(s);
    (r, s.ticks() - before)
}

// The specification, on trees.

pub fn rename(t: &T, f: &dyn Fn(u128) -> u128) -> T {
    match t {
        T::V(n) => T::V(f(*n)),
        T::S(g) => T::S(*g),
        T::A(a, b) => ap(rename(a, f), rename(b, f)),
    }
}

pub fn subst(t: &T, x: u128, u: &T) -> T {
    match t {
        T::V(n) => {
            if *n == x {
                u.clone()
            } else {
                T::V(*n)
            }
        }
        T::S(g) => T::S(*g),
        T::A(a, b) => ap(subst(a, x, u), subst(b, x, u)),
    }
}

pub fn occurs(t: &T, x: u128) -> bool {
    match t {
        T::V(n) => *n == x,
        T::S(_) => false,
        T::A(a, b) => occurs(a, x) || occurs(b, x),
    }
}

/// `solve` of `lean/RwLog/Kernel/Solve.lean`: the eliminations, in order.
pub fn solve(eqs: &[(T, T)]) -> Option<Vec<(u128, T)>> {
    let mut eqs: Vec<(T, T)> = eqs.to_vec();
    let mut out = Vec::new();
    while !eqs.is_empty() {
        let (p, q) = eqs.remove(0);
        let elim = match (&p, &q) {
            (T::V(x), T::V(y)) => {
                if x == y {
                    None
                } else {
                    Some((*x, q.clone()))
                }
            }
            (T::V(x), T::S(_)) => Some((*x, q.clone())),
            (T::V(x), T::A(_, _)) => {
                if occurs(&q, *x) {
                    return None;
                }
                Some((*x, q.clone()))
            }
            (T::S(_), T::V(y)) => Some((*y, p.clone())),
            (T::A(_, _), T::V(y)) => {
                if occurs(&p, *y) {
                    return None;
                }
                Some((*y, p.clone()))
            }
            (T::S(f), T::S(g)) => {
                if f != g {
                    return None;
                }
                None
            }
            (T::A(a, b), T::A(c, d)) => {
                eqs.insert(0, ((**b).clone(), (**d).clone()));
                eqs.insert(0, ((**a).clone(), (**c).clone()));
                None
            }
            _ => return None,
        };
        if let Some((x, u)) = elim {
            for e in eqs.iter_mut() {
                *e = (subst(&e.0, x, &u), subst(&e.1, x, &u));
            }
            out.push((x, u));
        }
    }
    Some(out)
}

fn apply(t: &T, th: &[(u128, T)]) -> T {
    let mut t = t.clone();
    for (x, u) in th {
        t = subst(&t, *x, u);
    }
    t
}

fn left(t: &T) -> T {
    rename(t, &|n| 2 * n)
}
fn right(t: &T) -> T {
    rename(t, &|n| 2 * n + 1)
}

fn store_of(x: &TSpan, y: &TSpan) -> Vec<T> {
    x.c.iter().map(left).chain(y.c.iter().map(right)).collect()
}

/// `Span.compose` of `lean/RwLog/Kernel/Span.lean`.
pub fn compose(x: &TSpan, y: &TSpan) -> Option<TSpan> {
    let th = solve(&[(left(&x.r), right(&y.l))])?;
    Some(TSpan {
        l: apply(&left(&x.l), &th),
        r: apply(&right(&y.r), &th),
        c: store_of(x, y).iter().map(|t| apply(t, &th)).collect(),
    })
}

/// `Span.meet` of `lean/RwLog/Kernel/Span.lean`.
pub fn meet(x: &TSpan, y: &TSpan) -> Option<TSpan> {
    let th = solve(&[(left(&x.l), right(&y.l)), (left(&x.r), right(&y.r))])?;
    Some(TSpan {
        l: apply(&left(&x.l), &th),
        r: apply(&left(&x.r), &th),
        c: store_of(x, y).iter().map(|t| apply(t, &th)).collect(),
    })
}

/// Every term with at most `depth` nested applications over two variables
/// and two symbols.
pub fn terms(depth: u32) -> Vec<T> {
    let leaves = vec![v(0), v(1), sy(0), sy(1)];
    if depth == 0 {
        return leaves;
    }
    let sub = terms(depth - 1);
    let mut out = leaves;
    for a in &sub {
        for b in &sub {
            out.push(ap(a.clone(), b.clone()));
        }
    }
    out
}

/// `matchInto` of `lean/RwLog/Kernel/Match.lean`.
pub fn match_into(p: &T, t: &T, th: &mut Vec<(u128, T)>) -> bool {
    match (p, t) {
        (T::V(x), _) => match th.iter().find(|b| b.0 == *x) {
            Some(b) => b.1 == *t,
            None => {
                th.push((*x, t.clone()));
                true
            }
        },
        (T::S(f), T::S(g)) => f == g,
        (T::A(p1, p2), T::A(t1, t2)) => match_into(p1, t1, th) && match_into(p2, t2, th),
        _ => false,
    }
}

/// `Span.covers?` for a covering span without constraints.
pub fn covers_plain(a: &TSpan, x: &TSpan) -> bool {
    assert!(a.c.is_empty());
    let mut th = Vec::new();
    match_into(&a.l, &x.l, &mut th) && match_into(&a.r, &x.r, &mut th)
}

pub fn vars(t: &T, out: &mut Vec<u128>) {
    match t {
        T::V(n) => out.push(*n),
        T::S(_) => (),
        T::A(a, b) => {
            vars(a, out);
            vars(b, out);
        }
    }
}

/// `bound` of the interface at `p` (`lean/RwLog/Kernel/Iface.lean`,
/// `Canon.lean`).
pub fn iface(p: &T, c: &[T]) -> Option<TSpan> {
    let mut pv = Vec::new();
    vars(p, &mut pv);
    let kept: Vec<T> = c
        .iter()
        .filter(|a| {
            let mut av = Vec::new();
            vars(a, &mut av);
            av.iter().all(|x| pv.contains(x))
        })
        .cloned()
        .collect();
    if matches!(p, T::V(_)) && kept.is_empty() {
        None
    } else {
        Some(TSpan { l: p.clone(), r: p.clone(), c: kept })
    }
}

/// Whether `Span.chain` is something.
pub fn chain_composes(xs: &[TSpan]) -> bool {
    match xs.split_first() {
        None => true,
        Some((h, rest)) => {
            let mut acc = Some(h.clone());
            for y in rest {
                acc = acc.and_then(|a| compose(&a, y));
            }
            acc.is_some()
        }
    }
}
