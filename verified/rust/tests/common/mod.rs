//! A reference implementation of the specification on trees, and helpers to
//! move terms between trees and the store.
#![allow(dead_code)]

pub mod decls;
pub mod dom;
pub mod sorts;

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
