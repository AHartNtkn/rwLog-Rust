//! Rebuilding, the occurs check and list append, against trees.

mod common;
use common::*;
use rwlog_core::store::{Node, Store, Tbl};
use rwlog_core::term::{append, occurs, rebuild, Leaf};

#[test]
fn rebuild_left_doubles_every_variable() {
    for t in terms(2) {
        let mut s = Store::new();
        let p = put(&mut s, &t);
        s.clear(Tbl::A);
        let r = rebuild(&mut s, Leaf::Left, p);
        assert_eq!(get(&mut s, r), rename(&t, &|n| 2 * n));
    }
}

#[test]
fn rebuild_right_doubles_and_adds_one() {
    for t in terms(2) {
        let mut s = Store::new();
        let p = put(&mut s, &t);
        s.clear(Tbl::A);
        let r = rebuild(&mut s, Leaf::Right, p);
        assert_eq!(get(&mut s, r), rename(&t, &|n| 2 * n + 1));
    }
}

#[test]
fn rebuild_sub_replaces_the_variable_only() {
    let us = [v(1), sy(1), ap(sy(0), v(5))];
    for t in terms(2) {
        for u in &us {
            let mut s = Store::new();
            let p = put(&mut s, &t);
            let x = put_var(&mut s, 0);
            let q = put(&mut s, u);
            s.clear(Tbl::A);
            let r = rebuild(&mut s, Leaf::Sub(x, q), p);
            assert_eq!(get(&mut s, r), subst(&t, 0, u));
        }
    }
}

#[test]
fn rebuild_of_a_term_without_the_variable_is_the_same_node() {
    let mut s = Store::new();
    let t = ap(ap(sy(0), v(1)), ap(sy(1), v(1)));
    let p = put(&mut s, &t);
    let x = put_var(&mut s, 0);
    let u = s.alloc(Node::Sym(9));
    s.clear(Tbl::A);
    let r = rebuild(&mut s, Leaf::Sub(x, u), p);
    assert!(s.same(r, p));
}

#[test]
fn rebuild_keeps_the_list_end() {
    let mut s = Store::new();
    let l = put_list(&mut s, &[v(0), ap(sy(0), v(1))]);
    s.clear(Tbl::A);
    let r = rebuild(&mut s, Leaf::Right, l);
    assert_eq!(get_list(&mut s, r), vec![v(1), ap(sy(0), v(3))]);
}

#[test]
fn rebuild_visits_a_shared_node_once() {
    // t_0 = x, t_{k+1} = (t_k t_k): 2^k leaves, k + 1 nodes.
    let mut s = Store::new();
    let mut p = s.root();
    for _ in 0..40 {
        p = s.alloc(Node::App(p, p));
    }
    s.clear(Tbl::A);
    let (_, t) = spent(&mut s, |s| rebuild(s, Leaf::Right, p));
    assert!(t <= 6 * 41, "spent {t} ticks on 41 nodes");
}

#[test]
fn occurs_agrees_with_the_tree() {
    for t in terms(2) {
        for x in 0..3u128 {
            let mut s = Store::new();
            let p = put(&mut s, &t);
            let xv = put_var(&mut s, x);
            s.clear(Tbl::B);
            assert_eq!(occurs(&mut s, xv, p), common::occurs(&t, x), "{x} in {t:?}");
        }
    }
}

#[test]
fn occurs_visits_a_shared_node_once() {
    let mut s = Store::new();
    let mut p = s.alloc(Node::Sym(0));
    for _ in 0..40 {
        p = s.alloc(Node::App(p, p));
    }
    let x = s.root();
    s.clear(Tbl::B);
    let (r, t) = spent(&mut s, |s| occurs(s, x, p));
    assert!(!r);
    assert!(t <= 5 * 41, "spent {t} ticks on 41 nodes");
}

#[test]
fn append_of_two_lists() {
    let xs = [v(0), sy(1)];
    let ys = [ap(sy(0), v(1))];
    let mut s = Store::new();
    let a = put_list(&mut s, &xs);
    let b = put_list(&mut s, &ys);
    let r = append(&mut s, a, b);
    assert_eq!(get_list(&mut s, r), vec![v(0), sy(1), ap(sy(0), v(1))]);
}

#[test]
fn append_to_the_empty_list_is_the_other_list() {
    let mut s = Store::new();
    let a = put_list(&mut s, &[]);
    let b = put_list(&mut s, &[v(1)]);
    let r = append(&mut s, a, b);
    assert!(s.same(r, b));
    let r2 = append(&mut s, b, a);
    assert!(s.same(r2, b));
}
