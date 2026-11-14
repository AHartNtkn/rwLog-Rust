//! What is done with one equation between two terms.

mod common;
use common::*;
use rwlog_core::span::{act, Act};
use rwlog_core::store::{Node, Store};

#[test]
fn act_on_the_same_term_skips() {
    let mut s = Store::new();
    let p = put(&mut s, &ap(sy(0), v(1)));
    assert!(matches!(act(&mut s, p, p), Act::Skip));
}

#[test]
fn act_on_two_symbols_fails() {
    let mut s = Store::new();
    let p = s.alloc(Node::Sym(0));
    let q = s.alloc(Node::Sym(1));
    assert!(matches!(act(&mut s, p, q), Act::Fail));
}

#[test]
fn act_on_a_symbol_and_an_application_fails_both_ways() {
    let mut s = Store::new();
    let p = s.alloc(Node::Sym(0));
    let q = put(&mut s, &ap(sy(0), sy(0)));
    assert!(matches!(act(&mut s, p, q), Act::Fail));
    assert!(matches!(act(&mut s, q, p), Act::Fail));
}

#[test]
fn act_on_two_variables_eliminates_the_first() {
    let mut s = Store::new();
    let p = put_var(&mut s, 3);
    let q = put_var(&mut s, 4);
    match act(&mut s, p, q) {
        Act::Elim(x, u) => {
            assert!(s.same(x, p));
            assert!(s.same(u, q));
        }
        _ => panic!("expected an elimination"),
    }
}

#[test]
fn act_eliminates_the_variable_on_either_side() {
    let mut s = Store::new();
    let x = put_var(&mut s, 3);
    let f = s.alloc(Node::Sym(0));
    let t = put(&mut s, &ap(sy(0), v(1)));
    for (p, q, u) in [(x, f, f), (f, x, f), (x, t, t), (t, x, t)] {
        match act(&mut s, p, q) {
            Act::Elim(y, w) => {
                assert!(s.same(y, x));
                assert!(s.same(w, u));
            }
            _ => panic!("expected an elimination"),
        }
    }
}

#[test]
fn act_fails_when_the_variable_occurs_in_the_application() {
    let mut s = Store::new();
    let x = put_var(&mut s, 1);
    let t = put(&mut s, &ap(sy(0), ap(v(1), sy(1))));
    assert!(matches!(act(&mut s, x, t), Act::Fail));
    assert!(matches!(act(&mut s, t, x), Act::Fail));
}

#[test]
fn act_splits_two_applications_in_order() {
    let mut s = Store::new();
    let p = put(&mut s, &ap(sy(0), v(1)));
    let q = put(&mut s, &ap(v(2), sy(3)));
    match act(&mut s, p, q) {
        Act::Split(a, c, b, d) => {
            assert_eq!(get(&mut s, a), sy(0));
            assert_eq!(get(&mut s, c), v(2));
            assert_eq!(get(&mut s, b), v(1));
            assert_eq!(get(&mut s, d), sy(3));
        }
        _ => panic!("expected a split"),
    }
}
