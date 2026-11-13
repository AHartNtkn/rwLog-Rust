//! Composition and conjunction of spans, against the specification on trees.

mod common;
use common::*;
use rwlog_core::span::{act, compose, meet, Act};
use rwlog_core::store::{Node, Store};

fn check_compose(x: &TSpan, y: &TSpan) {
    let mut s = Store::new();
    let a = put_span(&mut s, x);
    let b = put_span(&mut s, y);
    let got = compose(&mut s, a, b).map(|r| get_span(&mut s, r));
    assert_eq!(got, common::compose(x, y), "compose {x:?} {y:?}");
}

fn check_meet(x: &TSpan, y: &TSpan) {
    let mut s = Store::new();
    let a = put_span(&mut s, x);
    let b = put_span(&mut s, y);
    let got = meet(&mut s, a, b).map(|r| get_span(&mut s, r));
    assert_eq!(got, common::meet(x, y), "meet {x:?} {y:?}");
}

fn span(l: T, r: T) -> TSpan {
    TSpan { l, r, c: Vec::new() }
}

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

#[test]
fn compose_agrees_with_the_specification_on_all_small_spans() {
    let ts = terms(1);
    let mut n = 0;
    for l1 in &ts {
        for r1 in ts.iter().step_by(3) {
            for l2 in &ts {
                for r2 in ts.iter().step_by(5) {
                    check_compose(&span(l1.clone(), r1.clone()), &span(l2.clone(), r2.clone()));
                    n += 1;
                }
            }
        }
    }
    assert!(n > 1000);
}

#[test]
fn meet_agrees_with_the_specification_on_all_small_spans() {
    let ts = terms(1);
    for l1 in ts.iter().step_by(2) {
        for r1 in ts.iter().step_by(3) {
            for l2 in ts.iter().step_by(2) {
                for r2 in ts.iter().step_by(3) {
                    check_meet(&span(l1.clone(), r1.clone()), &span(l2.clone(), r2.clone()));
                }
            }
        }
    }
}

#[test]
fn compose_agrees_on_deeper_terms_at_the_interface() {
    let ts = terms(2);
    for (i, r1) in ts.iter().enumerate().step_by(7) {
        for l2 in ts.iter().skip(i % 5).step_by(11) {
            check_compose(&span(v(0), r1.clone()), &span(l2.clone(), v(1)));
        }
    }
}

#[test]
fn compose_carries_and_instantiates_constraints() {
    let x = TSpan { l: v(0), r: ap(sy(0), v(0)), c: vec![ap(sy(5), v(0))] };
    let y = TSpan { l: ap(v(0), sy(1)), r: v(0), c: vec![v(0), ap(sy(6), v(1))] };
    check_compose(&x, &y);
    check_meet(&x, &y);
}

#[test]
fn compose_decrement_with_itself() {
    // B(A(x), y) -> B(x, y), twice.
    let (a, b) = (sy(0), sy(1));
    let bb = |p: T, q: T| ap(ap(b.clone(), p), q);
    let dec = span(bb(ap(a.clone(), v(0)), v(1)), bb(v(0), v(1)));
    let mut s = Store::new();
    let p = put_span(&mut s, &dec);
    let r = compose(&mut s, p, p).expect("composable");
    let got = get_span(&mut s, r);
    // The interface equates the left copy's B(x, y) with the right copy's
    // B(A(x), y): left x := A(right x), left y := right y.
    assert_eq!(got.l, bb(ap(a.clone(), ap(a.clone(), v(1))), v(3)));
    assert_eq!(got.r, bb(v(1), v(3)));
    assert_eq!(Some(got), common::compose(&dec, &dec));
}

#[test]
fn compose_fails_on_a_symbol_clash() {
    let x = span(v(0), ap(sy(0), v(0)));
    let y = span(ap(sy(1), v(0)), v(0));
    let mut s = Store::new();
    let a = put_span(&mut s, &x);
    let b = put_span(&mut s, &y);
    assert!(compose(&mut s, a, b).is_none());
}

#[test]
fn compose_fails_on_the_occurs_check() {
    // (x x) against (y (f y)).
    let x = span(v(0), ap(v(0), v(0)));
    let y = span(ap(v(0), ap(sy(0), v(0))), v(0));
    let mut s = Store::new();
    let a = put_span(&mut s, &x);
    let b = put_span(&mut s, &y);
    assert!(compose(&mut s, a, b).is_none());
    assert_eq!(common::compose(&x, &y), None);
}

#[test]
fn compose_does_not_confuse_the_same_variable_on_the_two_sides() {
    // x -> f x  then  f x -> x  is the identity on its variable.
    let x = span(v(0), ap(sy(0), v(0)));
    let y = span(ap(sy(0), v(0)), v(0));
    check_compose(&x, &y);
    // x -> x  then  (x x) -> x: the two x are different variables.
    check_compose(&span(v(0), v(0)), &span(ap(v(0), v(0)), v(0)));
}

#[test]
fn compose_of_a_chain_of_doubling_spans_is_polynomial() {
    // dbl = x -> (x x). Composing n of them gives a term with 2^n leaves
    // and n + 1 nodes.
    let dbl = span(v(0), ap(v(0), v(0)));
    let mut s = Store::new();
    let d = put_span(&mut s, &dbl);
    let mut acc = d;
    let mut costs = Vec::new();
    for _ in 0..30 {
        let (r, t) = spent(&mut s, |s| compose(s, acc, d));
        acc = r.expect("composable");
        costs.push(t);
    }
    let last = *costs.last().unwrap();
    assert!(last < 40 * 30 * 30, "the 30th composition spent {last} ticks");
}

#[test]
fn meet_fails_when_the_right_sides_clash() {
    let x = span(v(0), sy(0));
    let y = span(v(0), sy(1));
    let mut s = Store::new();
    let a = put_span(&mut s, &x);
    let b = put_span(&mut s, &y);
    assert!(meet(&mut s, a, b).is_none());
}

#[test]
fn meet_of_a_span_with_itself_is_a_renaming_of_it() {
    let x = span(ap(sy(0), v(0)), ap(v(0), v(1)));
    check_meet(&x, &x);
}
