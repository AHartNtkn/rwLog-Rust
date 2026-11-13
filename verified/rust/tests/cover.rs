//! Coverage, equality, interfaces and the chain test, against the
//! specification on trees.

mod common;
use common::*;
use rwlog_core::cover::{covers_plain, left_bound, mmatch, right_bound, span_eq};
use rwlog_core::span::{composable, pack_span};
use rwlog_core::store::{Node, Store, Tbl, TermId};

fn span(l: T, r: T) -> TSpan {
    TSpan { l, r, c: Vec::new() }
}

#[test]
fn covers_agrees_with_the_specification_on_all_small_spans() {
    let ts = terms(1);
    let mut yes = 0;
    for l1 in &ts {
        for r1 in ts.iter().step_by(3) {
            for l2 in &ts {
                for r2 in ts.iter().step_by(2) {
                    let a = span(l1.clone(), r1.clone());
                    let x = span(l2.clone(), r2.clone());
                    let mut s = Store::new();
                    let pa = put_span(&mut s, &a);
                    let px = put_span(&mut s, &x);
                    let want = common::covers_plain(&a, &x);
                    assert_eq!(covers_plain(&mut s, pa, px), want, "{a:?} covers {x:?}");
                    if want {
                        yes += 1;
                    }
                }
            }
        }
    }
    assert!(yes > 50);
}

#[test]
fn a_variable_matched_twice_needs_the_same_term() {
    let a = span(ap(v(0), v(0)), v(0));
    let mut s = Store::new();
    let pa = put_span(&mut s, &a);
    let good = put_span(&mut s, &span(ap(sy(0), sy(0)), sy(0)));
    let bad1 = put_span(&mut s, &span(ap(sy(0), sy(1)), sy(0)));
    let bad2 = put_span(&mut s, &span(ap(sy(0), sy(0)), sy(1)));
    assert!(covers_plain(&mut s, pa, good));
    assert!(!covers_plain(&mut s, pa, bad1));
    assert!(!covers_plain(&mut s, pa, bad2));
}

#[test]
fn the_variables_of_the_covered_span_are_rigid() {
    // f x does not cover y, and x x does not cover x y.
    let mut s = Store::new();
    let a = put_span(&mut s, &span(ap(sy(0), v(0)), v(0)));
    let x = put_span(&mut s, &span(v(1), v(1)));
    assert!(!covers_plain(&mut s, a, x));
    let b = put_span(&mut s, &span(ap(v(0), v(0)), sy(0)));
    let y = put_span(&mut s, &span(ap(v(0), v(1)), sy(0)));
    assert!(!covers_plain(&mut s, b, y));
}

#[test]
fn a_span_covers_itself_even_with_the_same_variable_names() {
    for l in terms(1) {
        for r in terms(1).iter().step_by(4) {
            let a = span(l.clone(), r.clone());
            let mut s = Store::new();
            let p = put_span(&mut s, &a);
            assert!(covers_plain(&mut s, p, p), "{a:?}");
        }
    }
}

#[test]
fn a_failed_match_does_not_leave_a_binding_that_a_later_call_reads() {
    let mut s = Store::new();
    let a = put_span(&mut s, &span(ap(v(0), sy(1)), v(0)));
    let x = put_span(&mut s, &span(ap(sy(0), sy(0)), sy(0)));
    let y = put_span(&mut s, &span(ap(sy(1), sy(1)), sy(1)));
    assert!(!covers_plain(&mut s, a, x));
    assert!(covers_plain(&mut s, a, y));
}

#[test]
fn matching_visits_a_shared_pattern_node_once() {
    let mut s = Store::new();
    let mut p = s.root();
    let mut t = s.alloc(Node::Sym(0));
    for _ in 0..40 {
        p = s.alloc(Node::App(p, p));
        t = s.alloc(Node::App(t, t));
    }
    s.clear(Tbl::A);
    let (r, ticks) = spent(&mut s, |s| mmatch(s, p, t));
    assert!(r);
    assert!(ticks <= 6 * 41, "spent {ticks} ticks on 41 nodes");
}

#[test]
fn span_eq_is_equality_as_written() {
    let xs = [
        TSpan { l: v(0), r: v(0), c: vec![] },
        TSpan { l: v(0), r: v(1), c: vec![] },
        TSpan { l: v(1), r: v(0), c: vec![] },
        TSpan { l: v(0), r: v(0), c: vec![v(0)] },
        TSpan { l: v(0), r: v(0), c: vec![v(0), v(0)] },
        TSpan { l: v(0), r: v(0), c: vec![v(1), v(0)] },
        TSpan { l: v(0), r: v(0), c: vec![v(0), v(1)] },
        TSpan { l: ap(sy(0), v(0)), r: v(0), c: vec![] },
    ];
    for (i, a) in xs.iter().enumerate() {
        for (j, b) in xs.iter().enumerate() {
            let mut s = Store::new();
            let pa = put_span(&mut s, a);
            let pb = put_span(&mut s, b);
            assert_eq!(span_eq(&mut s, pa, pb), i == j, "{a:?} = {b:?}");
        }
    }
}

#[test]
fn span_eq_costs_at_most_three_ticks() {
    let mut s = Store::new();
    let big = TSpan { l: ap(ap(sy(0), v(0)), v(1)), r: v(0), c: vec![v(0), v(1), v(0)] };
    let a = put_span(&mut s, &big);
    let (r, t) = spent(&mut s, |s| span_eq(s, a, a));
    assert!(r);
    assert_eq!(t, 3);
}

fn check_bounds(x: &TSpan) {
    let mut s = Store::new();
    let p = put_span(&mut s, x);
    let r = right_bound(&mut s, p).map(|b| get_span(&mut s, b));
    assert_eq!(r, common::iface(&x.r, &x.c), "right of {x:?}");
    let l = left_bound(&mut s, p).map(|b| get_span(&mut s, b));
    assert_eq!(l, common::iface(&x.l, &x.c), "left of {x:?}");
}

#[test]
fn a_variable_side_without_constraints_has_no_bound() {
    let mut s = Store::new();
    let p = put_span(&mut s, &span(v(3), sy(0)));
    assert!(left_bound(&mut s, p).is_none());
    assert!(right_bound(&mut s, p).is_some());
}

#[test]
fn a_variable_side_with_a_constraint_on_it_has_a_bound() {
    check_bounds(&TSpan { l: v(0), r: v(1), c: vec![ap(sy(0), v(0))] });
}

#[test]
fn bounds_keep_exactly_the_constraints_on_their_variables() {
    let cs = vec![
        ap(sy(0), v(0)),
        ap(v(0), v(1)),
        sy(1),
        ap(sy(0), v(2)),
        v(1),
        ap(ap(v(1), v(1)), sy(0)),
    ];
    for l in terms(1) {
        for r in terms(1).iter().step_by(3) {
            check_bounds(&TSpan { l: l.clone(), r: r.clone(), c: cs.clone() });
        }
    }
}

#[test]
fn a_variable_is_not_marked_by_a_longer_variable_that_contains_its_node() {
    // The node of variable 3 is built on the node of variable 1.
    check_bounds(&TSpan { l: v(3), r: v(1), c: vec![v(1), v(3), v(0), v(7)] });
}

#[test]
fn bounds_keep_the_order_and_repetitions_of_constraints() {
    check_bounds(&TSpan { l: ap(v(0), v(1)), r: sy(0), c: vec![v(1), v(0), v(1), v(2), v(0)] });
}

fn put_chain(s: &mut Store, xs: &[TSpan]) -> TermId {
    match xs.split_first() {
        None => s.alloc(Node::Nil),
        Some((h, rest)) => {
            let r = put_chain(s, rest);
            let x = put_span(s, h);
            let p = pack_span(s, x);
            s.alloc(Node::App(p, r))
        }
    }
}

fn check_chain(xs: &[TSpan]) {
    let mut s = Store::new();
    let p = put_chain(&mut s, xs);
    assert_eq!(composable(&mut s, p), common::chain_composes(xs), "{xs:?}");
}

#[test]
fn the_empty_chain_and_a_single_span_compose() {
    check_chain(&[]);
    check_chain(&[span(sy(0), sy(1))]);
    let mut s = Store::new();
    let p = put_chain(&mut s, &[]);
    assert!(composable(&mut s, p));
}

#[test]
fn chains_agree_with_the_specification() {
    let ts = terms(1);
    let spans: Vec<TSpan> = ts
        .iter()
        .step_by(3)
        .flat_map(|l| ts.iter().step_by(4).map(move |r| span(l.clone(), r.clone())))
        .collect();
    let mut yes = 0;
    let mut no = 0;
    for a in spans.iter().step_by(2) {
        for b in spans.iter().step_by(3) {
            for c in spans.iter().step_by(5) {
                let xs = [a.clone(), b.clone(), c.clone()];
                if common::chain_composes(&xs) {
                    yes += 1;
                } else {
                    no += 1;
                }
                check_chain(&xs);
            }
        }
    }
    assert!(yes > 10 && no > 10, "{yes} compose, {no} do not");
}

#[test]
fn a_chain_fails_at_a_later_link() {
    let f = |a: u32, b: u32| span(sy(a), sy(b));
    check_chain(&[f(0, 1), f(1, 2), f(3, 4), f(4, 5)]);
    let mut s = Store::new();
    let p = put_chain(&mut s, &[f(0, 1), f(1, 2), f(3, 4), f(4, 5)]);
    assert!(!composable(&mut s, p));
}
