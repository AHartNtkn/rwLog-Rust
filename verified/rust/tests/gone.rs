//! The ground term an exclusion excludes a variable from, when that is all
//! the exclusion says (`sorts::unit_on`), and the terms a list of exclusions
//! excludes a variable from (`sorts::gone`), against `unitOn` and `gone` of
//! the specification (`lean/RwLog/Sorts/Gone.lean`) as the reference on
//! trees has them.

mod common;

use common::sorts::*;
use common::{get, get_list, put_var, T};
use rwlog_core::sorts::{gone, unit_on};
use rwlog_core::store::{Frame, Store, Tbl};

// Symbols.
const A: u32 = 0;
const B: u32 = 1;
const C: u32 = 2;
const F: u32 = 3;
const G: u32 = 4;
const H: u32 = 5;

// Variables. `X` is not the variable `0`, whose node is the first of every
// store.
const X: usize = 5;
const Y: usize = 6;

fn a() -> P {
    pf(A, vec![])
}
fn b() -> P {
    pf(B, vec![])
}
fn c() -> P {
    pf(C, vec![])
}
fn x() -> P {
    pv(X)
}
fn y() -> P {
    pv(Y)
}
fn f1(p: P) -> P {
    pf(F, vec![p])
}
fn f2(p: P, q: P) -> P {
    pf(F, vec![p, q])
}
fn g1(p: P) -> P {
    pf(G, vec![p])
}
fn g2(p: P, q: P) -> P {
    pf(G, vec![p, q])
}
fn h2(p: P, q: P) -> P {
    pf(H, vec![p, q])
}

type Eqs = Vec<(P, P)>;

/// `unit_on` in a store that `prep` has used first, read back as a tree.
fn unit_in(prep: impl FnOnce(&mut Store), v: usize, e: &[(P, P)]) -> Option<T> {
    let mut s = Store::new();
    prep(&mut s);
    let vi = put_var(&mut s, v as u128);
    let ei = put_eqns(&mut s, e);
    let got = unit_on(&mut s, vi, ei);
    assert!(s.pop().is_none(), "the stack is not empty");
    got.map(|g| get(&mut s, g))
}

/// The answer written by hand is the answer of the store and of the
/// reference.
fn unit_is(v: usize, e: &[(P, P)], want: Option<P>) {
    assert_eq!(common::sorts::unit_on(v, e), want, "the reference on {:?}", e);
    assert_eq!(unit_in(|_| (), v, e), want.map(|g| g.tree()), "the store on {:?}", e);
}

/// `gone` in the store, read back as trees.
fn gone_in(x: &[Eqs], v: usize) -> Vec<T> {
    let mut s = Store::new();
    let xi = put_excls(&mut s, x);
    let vi = put_var(&mut s, v as u128);
    let got = gone(&mut s, xi, vi);
    assert!(s.pop().is_none(), "the stack is not empty");
    get_list(&mut s, got)
}

fn gone_is(x: &[Eqs], v: usize, want: &[P]) {
    assert_eq!(common::sorts::gone(x, v), want, "the reference on {:?}", x);
    let trees: Vec<T> = want.iter().map(P::tree).collect();
    assert_eq!(gone_in(x, v), trees, "the store on {:?}", x);
}

// One equation that binds the variable to a ground term.

#[test]
fn a_variable_equated_to_a_constant_is_excluded_from_it() {
    unit_is(X, &[(x(), a())], Some(a()));
}

#[test]
fn the_variable_may_be_on_the_right() {
    unit_is(X, &[(a(), x())], Some(a()));
}

#[test]
fn a_variable_equated_to_a_ground_term_with_arguments_is_excluded_from_it() {
    unit_is(X, &[(x(), f2(a(), b()))], Some(f2(a(), b())));
}

#[test]
fn the_variable_may_be_below_a_symbol_on_both_sides() {
    unit_is(X, &[(f1(x()), f1(a()))], Some(a()));
}

#[test]
fn two_places_of_the_variable_with_one_value_are_one_exclusion() {
    unit_is(X, &[(f2(x(), x()), f2(a(), a()))], Some(a()));
}

#[test]
fn two_places_of_the_variable_with_two_values_never_hold() {
    unit_is(X, &[(f2(x(), x()), f2(a(), b()))], None);
}

// More than one equation.

#[test]
fn the_same_equation_twice_is_one_exclusion() {
    unit_is(X, &[(x(), a()), (x(), a())], Some(a()));
}

#[test]
fn two_values_for_the_variable_never_hold() {
    unit_is(X, &[(x(), a()), (x(), b())], None);
}

#[test]
fn an_equation_that_always_holds_beside_it_changes_nothing() {
    unit_is(X, &[(x(), a()), (a(), a())], Some(a()));
    unit_is(X, &[(x(), a()), (y(), y())], Some(a()));
}

#[test]
fn an_equation_that_never_holds_after_the_variable_is_bound_gives_nothing() {
    unit_is(X, &[(x(), a()), (f1(a()), b())], None);
}

// Equations that do not say one ground value for the variable.

#[test]
fn no_equation_excludes_nothing() {
    unit_is(X, &[], None);
}

#[test]
fn equations_without_a_variable_exclude_nothing() {
    unit_is(X, &[(a(), a())], None);
    unit_is(X, &[(a(), b())], None);
    unit_is(X, &[(f1(a()), a())], None);
}

#[test]
fn the_variable_equated_to_itself_excludes_nothing() {
    unit_is(X, &[(x(), x())], None);
}

#[test]
fn an_equation_on_another_variable_excludes_nothing_of_this_one() {
    unit_is(X, &[(y(), a())], None);
    unit_is(Y, &[(x(), a())], None);
}

#[test]
fn two_variables_equated_exclude_no_ground_term() {
    unit_is(X, &[(x(), y())], None);
    unit_is(X, &[(y(), x())], None);
}

#[test]
fn a_value_with_a_variable_is_not_ground() {
    unit_is(X, &[(x(), f1(y()))], None);
}

#[test]
fn another_variable_bound_beside_it_is_more_than_one_exclusion() {
    unit_is(X, &[(x(), a()), (y(), b())], None);
}

#[test]
fn another_variable_bound_through_this_one_is_more_than_one_exclusion() {
    unit_is(X, &[(y(), x()), (x(), a())], None);
    unit_is(X, &[(x(), y()), (y(), a())], None);
}

#[test]
fn a_ground_value_reached_through_another_bound_variable_gives_nothing() {
    unit_is(X, &[(x(), f1(y())), (y(), a())], None);
    unit_is(X, &[(y(), f1(x())), (x(), a())], None);
}

#[test]
fn another_variable_bound_to_a_term_of_this_one_gives_nothing() {
    unit_is(X, &[(y(), f1(x()))], None);
}

#[test]
fn a_variable_inside_its_own_value_never_holds() {
    unit_is(X, &[(x(), f1(x()))], None);
    unit_is(X, &[(x(), f1(y())), (y(), g1(x()))], None);
}

// Shared subterms.

#[test]
fn a_shared_ground_term_on_both_sides_is_found_once() {
    let t = f2(a(), a());
    unit_is(X, &[(g2(x(), t.clone()), g2(t.clone(), x()))], Some(t));
}

#[test]
fn the_excluded_term_is_the_node_of_the_equation() {
    let t = f2(a(), a());
    let big = h2(t.clone(), t);
    let mut s = Store::new();
    let vi = put_var(&mut s, X as u128);
    let bi = put_pat(&mut s, &big);
    let ei = put_eqns(&mut s, &[(x(), big)]);
    match unit_on(&mut s, vi, ei) {
        Some(g) => assert!(s.same(g, bi), "another node than that of the equation"),
        None => panic!("nothing found"),
    }
}

// The variable `0`, and a store that has been used.

#[test]
fn the_variable_zero_is_a_variable_like_another() {
    unit_is(0, &[(pv(0), a())], Some(a()));
    unit_is(0, &[(x(), a())], None);
    unit_is(X, &[(pv(0), a())], None);
}

#[test]
fn what_the_tables_held_before_does_not_matter() {
    let dirty = |s: &mut Store| {
        let xi = put_var(s, X as u128);
        let ai = put_pat(s, &a());
        let bi = put_pat(s, &b());
        s.set(Tbl::A, xi, bi);
        s.set(Tbl::A, ai, bi);
        s.set_flag(Tbl::B, xi, false);
        s.set_flag(Tbl::B, ai, false);
        s.set_flag(Tbl::A, bi, true);
    };
    assert_eq!(unit_in(dirty, X, &[(x(), a())]), Some(a().tree()));
    assert_eq!(unit_in(dirty, X, &[(x(), f1(y()))]), None);
}

// Lists of exclusions.

#[test]
fn no_exclusion_excludes_nothing() {
    gone_is(&[], X, &[]);
}

#[test]
fn one_exclusion_gives_its_term() {
    gone_is(&[vec![(x(), a())]], X, &[a()]);
}

#[test]
fn the_terms_come_in_the_order_of_the_exclusions() {
    gone_is(&[vec![(x(), a())], vec![(x(), b())]], X, &[a(), b()]);
    gone_is(&[vec![(x(), b())], vec![(x(), a())]], X, &[b(), a()]);
}

#[test]
fn exclusions_of_other_variables_are_passed_over() {
    gone_is(&[vec![(x(), a())], vec![(y(), c())], vec![(x(), b())]], X, &[a(), b()]);
    gone_is(&[vec![(x(), a())], vec![(y(), b())]], Y, &[b()]);
}

#[test]
fn a_term_excluded_twice_is_listed_twice() {
    gone_is(&[vec![(x(), a())], vec![(x(), a())]], X, &[a(), a()]);
}

#[test]
fn exclusions_that_say_something_else_give_nothing() {
    gone_is(&[vec![(y(), a())], vec![(a(), b())], vec![]], X, &[]);
    gone_is(&[vec![(x(), a()), (y(), b())], vec![(x(), c())]], X, &[c()]);
}

#[test]
fn an_exclusion_that_never_holds_does_not_lose_the_others() {
    gone_is(&[vec![(x(), f1(x()))], vec![(x(), a())]], X, &[a()]);
    gone_is(&[vec![(x(), a())], vec![(x(), f1(x()))], vec![(x(), b())]], X, &[a(), b()]);
}

#[test]
fn the_stack_is_left_empty_when_it_was_empty() {
    let mut s = Store::new();
    let xi = put_excls(&mut s, &[vec![(x(), f1(x()))], vec![(x(), a())]]);
    let vi = put_var(&mut s, X as u128);
    let _ = gone(&mut s, xi, vi);
    s.push(Frame::Visit(vi, vi));
    assert!(s.pop().is_some());
    assert!(s.pop().is_none());
}

// Every list of two equations over a few small terms.

#[test]
fn every_pair_of_small_equations_agrees_with_the_reference() {
    let terms = [x(), y(), a(), b(), f1(x()), f1(y()), f1(a()), f2(x(), a()), f2(a(), y())];
    for p in &terms {
        for q in &terms {
            for r in &terms {
                for t in [a(), x(), f1(y())] {
                    let e = vec![(p.clone(), q.clone()), (r.clone(), t)];
                    for v in [X, Y] {
                        let want = common::sorts::unit_on(v, &e).map(|g| g.tree());
                        assert_eq!(unit_in(|_| (), v, &e), want, "{:?} on {}", e, v);
                    }
                }
            }
        }
    }
}
