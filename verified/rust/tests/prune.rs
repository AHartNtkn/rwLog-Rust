//! Dropping the hidden variables of a store: the solved form of an
//! exclusion (`sorts::solved_ex`), and the exclusions and entries that are
//! over the variables of the pattern (`sorts::prune`); against `solvedEx`,
//! `pruneX` and `CStore.prune` of the specification
//! (`lean/RwLog/Sorts/Prune.lean`), with the most general solution written
//! on trees (`common::sorts::mgu`).
//!
//! An exclusion is a list of equations and says that they do not all hold.
//! Its solved form is the list of the equations `variable = value`, one for
//! each variable its most general solution moves, in the order the variables
//! first occur in it. A variable is hidden when it is not one of the
//! variables of the pattern. When every variable has infinitely many values,
//! an exclusion whose solved form mentions a hidden variable excludes
//! nothing, as the hidden variable can be chosen to avoid it; one without a
//! solution excludes nothing either; and any other says what its solved form
//! says.
//!
//! Where the solution makes two variables equal and neither a term, which of
//! the two is moved is not specified, and the tests accept either.

mod common;

use common::decls::*;
use common::sorts::*;
use common::{get_list, put_var, T};
use rwlog_core::sorts::{prune, solved_ex};
use rwlog_core::store::{Node, Tbl, TermId};
use std::collections::BTreeMap;

type Eqs = Vec<(P, P)>;
/// A solved form: the variables moved, each with its value, in order.
type Solved = Vec<(usize, P)>;

// The variables of the pattern in most tests, and two hidden ones.
fn x() -> P {
    pv(0)
}
fn y() -> P {
    pv(1)
}
fn w() -> P {
    pv(2)
}
fn h() -> P {
    pv(7)
}
fn k() -> P {
    pv(8)
}
const X: usize = 0;
const Y: usize = 1;
const W: usize = 2;
const HID: usize = 7;

/// A constant that is not `z` or `a`.
fn b() -> P {
    pf(8, vec![])
}

fn fx() -> Fx {
    fixture(wf())
}

/// A first-order term read back from a tree.
fn pat_of(t: &T) -> P {
    match t {
        T::V(n) => pv(*n as usize),
        T::S(f) => pf(*f, vec![]),
        T::A(l, r) => match pat_of(l) {
            P::F(f, mut args) => {
                args.push(pat_of(r));
                pf(f, args)
            }
            P::V(_) => panic!("a variable applied to {r:?}"),
        },
    }
}

/// A solved form read back: every left side must be a variable.
fn read_solved(f: &mut Fx, r: TermId) -> Solved {
    get_list(&mut f.s, r)
        .iter()
        .map(|eq| match eq {
            T::A(l, p) => match **l {
                T::V(n) => (n as usize, pat_of(p)),
                _ => panic!("the left side of {eq:?} is not a variable"),
            },
            _ => panic!("{eq:?} is not an equation"),
        })
        .collect()
}

fn read_solveds(f: &mut Fx, mut p: TermId) -> Vec<Solved> {
    let mut out = Vec::new();
    loop {
        match f.s.read(p) {
            Node::Nil => return out,
            Node::App(e, rest) => {
                out.push(read_solved(f, e));
                p = rest;
            }
            _ => panic!("a term where a list was expected"),
        }
    }
}

fn as_eqs(l: &[(usize, P)]) -> Eqs {
    l.iter().map(|(v, p)| (pv(*v), p.clone())).collect()
}

fn put_solved(f: &mut Fx, l: &[(usize, P)]) -> TermId {
    put_eqns(&mut f.s, &as_eqs(l))
}

fn put_vars(f: &mut Fx, ks: &[usize]) -> TermId {
    let ps: Vec<P> = ks.iter().map(|v| pv(*v)).collect();
    put_pats(&mut f.s, &ps)
}

/// The variables of the equations, once each, in the order they first
/// occur reading left to right.
fn vars_in_order(e: &[(P, P)]) -> Vec<usize> {
    let mut out = Vec::new();
    for (l, r) in e {
        l.vars(&mut out);
        r.vars(&mut out);
    }
    out
}

/// Every variable a solved form mentions: the ones moved and the ones in
/// their values.
fn mentioned(l: &[(usize, P)]) -> Vec<usize> {
    vars_in_order(&as_eqs(l))
}

/// Tables with entries and flags left by earlier work, on the variables,
/// the symbols and the lists the functions are about to read.
fn dirty(f: &mut Fx, lists: &[TermId]) {
    let zi = put_pat(&mut f.s, &z());
    let ai = put_pat(&mut f.s, &a());
    for n in [X, Y, W, HID] {
        let vi = put_var(&mut f.s, n as u128);
        f.s.set(Tbl::A, vi, zi);
        f.s.set(Tbl::B, vi, ai);
    }
    f.s.set(Tbl::A, zi, ai);
    f.s.set(Tbl::B, ai, zi);
    let v8 = put_var(&mut f.s, 8);
    f.s.set_flag(Tbl::A, v8, true);
    f.s.set_flag(Tbl::B, v8, true);
    for l in lists {
        f.s.set_flag(Tbl::B, *l, true);
        f.s.set(Tbl::A, *l, zi);
    }
}

// The solved form of an exclusion.

/// `got` is a solved form of the equations `e`, whichever variable of two
/// that are made equal it moves: its variables are variables of `e`, each
/// once, in the order they first occur in `e`; each is moved; none occurs in
/// a value; and it has the solutions of `e`, which is that its own most
/// general solution on trees is that of `e`.
fn fits(e: &[(P, P)], got: &[(usize, P)]) {
    let theta = mgu(e).unwrap_or_else(|| panic!("the reference has no solution of {e:?}"));
    let order = vars_in_order(e);
    let keys: Vec<usize> = got.iter().map(|(v, _)| *v).collect();
    let places: Vec<usize> = keys
        .iter()
        .map(|v| order.iter().position(|o| o == v).unwrap_or_else(|| panic!("{v} is not a variable of {e:?}")))
        .collect();
    assert!(places.windows(2).all(|p| p[0] < p[1]), "{got:?} is not in the order of the variables of {e:?}");
    for (v, p) in got {
        assert_ne!(*p, pv(*v), "{v} is not moved in {got:?}");
        let mut vs = Vec::new();
        p.vars(&mut vs);
        assert!(vs.iter().all(|u| !keys.contains(u)), "a moved variable occurs in the value of {v} in {got:?}");
    }
    let again = mgu(&as_eqs(got)).unwrap_or_else(|| panic!("{got:?} has no solution"));
    assert_eq!(again, theta, "{got:?} does not have the solutions of {e:?}");
    assert_eq!(got.len(), theta.len(), "{got:?} moves another number of variables than the reference");
}

/// `solved_ex` of the equations, read back, with the node. The stack is
/// empty afterwards.
fn run_solved(f: &mut Fx, e: &[(P, P)], soiled: bool) -> Option<(TermId, Solved)> {
    let ei = put_eqns(&mut f.s, e);
    if soiled {
        dirty(f, &[ei]);
    }
    let r = solved_ex(&mut f.s, ei);
    f.empty_stack();
    r.map(|r| (r, read_solved(f, r)))
}

/// The solved form of `e` is `want`, node for node. This is for equations
/// whose solution makes no two variables equal without giving them a term,
/// so that there is one solved form, that of the reference.
fn solved_is(e: &[(P, P)], want: &[(usize, P)]) {
    let theta = mgu(e).expect("the reference has no solution");
    assert!(theta.values().all(|p| !matches!(p, P::V(_))), "the orientation of {e:?} is not determined");
    let by_hand: BTreeMap<usize, P> = want.iter().cloned().collect();
    assert_eq!(by_hand, theta, "the reference");
    let mut f = fx();
    let (r, got) = run_solved(&mut f, e, false).expect("a solved form");
    assert_eq!(got, want, "{e:?}");
    fits(e, &got);
    let wi = put_solved(&mut f, want);
    assert!(f.s.same(r, wi), "the solved form of {e:?} is another node");
}

/// The solved form of `e` is one of `wants`, which differ in which of two
/// equal variables is moved.
fn solved_is_one_of(e: &[(P, P)], wants: &[Solved]) {
    for want in wants {
        fits(e, want);
    }
    let mut f = fx();
    let (_, got) = run_solved(&mut f, e, false).expect("a solved form");
    fits(e, &got);
    assert!(wants.contains(&got), "{got:?} for {e:?}");
}

/// The equations have no solution, in the store and in the reference.
fn solved_none(e: &[(P, P)]) {
    assert!(mgu(e).is_none(), "the reference solves {e:?}");
    let mut f = fx();
    assert!(run_solved(&mut f, e, false).is_none(), "{e:?} has a solved form");
}

fn chain(n: usize, end: P) -> P {
    (0..n).fold(end, |p, _| su(p))
}

#[test]
fn solved_ex_of_no_equations_is_the_empty_list() {
    solved_is(&[], &[]);
}

#[test]
fn solved_ex_of_a_variable_equal_to_itself_is_the_empty_list() {
    solved_is(&[(x(), x())], &[]);
}

#[test]
fn solved_ex_of_equal_ground_terms_is_the_empty_list() {
    solved_is(&[(z(), z()), (pr(su(z()), a()), pr(su(z()), a()))], &[]);
}

#[test]
fn solved_ex_of_equal_terms_with_variables_is_the_empty_list() {
    solved_is(&[(pr(x(), su(y())), pr(x(), su(y())))], &[]);
}

#[test]
fn solved_ex_of_different_constants_is_none() {
    solved_none(&[(z(), a())]);
}

#[test]
fn solved_ex_of_a_constant_and_an_application_is_none() {
    solved_none(&[(z(), su(z()))]);
    solved_none(&[(su(z()), z())]);
}

#[test]
fn solved_ex_of_a_clash_under_a_common_root_is_none() {
    solved_none(&[(pr(x(), z()), pr(y(), a()))]);
}

#[test]
fn solved_ex_of_a_clash_after_a_solvable_equation_is_none() {
    solved_none(&[(x(), a()), (z(), b())]);
}

#[test]
fn solved_ex_of_one_variable_given_two_values_is_none() {
    solved_none(&[(x(), a()), (x(), b())]);
}

#[test]
fn solved_ex_of_a_variable_equal_to_a_term_over_itself_is_none() {
    solved_none(&[(x(), su(x()))]);
    solved_none(&[(pr(y(), x()), x())]);
}

#[test]
fn solved_ex_of_an_occurs_check_through_another_variable_is_none() {
    solved_none(&[(x(), su(y())), (y(), x())]);
    solved_none(&[(x(), su(y())), (y(), pr(x(), z()))]);
}

#[test]
fn solved_ex_binds_a_variable_to_a_ground_term() {
    solved_is(&[(x(), su(z()))], &[(X, su(z()))]);
}

#[test]
fn solved_ex_puts_the_variable_on_the_left_when_it_was_written_on_the_right() {
    solved_is(&[(a(), x())], &[(X, a())]);
    solved_is(&[(pr(z(), y()), x())], &[(X, pr(z(), y()))]);
}

#[test]
fn solved_ex_binds_a_variable_to_a_term_with_variables_and_lists_only_the_moved_one() {
    solved_is(&[(x(), pr(y(), su(w())))], &[(X, pr(y(), su(w())))]);
}

#[test]
fn solved_ex_takes_two_terms_apart() {
    solved_is(&[(pr(x(), su(y())), pr(z(), w()))], &[(X, z()), (W, su(y()))]);
}

#[test]
fn solved_ex_leaves_out_the_equations_that_always_hold() {
    solved_is(&[(h(), h()), (x(), a()), (z(), z())], &[(X, a())]);
    solved_is(&[(f2(h(), x()), f2(h(), a()))], &[(X, a())]);
}

#[test]
fn solved_ex_lists_the_variables_in_the_order_they_first_occur_and_not_by_number() {
    solved_is(&[(pv(5), a()), (pv(2), b())], &[(5, a()), (2, b())]);
    solved_is(&[(y(), a()), (x(), b())], &[(Y, a()), (X, b())]);
}

#[test]
fn solved_ex_lists_the_variables_in_the_order_they_first_occur_and_not_as_they_are_eliminated() {
    // `x` is eliminated before `y`, and `y` occurs first.
    solved_is(&[(pr(su(y()), a()), pr(x(), y()))], &[(Y, a()), (X, su(a()))]);
}

#[test]
fn solved_ex_counts_an_occurrence_on_the_right_of_an_earlier_equation_as_first() {
    solved_is(&[(x(), pr(y(), w())), (w(), a()), (y(), b())], &[(X, pr(b(), a())), (Y, b()), (W, a())]);
}

#[test]
fn solved_ex_replaces_the_moved_variables_in_every_value() {
    solved_is(&[(x(), su(y())), (y(), su(w())), (w(), z())], &[(X, chain(2, z())), (Y, su(z())), (W, z())]);
}

#[test]
fn solved_ex_replaces_a_variable_moved_later_in_a_value_found_earlier() {
    solved_is(&[(x(), pr(y(), y())), (y(), a())], &[(X, pr(a(), a())), (Y, a())]);
}

#[test]
fn solved_ex_gives_two_variables_made_equal_and_a_term_that_term() {
    solved_is(&[(x(), y()), (y(), a())], &[(X, a()), (Y, a())]);
    solved_is(&[(x(), y()), (x(), su(w()))], &[(X, su(w())), (Y, su(w()))]);
}

#[test]
fn solved_ex_of_the_same_equation_twice_is_that_of_one() {
    solved_is(&[(x(), su(y())), (x(), su(y()))], &[(X, su(y()))]);
}

#[test]
fn solved_ex_of_a_repeated_variable_against_two_terms_solves_both() {
    solved_is(&[(pr(x(), x()), pr(su(y()), su(a())))], &[(X, su(a())), (Y, a())]);
}

#[test]
fn solved_ex_of_a_repeated_variable_against_two_different_terms_is_none() {
    solved_none(&[(pr(x(), x()), pr(a(), b()))]);
}

#[test]
fn solved_ex_of_a_repeated_variable_against_a_term_and_a_term_over_it_is_none() {
    solved_none(&[(pr(x(), x()), pr(y(), su(y())))]);
}

#[test]
fn solved_ex_of_a_value_with_a_repeated_subterm_is_one_shared_node() {
    let u = pr(su(y()), su(y()));
    solved_is(&[(x(), pr(u.clone(), u.clone()))], &[(X, pr(u.clone(), u))]);
}

#[test]
fn solved_ex_of_terms_that_double_at_each_equation_has_the_whole_values() {
    // The value of the first variable has `2^5` leaves as a tree.
    let n = 5;
    let mut e: Eqs = (0..n).map(|i| (pv(i), pr(pv(i + 1), pv(i + 1)))).collect();
    e.push((pv(n), z()));
    let mut vals = vec![z()];
    for i in 0..n {
        let last = vals[i].clone();
        vals.push(pr(last.clone(), last));
    }
    let want: Solved = (0..=n).map(|i| (i, vals[n - i].clone())).collect();
    solved_is(&e, &want);
}

#[test]
fn solved_ex_of_a_long_chain_gives_every_variable_its_ground_value() {
    let n = 40;
    let mut e: Eqs = (0..n).map(|i| (pv(i), su(pv(i + 1)))).collect();
    e.push((pv(n), z()));
    let want: Solved = (0..=n).map(|i| (i, chain(n - i, z()))).collect();
    solved_is(&e, &want);
}

#[test]
fn solved_ex_of_a_long_chain_written_from_its_end_keeps_the_order_of_first_occurrence() {
    let n = 40;
    let mut e: Eqs = vec![(pv(n), z())];
    e.extend((0..n).rev().map(|i| (pv(i), su(pv(i + 1)))));
    let mut want: Solved = vec![(n, z())];
    want.extend((0..n).rev().map(|i| (i, chain(n - i, z()))));
    solved_is(&e, &want);
}

#[test]
fn solved_ex_of_two_variables_made_equal_moves_one_of_them() {
    solved_is_one_of(&[(x(), y())], &[vec![(X, y())], vec![(Y, x())]]);
}

#[test]
fn solved_ex_of_two_variables_made_equal_written_the_other_way_moves_one_of_them() {
    solved_is_one_of(&[(y(), x())], &[vec![(Y, x())], vec![(X, y())]]);
}

#[test]
fn solved_ex_of_two_variables_made_equal_twice_moves_one_of_them_once() {
    solved_is_one_of(&[(x(), y()), (y(), x())], &[vec![(X, y())], vec![(Y, x())]]);
}

#[test]
fn solved_ex_of_three_variables_made_equal_moves_two_to_the_third() {
    solved_is_one_of(
        &[(x(), y()), (y(), w())],
        &[
            vec![(X, w()), (Y, w())],
            vec![(X, y()), (W, y())],
            vec![(Y, x()), (W, x())],
        ],
    );
}

#[test]
fn solved_ex_of_variables_made_equal_under_terms_moves_one_of_each_pair() {
    solved_is_one_of(
        &[(pr(x(), su(y())), pr(w(), su(h())))],
        &[
            vec![(X, w()), (Y, h())],
            vec![(X, w()), (HID, y())],
            vec![(Y, h()), (W, x())],
            vec![(W, x()), (HID, y())],
        ],
    );
}

#[test]
fn solved_ex_of_a_value_over_one_of_two_equal_variables_is_written_with_the_one_not_moved() {
    solved_is_one_of(
        &[(x(), su(y())), (y(), w())],
        &[vec![(X, su(w())), (Y, w())], vec![(X, su(y())), (W, y())]],
    );
}

#[test]
fn solved_ex_of_a_long_chain_of_equal_variables_moves_all_but_one_to_it() {
    let n = 30;
    let e: Eqs = (0..n).map(|i| (pv(i), pv(i + 1))).collect();
    let mut f = fx();
    let (_, got) = run_solved(&mut f, &e, false).expect("a solved form");
    fits(&e, &got);
    assert_eq!(got.len(), n, "{got:?}");
    let to = &got[0].1;
    assert!(matches!(to, P::V(_)) && got.iter().all(|(_, p)| p == to), "{got:?}");
}

#[test]
fn solved_ex_of_its_own_result_is_that_result() {
    let cases: Vec<Eqs> = vec![
        vec![],
        vec![(pr(su(y()), a()), pr(x(), y()))],
        vec![(x(), pr(y(), su(w())))],
        vec![(x(), y()), (y(), a())],
        vec![(pr(x(), su(y())), pr(z(), w()))],
    ];
    for e in cases {
        let mut f = fx();
        let (r, got) = run_solved(&mut f, &e, false).expect("a solved form");
        let again = solved_ex(&mut f.s, r).expect("a solved form of a solved form");
        f.empty_stack();
        assert!(f.s.same(again, r), "the solved form of {got:?} is {:?}", read_solved(&mut f, again));
    }
}

#[test]
fn solved_ex_twice_on_the_same_node_gives_the_same_node() {
    let mut f = fx();
    let e = [(pr(x(), su(y())), pr(z(), w())), (y(), k())];
    let ei = put_eqns(&mut f.s, &e);
    let r1 = solved_ex(&mut f.s, ei).expect("a solved form");
    let r2 = solved_ex(&mut f.s, ei).expect("a solved form");
    f.empty_stack();
    assert!(f.s.same(r1, r2));
}

#[test]
fn solved_ex_does_not_read_what_the_tables_held_before() {
    let cases: Vec<Eqs> = vec![
        vec![],
        vec![(x(), a())],
        vec![(h(), h()), (x(), a())],
        vec![(pr(su(y()), a()), pr(x(), y()))],
        vec![(x(), pr(y(), su(w())))],
        vec![(x(), y()), (w(), k())],
        vec![(pr(x(), x()), pr(su(y()), su(a())))],
    ];
    for e in cases {
        let clean = run_solved(&mut fx(), &e, false).expect("a solved form").1;
        let soiled = run_solved(&mut fx(), &e, true).expect("a solved form").1;
        assert_eq!(soiled, clean, "{e:?}");
    }
}

#[test]
fn solved_ex_without_a_solution_does_not_read_what_the_tables_held_before() {
    for e in [vec![(z(), a())], vec![(x(), su(x()))], vec![(x(), a()), (x(), b())]] {
        assert!(run_solved(&mut fx(), &e, true).is_none(), "{e:?}");
    }
}

#[test]
fn solved_ex_leaves_the_stack_empty_with_and_without_a_solution() {
    let mut f = fx();
    assert!(run_solved(&mut f, &[(x(), su(x()))], false).is_none());
    assert!(run_solved(&mut f, &[(pr(x(), z()), pr(y(), a()))], false).is_none());
    assert!(run_solved(&mut f, &[(pr(x(), su(y())), pr(z(), w()))], false).is_some());
    assert!(run_solved(&mut f, &[], false).is_some());
    f.empty_stack();
}

/// The terms with at most one symbol over other terms: two variables, two
/// constants, and `s` and the pair of these.
fn small_terms() -> Vec<P> {
    let leaves = vec![x(), y(), z(), a()];
    let mut out = leaves.clone();
    for l in &leaves {
        out.push(su(l.clone()));
    }
    for l in &leaves {
        for r in &leaves {
            out.push(pr(l.clone(), r.clone()));
        }
    }
    out
}

/// The terms over one variable of the pattern and one hidden variable: the
/// two, two constants, and `s` of these.
fn tiny_terms() -> Vec<P> {
    let leaves = vec![x(), h(), z(), a()];
    let mut out = leaves.clone();
    for l in &leaves {
        out.push(su(l.clone()));
    }
    out
}

fn all_pairs(ts: &[P]) -> Eqs {
    let mut out = Vec::new();
    for l in ts {
        for r in ts {
            out.push((l.clone(), r.clone()));
        }
    }
    out
}

#[test]
fn solved_ex_of_every_small_equation_is_a_solved_form_exactly_when_the_reference_solves_it() {
    let mut f = fx();
    for eq in all_pairs(&small_terms()) {
        let e = vec![eq];
        match (run_solved(&mut f, &e, false), mgu(&e)) {
            (None, None) => {}
            (Some((_, got)), Some(_)) => fits(&e, &got),
            (got, want) => panic!("{e:?}: {:?} against {want:?}", got.map(|g| g.1)),
        }
    }
}

#[test]
fn solved_ex_of_every_two_tiny_equations_is_a_solved_form_exactly_when_the_reference_solves_them() {
    let mut f = fx();
    let eqs = all_pairs(&tiny_terms());
    for e1 in &eqs {
        for e2 in &eqs {
            let e = vec![e1.clone(), e2.clone()];
            match (run_solved(&mut f, &e, false), mgu(&e)) {
                (None, None) => {}
                (Some((_, got)), Some(_)) => fits(&e, &got),
                (got, want) => panic!("{e:?}: {:?} against {want:?}", got.map(|g| g.1)),
            }
        }
    }
}

// The exclusions and the entries over the variables of the pattern.

/// Whether the specification keeps the exclusion `e` at the variables `ks`:
/// it has a solution, and the solved form mentions variables of `ks` only.
/// The variables a solved form mentions do not depend on which of two equal
/// variables it moves, so the reference decides this.
fn keeps_ref(ks: &[usize], e: &[(P, P)]) -> bool {
    match mgu(e) {
        None => false,
        Some(theta) => {
            let l: Solved = theta.into_iter().collect();
            mentioned(&l).iter().all(|v| ks.contains(v))
        }
    }
}

/// `prune` in the store, checked against its specification: the exclusions
/// returned are, in order, solved forms of the exclusions the reference
/// keeps, each the node `solved_ex` gives, and over `ks` only; the entries
/// returned are the entries of the variables of `ks`, in order, as one node
/// with the list written by hand. The stack is empty afterwards. Returned
/// are the places of the exclusions kept, their solved forms, and the
/// entries.
fn run_prune(ks: &[usize], xs: &[Eqs], es: &[(usize, Vec<Name>)], soiled: bool) -> (Vec<usize>, Vec<Solved>, Entries) {
    let mut f = fx();
    let ki = put_vars(&mut f, ks);
    let xi = put_excls(&mut f.s, xs);
    let ei = f.entries(es);
    if soiled {
        dirty(&mut f, &[ki, xi, ei]);
    }
    let (x1, e1) = prune(&mut f.s, ki, xi, ei);
    f.empty_stack();

    let kept: Vec<usize> = (0..xs.len()).filter(|i| keeps_ref(ks, &xs[*i])).collect();
    let got = read_solveds(&mut f, x1);
    assert_eq!(got.len(), kept.len(), "{got:?} are not the exclusions at {kept:?} of {xs:?}");
    let mut nodes = Vec::new();
    for (g, i) in got.iter().zip(&kept) {
        fits(&xs[*i], g);
        assert!(mentioned(g).iter().all(|v| ks.contains(v)), "{g:?} mentions a hidden variable");
        let e = put_eqns(&mut f.s, &xs[*i]);
        nodes.push(solved_ex(&mut f.s, e).expect("a solved form"));
    }
    let mut want_x = f.s.alloc(Node::Nil);
    for n in nodes.into_iter().rev() {
        want_x = f.s.alloc(Node::App(n, want_x));
    }
    assert!(f.s.same(x1, want_x), "{got:?} are not the nodes `solved_ex` gives");

    let want_es: Entries = es.iter().filter(|(v, _)| ks.contains(v)).cloned().collect();
    let got_es = f.read_entries(e1);
    let want_e = f.entries(&want_es);
    assert!(f.s.same(e1, want_e), "the entries are {got_es:?}, not {want_es:?}");
    f.empty_stack();
    (kept, got, got_es)
}

/// At the variables `ks`, the exclusions `xs` are pruned to the solved forms
/// `want`, written by hand, in order.
fn pruned_is(ks: &[usize], xs: &[Eqs], want: &[Solved]) {
    let (_, got, _) = run_prune(ks, xs, &[], false);
    assert_eq!(got, want, "{xs:?} at {ks:?}");
}

/// At the variables `ks`, every exclusion of `xs` is dropped.
fn pruned_away(ks: &[usize], xs: &[Eqs]) {
    pruned_is(ks, xs, &[]);
}

/// At the variables `ks`, the entries `es` are pruned to `want`.
fn entries_are(ks: &[usize], es: &[(usize, Vec<Name>)], want: &[(usize, Vec<Name>)]) {
    let order = fx().order;
    let (_, _, got) = run_prune(ks, &[], es, false);
    let want: Entries =
        want.iter().map(|(v, c)| (*v, canon(&order, &c.iter().copied().collect()))).collect();
    assert_eq!(got, want, "{es:?} at {ks:?}");
}

const KS: [usize; 3] = [X, Y, W];

#[test]
fn prune_of_no_exclusions_and_no_entries_is_empty() {
    let (kept, got, es) = run_prune(&KS, &[], &[], false);
    assert!(kept.is_empty() && got.is_empty() && es.is_empty());
}

#[test]
fn prune_of_no_exclusions_keeps_the_entries_of_the_pattern() {
    entries_are(&KS, &[(X, vec![NAT]), (Y, vec![])], &[(X, vec![NAT]), (Y, vec![])]);
}

#[test]
fn prune_drops_an_exclusion_whose_symbols_clash() {
    pruned_away(&KS, &[vec![(z(), a())]]);
    pruned_away(&KS, &[vec![(pr(x(), z()), pr(y(), a()))]]);
}

#[test]
fn prune_drops_an_exclusion_that_gives_one_variable_two_values() {
    pruned_away(&KS, &[vec![(x(), a()), (x(), b())]]);
}

#[test]
fn prune_drops_an_exclusion_that_fails_the_occurs_check() {
    pruned_away(&KS, &[vec![(x(), su(x()))]]);
    pruned_away(&KS, &[vec![(x(), su(y())), (y(), x())]]);
}

#[test]
fn prune_drops_an_exclusion_without_a_solution_over_hidden_variables() {
    pruned_away(&KS, &[vec![(h(), su(h()))]]);
    pruned_away(&KS, &[vec![(h(), a()), (h(), b())]]);
}

#[test]
fn prune_keeps_an_exclusion_without_equations_as_the_empty_list() {
    pruned_is(&KS, &[vec![]], &[vec![]]);
}

#[test]
fn prune_keeps_an_exclusion_that_always_holds_as_the_empty_list() {
    pruned_is(&KS, &[vec![(x(), x())]], &[vec![]]);
    pruned_is(&KS, &[vec![(z(), z())]], &[vec![]]);
}

#[test]
fn prune_keeps_an_exclusion_that_always_holds_over_a_hidden_variable_as_the_empty_list() {
    pruned_is(&KS, &[vec![(h(), h())]], &[vec![]]);
    pruned_is(&KS, &[vec![(pr(h(), su(k())), pr(h(), su(k())))]], &[vec![]]);
}

#[test]
fn prune_keeps_an_exclusion_of_a_pattern_variable_from_a_ground_term() {
    pruned_is(&KS, &[vec![(x(), su(z()))]], &[vec![(X, su(z()))]]);
}

#[test]
fn prune_writes_a_kept_exclusion_with_the_variable_on_the_left() {
    pruned_is(&KS, &[vec![(a(), x())]], &[vec![(X, a())]]);
}

#[test]
fn prune_keeps_an_exclusion_of_a_pattern_variable_from_a_term_over_pattern_variables() {
    pruned_is(&KS, &[vec![(x(), pr(y(), su(w())))]], &[vec![(X, pr(y(), su(w())))]]);
}

#[test]
fn prune_keeps_an_exclusion_between_terms_over_pattern_variables_as_its_solved_form() {
    pruned_is(&KS, &[vec![(pr(x(), su(y())), pr(z(), w()))]], &[vec![(X, z()), (W, su(y()))]]);
}

#[test]
fn prune_keeps_an_exclusion_between_two_pattern_variables() {
    let (kept, got, _) = run_prune(&KS, &[vec![(x(), y())]], &[], false);
    assert_eq!(kept, [0]);
    assert!(got == [vec![(X, y())]] || got == [vec![(Y, x())]], "{got:?}");
}

#[test]
fn prune_drops_an_exclusion_of_a_hidden_variable_from_a_ground_term() {
    pruned_away(&KS, &[vec![(h(), z())]]);
    pruned_away(&KS, &[vec![(su(z()), h())]]);
}

#[test]
fn prune_drops_an_exclusion_of_a_hidden_variable_from_a_term_over_pattern_variables() {
    pruned_away(&KS, &[vec![(h(), pr(x(), y()))]]);
}

#[test]
fn prune_drops_an_exclusion_of_a_pattern_variable_from_a_term_over_a_hidden_variable() {
    pruned_away(&KS, &[vec![(x(), su(h()))]]);
    pruned_away(&KS, &[vec![(pr(y(), su(h())), x())]]);
}

#[test]
fn prune_drops_an_exclusion_whose_solved_form_has_a_hidden_variable_next_to_pattern_ones() {
    // `x = a` alone would be kept; with `y = (s h)` the whole is avoided.
    pruned_away(&KS, &[vec![(x(), a()), (y(), su(h()))]]);
    pruned_away(&KS, &[vec![(pr(x(), y()), pr(a(), su(h())))]]);
}

#[test]
fn prune_drops_an_exclusion_between_two_hidden_variables() {
    pruned_away(&KS, &[vec![(h(), k())]]);
    pruned_away(&KS, &[vec![(k(), h())]]);
}

#[test]
fn prune_drops_an_exclusion_of_a_pattern_variable_from_a_hidden_one() {
    pruned_away(&KS, &[vec![(x(), h())]]);
}

#[test]
fn prune_drops_an_exclusion_of_a_hidden_variable_from_a_pattern_one() {
    pruned_away(&KS, &[vec![(h(), x())]]);
}

#[test]
fn prune_drops_an_exclusion_between_a_pattern_and_a_hidden_variable_under_terms() {
    pruned_away(&KS, &[vec![(su(x()), su(h()))]]);
    pruned_away(&KS, &[vec![(pr(h(), z()), pr(x(), z()))]]);
}

#[test]
fn prune_keeps_the_rest_of_an_exclusion_that_equates_a_hidden_variable_with_itself() {
    pruned_is(&KS, &[vec![(h(), h()), (x(), a())]], &[vec![(X, a())]]);
    pruned_is(&KS, &[vec![(x(), a()), (h(), h())]], &[vec![(X, a())]]);
}

#[test]
fn prune_keeps_the_rest_of_an_exclusion_with_a_hidden_variable_at_the_same_place_on_both_sides() {
    pruned_is(&KS, &[vec![(f2(h(), x()), f2(h(), a()))]], &[vec![(X, a())]]);
    pruned_is(&KS, &[vec![(pr(su(h()), x()), pr(su(h()), su(y())))]], &[vec![(X, su(y()))]]);
}

#[test]
fn prune_drops_a_chain_from_a_pattern_variable_through_a_hidden_one_to_a_ground_term() {
    // The solution gives `x` the ground term, and `h` too.
    pruned_away(&KS, &[vec![(x(), h()), (h(), a())]]);
    pruned_away(&KS, &[vec![(h(), a()), (x(), h())]]);
}

#[test]
fn prune_drops_two_pattern_variables_made_equal_through_a_hidden_one() {
    // Not `x != y`: the hidden variable can differ from both.
    pruned_away(&KS, &[vec![(x(), h()), (y(), h())]]);
    pruned_away(&KS, &[vec![(x(), su(h())), (y(), su(h()))]]);
}

#[test]
fn prune_drops_a_chain_through_two_hidden_variables() {
    pruned_away(&KS, &[vec![(x(), su(h())), (h(), pr(k(), k())), (k(), z())]]);
}

#[test]
fn prune_keeps_a_chain_through_pattern_variables_with_every_value_replaced() {
    pruned_is(
        &KS,
        &[vec![(x(), su(y())), (y(), su(w())), (w(), z())]],
        &[vec![(X, chain(2, z())), (Y, su(z())), (W, z())]],
    );
}

#[test]
fn prune_lists_the_equations_of_a_kept_exclusion_by_first_occurrence_of_the_variables() {
    pruned_is(&KS, &[vec![(pr(su(y()), a()), pr(x(), y()))]], &[vec![(Y, a()), (X, su(a()))]]);
}

#[test]
fn prune_keeps_the_survivors_in_the_order_of_the_exclusions() {
    let xs: Excls = vec![
        vec![(y(), b())],
        vec![(x(), h())],
        vec![(x(), a())],
        vec![(z(), a())],
        vec![(w(), su(x()))],
        vec![(h(), z())],
        vec![(x(), z())],
    ];
    let (kept, got, _) = run_prune(&KS, &xs, &[], false);
    assert_eq!(kept, [0, 2, 4, 6]);
    assert_eq!(got, [vec![(Y, b())], vec![(X, a())], vec![(W, su(x()))], vec![(X, z())]]);
}

#[test]
fn prune_keeps_an_exclusion_that_always_holds_at_its_place_among_the_others() {
    let xs: Excls = vec![vec![(x(), a())], vec![(h(), h())], vec![(y(), b())]];
    pruned_is(&KS, &xs, &[vec![(X, a())], vec![], vec![(Y, b())]]);
}

#[test]
fn prune_keeps_the_same_exclusion_listed_twice_twice() {
    let xs: Excls = vec![vec![(x(), a())], vec![(x(), a())]];
    pruned_is(&KS, &xs, &[vec![(X, a())], vec![(X, a())]]);
}

#[test]
fn prune_keeps_two_exclusions_with_one_solved_form_twice() {
    let xs: Excls = vec![vec![(x(), a())], vec![(su(x()), su(a())), (h(), h())]];
    pruned_is(&KS, &xs, &[vec![(X, a())], vec![(X, a())]]);
}

#[test]
fn prune_keeps_an_exclusion_with_a_repeated_subterm_over_pattern_variables() {
    let u = pr(su(y()), su(y()));
    pruned_is(&KS, &[vec![(x(), pr(u.clone(), u.clone()))]], &[vec![(X, pr(u.clone(), u))]]);
}

#[test]
fn prune_finds_a_hidden_variable_under_a_repeated_subterm() {
    let u = pr(su(h()), su(y()));
    pruned_away(&KS, &[vec![(x(), pr(u.clone(), u))]]);
    let d = pr(y(), y());
    pruned_away(&KS, &[vec![(x(), pr(d.clone(), pr(d, h())))]]);
}

#[test]
fn prune_judges_each_of_two_exclusions_that_share_a_subterm_on_its_own() {
    let u = su(pr(y(), w()));
    let xs: Excls = vec![vec![(x(), u.clone())], vec![(h(), u.clone())], vec![(x(), pr(u.clone(), u.clone()))]];
    pruned_is(&KS, &xs, &[vec![(X, u.clone())], vec![(X, pr(u.clone(), u))]]);
}

#[test]
fn prune_takes_the_variables_of_the_pattern_in_any_order() {
    let xs: Excls = vec![vec![(pv(3), su(x()))], vec![(y(), z())]];
    pruned_is(&[3, 0], &xs, &[vec![(3, su(x()))]]);
    entries_are(&[3, 0], &[(0, vec![NAT]), (1, vec![NAT]), (3, vec![BOX])], &[(0, vec![NAT]), (3, vec![BOX])]);
}

#[test]
fn prune_treats_a_variable_as_hidden_only_when_it_is_not_of_the_pattern() {
    let xs: Excls = vec![vec![(x(), su(h()))]];
    pruned_away(&KS, &xs);
    pruned_is(&[X, HID], &xs, &[vec![(X, su(h()))]]);
}

#[test]
fn prune_with_no_pattern_variable_drops_every_exclusion_that_binds_a_variable() {
    pruned_away(&[], &[vec![(x(), a())], vec![(x(), y())], vec![(x(), su(x()))]]);
}

#[test]
fn prune_with_no_pattern_variable_keeps_the_exclusions_that_always_hold() {
    let xs: Excls = vec![vec![(x(), a())], vec![(z(), z())], vec![(z(), a())], vec![(x(), x())], vec![]];
    pruned_is(&[], &xs, &[vec![], vec![], vec![]]);
}

#[test]
fn prune_with_no_pattern_variable_drops_every_entry() {
    entries_are(&[], &[(X, vec![NAT]), (Y, vec![])], &[]);
}

#[test]
fn prune_drops_the_entries_of_hidden_variables_and_keeps_the_order_of_the_others() {
    entries_are(
        &[X, W],
        &[(X, vec![NAT]), (Y, vec![NAT]), (W, vec![BOX]), (3, vec![PAIR])],
        &[(X, vec![NAT]), (W, vec![BOX])],
    );
}

#[test]
fn prune_keeps_the_entries_in_their_order_and_not_in_that_of_the_pattern_variables() {
    entries_are(&[W, X], &[(X, vec![NAT]), (W, vec![BOX])], &[(X, vec![NAT]), (W, vec![BOX])]);
    entries_are(&[X, W], &[(W, vec![BOX]), (X, vec![NAT])], &[(W, vec![BOX]), (X, vec![NAT])]);
}

#[test]
fn prune_keeps_an_entry_without_sorts_of_a_pattern_variable() {
    entries_are(&KS, &[(X, vec![]), (HID, vec![])], &[(X, vec![])]);
}

#[test]
fn prune_keeps_an_entry_with_several_sorts_whole() {
    entries_are(&KS, &[(HID, vec![NAT, SUC]), (Y, vec![NAT, SUC, ANY])], &[(Y, vec![NAT, SUC, ANY])]);
}

#[test]
fn prune_makes_no_entry_for_a_pattern_variable_that_has_none() {
    entries_are(&KS, &[(Y, vec![NAT])], &[(Y, vec![NAT])]);
    entries_are(&KS, &[], &[]);
}

#[test]
fn prune_drops_every_entry_when_all_are_of_hidden_variables() {
    entries_are(&[X], &[(Y, vec![NAT]), (W, vec![]), (HID, vec![BOX])], &[]);
}

#[test]
fn prune_judges_an_exclusion_by_the_pattern_variables_and_not_by_the_entries() {
    // `h` has an entry and is hidden; `w` has no entry and is of the pattern.
    let xs: Excls = vec![vec![(x(), su(h()))], vec![(x(), su(w()))]];
    let es: Entries = vec![(X, vec![NAT]), (HID, vec![NAT])];
    let (kept, got, got_es) = run_prune(&KS, &xs, &es, false);
    assert_eq!(kept, [1]);
    assert_eq!(got, [vec![(X, su(w()))]]);
    assert_eq!(got_es.len(), 1);
}

fn mixed() -> (Excls, Entries) {
    let xs: Excls = vec![
        vec![(x(), a())],
        vec![(h(), h()), (y(), su(w()))],
        vec![(x(), su(h()))],
        vec![(pr(x(), x()), pr(su(y()), su(a())))],
        vec![(k(), z())],
        vec![(x(), su(x()))],
        vec![(w(), y())],
        vec![(k(), k())],
    ];
    let es: Entries = vec![(X, vec![NAT]), (Y, vec![]), (HID, vec![NAT]), (W, vec![BOX]), (8, vec![])];
    (xs, es)
}

#[test]
fn prune_of_a_store_with_everything_keeps_what_is_over_the_pattern() {
    let (xs, es) = mixed();
    let (kept, got, got_es) = run_prune(&KS, &xs, &es, false);
    assert_eq!(kept, [0, 1, 3, 6, 7]);
    assert_eq!(got[0], [(X, a())]);
    assert_eq!(got[1], [(Y, su(w()))]);
    assert_eq!(got[2], [(X, su(a())), (Y, a())]);
    assert!(got[3] == [(W, y())] || got[3] == [(Y, w())], "{:?}", got[3]);
    assert!(got[4].is_empty());
    assert_eq!(got_es.iter().map(|e| e.0).collect::<Vec<_>>(), [X, Y, W]);
}

#[test]
fn prune_does_not_read_what_the_tables_held_before() {
    let (xs, es) = mixed();
    let clean = run_prune(&KS, &xs, &es, false);
    let soiled = run_prune(&KS, &xs, &es, true);
    assert_eq!(soiled, clean);
}

#[test]
fn prune_with_no_pattern_variable_does_not_read_what_the_tables_held_before() {
    let (xs, es) = mixed();
    let clean = run_prune(&[], &xs, &es, false);
    let soiled = run_prune(&[], &xs, &es, true);
    assert_eq!(soiled, clean);
}

#[test]
fn prune_twice_on_the_same_nodes_gives_the_same_nodes() {
    let (xs, es) = mixed();
    let mut f = fx();
    let ki = put_vars(&mut f, &KS);
    let xi = put_excls(&mut f.s, &xs);
    let ei = f.entries(&es);
    let (x1, e1) = prune(&mut f.s, ki, xi, ei);
    let (x2, e2) = prune(&mut f.s, ki, xi, ei);
    f.empty_stack();
    assert!(f.s.same(x1, x2) && f.s.same(e1, e2));
}

#[test]
fn prune_of_what_it_returned_returns_exclusions_that_say_the_same_and_the_same_entries() {
    let (xs, es) = mixed();
    let (_, got, got_es) = run_prune(&KS, &xs, &es, false);
    let again_xs: Excls = got.iter().map(|g| as_eqs(g)).collect();
    let (kept, again, again_es) = run_prune(&KS, &again_xs, &got_es, false);
    assert_eq!(kept, (0..got.len()).collect::<Vec<_>>());
    assert_eq!(again_es, got_es);
    for (g, a) in got.iter().zip(&again) {
        fits(&as_eqs(g), a);
    }
}

#[test]
fn prune_leaves_the_stack_empty_whatever_is_dropped() {
    let (xs, es) = mixed();
    let mut f = fx();
    for ks in [vec![], vec![X], vec![X, Y, W], vec![X, Y, W, HID, 8]] {
        let ki = put_vars(&mut f, &ks);
        let xi = put_excls(&mut f.s, &xs);
        let ei = f.entries(&es);
        prune(&mut f.s, ki, xi, ei);
        f.empty_stack();
    }
}

#[test]
fn prune_of_every_two_tiny_equations_keeps_what_the_reference_keeps() {
    // One variable of the pattern and one hidden variable: `run_prune`
    // compares what is kept with the reference.
    let eqs = all_pairs(&tiny_terms());
    let mut xs: Excls = eqs.iter().map(|e| vec![e.clone()]).collect();
    for (i, e1) in eqs.iter().enumerate() {
        for e2 in eqs.iter().skip(i % 5).step_by(5) {
            xs.push(vec![e1.clone(), e2.clone()]);
        }
    }
    let (kept, _, _) = run_prune(&[X], &xs, &[(X, vec![NAT]), (HID, vec![NAT])], false);
    assert!(!kept.is_empty() && kept.len() < xs.len());
}
