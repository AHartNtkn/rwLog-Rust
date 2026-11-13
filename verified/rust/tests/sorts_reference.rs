//! The reference normal store of `common/sorts.rs` against the meaning of a
//! problem: worked cases, enumeration of ground solutions, and the same
//! solutions written in other ways.

mod common;

use common::sorts::*;
use std::collections::{BTreeMap, BTreeSet};

// Symbols.
const Z: u32 = 0;
const K: u32 = 1;
const Q: u32 = 2; // named by no sort
const S: u32 = 3;
const PAIR: u32 = 4;

// Sorts.
const NAT: Name = 10;
const POS: Name = 11;
const ANY: Name = 12;
const ZK: Name = 13;
const KK: Name = 14;
const NOK: Name = 15;
const ONE: Name = 16;
const NIL: Name = 17;

fn z() -> P {
    pf(Z, vec![])
}
fn k() -> P {
    pf(K, vec![])
}
fn q() -> P {
    pf(Q, vec![])
}
fn s(a: P) -> P {
    pf(S, vec![a])
}
fn pair(a: P, b: P) -> P {
    pf(PAIR, vec![a, b])
}

/// ```text
/// sort nat = z | (s nat)
/// sort pos = (s _)
/// sort any = other
/// sort zk  = z | k | (pair zk zk)
/// sort kk  = k | (pair zk zk)
/// sort nok = other of nok \ k
/// sort one = z
/// sort nil = none
/// ```
fn sorts() -> Sorts {
    let def = |cases: Vec<(u32, Vec<Option<Name>>)>, rest| Def { cases, rest };
    Sorts::new(vec![
        (NAT, def(vec![(Z, vec![]), (S, vec![Some(NAT)])], None)),
        (POS, def(vec![(S, vec![None])], None)),
        (ANY, def(vec![], Some((vec![], None)))),
        (ZK, def(vec![(Z, vec![]), (K, vec![]), (PAIR, vec![Some(ZK), Some(ZK)])], None)),
        (KK, def(vec![(K, vec![]), (PAIR, vec![Some(ZK), Some(ZK)])], None)),
        (NOK, def(vec![], Some((vec![(K, 0)], Some(NOK))))),
        (ONE, def(vec![(Z, vec![])], None)),
        (NIL, def(vec![], None)),
    ])
}

fn conj(ns: &[Name]) -> Conj {
    ns.iter().copied().collect()
}

fn prob(t: P) -> Prob {
    Prob { t, e: vec![], a: vec![], x: vec![] }
}

// ---- the sorts themselves ----

#[test]
fn size_of_sorts() {
    let ss = sorts();
    assert_eq!(ss.size(&conj(&[])), Size::Infinite);
    assert_eq!(ss.size(&conj(&[NAT])), Size::Infinite);
    assert_eq!(ss.size(&conj(&[NIL])), Size::Empty);
    assert_eq!(ss.size(&conj(&[ONE])), Size::One(z()));
    assert_eq!(ss.size(&conj(&[NAT, ZK])), Size::One(z()));
    assert_eq!(ss.size(&conj(&[NAT, KK])), Size::Empty);
    assert_eq!(ss.size(&conj(&[POS, ZK])), Size::Empty);
    assert_eq!(ss.size(&conj(&[NOK, ZK])), Size::Infinite);
    assert_eq!(ss.size(&conj(&[99])), Size::Empty);
}

#[test]
fn inclusion_of_sorts() {
    let ss = sorts();
    assert!(ss.included(&conj(&[NAT]), ANY));
    assert!(ss.included(&conj(&[NAT]), NOK));
    assert!(!ss.included(&conj(&[NAT]), POS));
    assert!(ss.included(&conj(&[NAT, POS]), POS));
    assert!(ss.included(&conj(&[KK]), ZK));
    assert!(!ss.included(&conj(&[ZK]), KK));
    assert!(!ss.included(&conj(&[ANY]), NOK));
    assert!(ss.included(&conj(&[NIL]), NAT));
    assert!(!ss.included(&conj(&[]), NAT));
    assert!(ss.included(&conj(&[]), ANY));
}

#[test]
fn inclusion_but_ground_terms() {
    let ss = sorts();
    assert!(ss.included_but(&conj(&[ZK]), KK, &[z()]));
    assert!(!ss.included_but(&conj(&[ZK]), KK, &[k()]));
    assert!(ss.included_but(&conj(&[NAT]), POS, &[z()]));
    assert!(!ss.included_but(&conj(&[NAT]), POS, &[s(z())]));
    assert!(!ss.included_but(&conj(&[ANY]), NOK, &[k()]));
    assert!(!ss.included_but(&conj(&[ZK]), NOK, &[k()]));
}

// ---- worked cases ----

#[test]
fn no_constraint_numbers_the_variables() {
    let r = normal(&sorts(), &prob(pair(pv(7), pair(pv(3), pv(7))))).unwrap();
    assert_eq!(r.t, pair(pv(0), pair(pv(1), pv(0))));
    assert_eq!(r.c, vec![conj(&[ANY]), conj(&[ANY])]);
    assert!(r.x.is_empty());
}

#[test]
fn sort_of_a_variable_gets_every_sort_that_holds() {
    let mut p = prob(pv(0));
    p.a.push((NAT, pv(0)));
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(r.t, pv(0));
    assert_eq!(r.c, vec![conj(&[NAT, ANY, NOK])]);
}

#[test]
fn sort_is_pushed_through_a_pattern() {
    let mut p = prob(pv(0));
    p.a.push((NAT, s(pv(0))));
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(r.c, vec![conj(&[NAT, ANY, NOK])]);
}

#[test]
fn sort_that_rejects_the_pattern_is_dead() {
    let mut p = prob(pv(0));
    p.a.push((NAT, pair(pv(0), pv(0))));
    assert_eq!(normal(&sorts(), &p), None);
}

#[test]
fn sorts_with_no_common_term_are_dead() {
    let mut p = prob(pv(0));
    p.a.push((NAT, pv(0)));
    p.a.push((KK, pv(0)));
    assert_eq!(normal(&sorts(), &p), None);
}

#[test]
fn sort_of_one_term_binds_the_variable() {
    let mut p = prob(pair(pv(0), pv(1)));
    p.a.push((NAT, pv(0)));
    p.a.push((ZK, pv(0)));
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(r.t, pair(z(), pv(0)));
    assert_eq!(r.c, vec![conj(&[ANY])]);
}

#[test]
fn sort_with_one_root_extends_the_pattern() {
    let mut p = prob(pv(0));
    p.a.push((POS, pv(0)));
    p.a.push((NAT, pv(0)));
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(r.t, s(pv(0)));
    assert_eq!(r.c, vec![conj(&[NAT, ANY, NOK])]);
}

#[test]
fn excluded_value_leaves_one_root() {
    // $x : nat, $x != z  is  (s $y), $y : nat
    let mut p = prob(pv(0));
    p.a.push((NAT, pv(0)));
    p.x.push(vec![(pv(0), z())]);
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(r.t, s(pv(0)));
    assert_eq!(r.c, vec![conj(&[NAT, ANY, NOK])]);
    assert!(r.x.is_empty());
}

#[test]
fn excluded_value_moves_the_variable_to_a_smaller_sort() {
    // $x : zk, $x != z  is  $x : kk
    let mut p = prob(pv(0));
    p.a.push((ZK, pv(0)));
    p.x.push(vec![(pv(0), z())]);
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(r.t, pv(0));
    assert_eq!(r.c, vec![conj(&[ZK, KK, ANY])]);
    assert!(r.x.is_empty());
}

#[test]
fn excluded_value_outside_the_sort_is_dropped() {
    let mut p = prob(pv(0));
    p.a.push((NAT, pv(0)));
    p.x.push(vec![(pv(0), k())]);
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(r.t, pv(0));
    assert!(r.x.is_empty());
}

#[test]
fn excluded_value_inside_the_sort_is_kept() {
    let mut p = prob(pv(0));
    p.a.push((NAT, pv(0)));
    p.x.push(vec![(s(z()), pv(0))]);
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(r.t, pv(0));
    assert_eq!(r.x, vec![vec![(0, s(z()))]]);
}

#[test]
fn exclusion_of_a_term_from_itself_is_dead() {
    let mut p = prob(pv(0));
    p.x.push(vec![(pair(pv(0), z()), pair(pv(0), z()))]);
    assert_eq!(normal(&sorts(), &p), None);
}

#[test]
fn exclusion_made_true_by_an_equation_is_dead() {
    let mut p = prob(pair(pv(0), pv(1)));
    p.e.push((pv(0), pv(1)));
    p.x.push(vec![(pv(0), pv(1))]);
    assert_eq!(normal(&sorts(), &p), None);
}

#[test]
fn exclusion_of_the_only_value_is_dead() {
    let mut p = prob(pv(0));
    p.a.push((ONE, pv(0)));
    p.x.push(vec![(pv(0), z())]);
    assert_eq!(normal(&sorts(), &p), None);
}

#[test]
fn exclusion_between_variables_binds_the_later() {
    let mut p = prob(pair(pv(5), pv(2)));
    p.x.push(vec![(pv(5), pv(2))]);
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(r.t, pair(pv(0), pv(1)));
    assert_eq!(r.x, vec![vec![(1, pv(0))]]);
}

#[test]
fn exclusion_is_written_as_its_solution() {
    // (pair $x z) != (pair k $y)  is  not both $x = k and $y = z
    let mut p = prob(pair(pv(0), pv(1)));
    p.x.push(vec![(pair(pv(0), z()), pair(k(), pv(1)))]);
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(r.x, vec![vec![(0, k()), (1, z())]]);
}

#[test]
fn exclusion_that_cannot_hold_in_the_sorts_is_dropped() {
    // $x : nat, $y : kk: they are never equal.
    let mut p = prob(pair(pv(0), pv(1)));
    p.a.push((NAT, pv(0)));
    p.a.push((KK, pv(1)));
    p.x.push(vec![(pv(0), pv(1))]);
    let r = normal(&sorts(), &p).unwrap();
    assert!(r.x.is_empty());
}

#[test]
fn exclusion_binds_a_variable_its_equations_leave_one_value() {
    // $x : nat, $y : zk, $x != $y: equal only when both are z.
    let mut p = prob(pair(pv(0), pv(1)));
    p.a.push((NAT, pv(0)));
    p.a.push((ZK, pv(1)));
    p.x.push(vec![(pv(0), pv(1))]);
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(r.x, vec![vec![(0, z()), (1, z())]]);
}

#[test]
fn exclusion_implied_by_another_is_dropped() {
    // not $x = z, and not both $x = z and $y = z: the second says no more.
    let mut p = prob(pair(pv(0), pv(1)));
    p.x.push(vec![(pv(0), z()), (pv(1), z())]);
    p.x.push(vec![(pv(0), z())]);
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(r.x, vec![vec![(0, z())]]);
}

#[test]
fn exclusions_are_listed_in_order_and_once() {
    let mut p = prob(pair(pv(0), pv(1)));
    p.x.push(vec![(pv(1), k())]);
    p.x.push(vec![(pv(0), s(z()))]);
    p.x.push(vec![(k(), pv(1))]);
    p.x.push(vec![(pv(0), z())]);
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(
        r.x,
        vec![vec![(0, z())], vec![(0, s(z()))], vec![(1, k())]]
    );
}

#[test]
fn hidden_variable_and_its_exclusions_are_dropped() {
    let mut p = prob(pv(0));
    p.a.push((NAT, pv(1)));
    p.x.push(vec![(pv(0), pv(1))]);
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(r.t, pv(0));
    assert_eq!(r.c, vec![conj(&[ANY])]);
    assert!(r.x.is_empty());
}

#[test]
fn hidden_variable_with_no_value_is_dead() {
    let mut p = prob(pv(0));
    p.a.push((NAT, pv(1)));
    p.a.push((KK, pv(1)));
    assert_eq!(normal(&sorts(), &p), None);
}

#[test]
fn equation_is_solved_before_the_sorts() {
    let mut p = prob(pair(pv(0), pv(1)));
    p.e.push((pv(0), s(pv(1))));
    p.a.push((NAT, pv(0)));
    let r = normal(&sorts(), &p).unwrap();
    assert_eq!(r.t, pair(s(pv(0)), pv(0)));
    assert_eq!(r.c, vec![conj(&[NAT, ANY, NOK])]);
}

#[test]
fn equation_with_no_solution_is_dead() {
    let mut p = prob(pv(0));
    p.e.push((pv(0), s(pv(0))));
    assert_eq!(normal(&sorts(), &p), None);
    let mut p = prob(pv(0));
    p.e.push((z(), k()));
    assert_eq!(normal(&sorts(), &p), None);
}

// ---- against enumeration ----

#[test]
fn solution_of_equations_is_the_most_general() {
    let u = universe(3);
    let mut rng = Rng(5);
    let (mut some, mut none) = (0, 0);
    for round in 0..600 {
        let eqs: Vec<(P, P)> = (0..1 + rng.next(2))
            .map(|_| (random_term(&mut rng, 2, 2), random_term(&mut rng, 2, 2)))
            .collect();
        // The assignments of the two variables that solve the equations.
        let mut want = BTreeSet::new();
        for a in &u {
            for b in &u {
                let sigma = BTreeMap::from([(0, a.clone()), (1, b.clone())]);
                if eqs.iter().all(|(l, r)| l.subst(&sigma) == r.subst(&sigma)) {
                    want.insert((a.clone(), b.clone()));
                }
            }
        }
        // The instances of the solution.
        let mut got = BTreeSet::new();
        if let Some(theta) = mgu(&eqs) {
            some += 1;
            for (y, p) in &theta {
                let mut vs = Vec::new();
                p.vars(&mut vs);
                assert!(vs.iter().all(|w| !theta.contains_key(w)), "round {}: {:?}", round, theta);
                assert!(!matches!(p, P::V(w) if w > y), "round {}: {:?}", round, theta);
            }
            for a in &u {
                for b in &u {
                    let sigma = BTreeMap::from([(0, a.clone()), (1, b.clone())]);
                    let pair = (pv(0).subst(&theta).subst(&sigma), pv(1).subst(&theta).subst(&sigma));
                    if u.contains(&pair.0) && u.contains(&pair.1) {
                        got.insert(pair);
                    }
                }
            }
        } else {
            none += 1;
        }
        assert_eq!(got, want, "round {}: {:?}", round, eqs);
    }
    assert!(some > 100 && none > 100, "{} with a solution, {} without", some, none);
}

struct Rng(u64);

impl Rng {
    fn next(&mut self, n: usize) -> usize {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % n
    }
}

fn size(t: &P) -> usize {
    match t {
        P::V(_) => 1,
        P::F(_, args) => 1 + args.iter().map(size).sum::<usize>(),
    }
}

/// The ground terms of at most `n` symbols.
fn universe(n: usize) -> Vec<P> {
    let mut by_size: Vec<Vec<P>> = vec![vec![], vec![z(), k(), q()]];
    for m in 2..=n {
        let mut now = Vec::new();
        for a in &by_size[m - 1] {
            now.push(s(a.clone()));
        }
        for i in 1..m - 1 {
            for a in &by_size[i] {
                for b in &by_size[m - 1 - i] {
                    now.push(pair(a.clone(), b.clone()));
                }
            }
        }
        by_size.push(now);
    }
    by_size.concat()
}

fn holds(ss: &Sorts, p: &Prob, sigma: &BTreeMap<usize, P>) -> bool {
    p.e.iter().all(|(a, b)| a.subst(sigma) == b.subst(sigma))
        && p.a.iter().all(|(n, t)| ss.member(*n, &t.subst(sigma)))
        && p.x.iter().all(|e| e.iter().any(|(a, b)| a.subst(sigma) != b.subst(sigma)))
}

fn vars_of(p: &Prob) -> (Vec<usize>, Vec<usize>) {
    let mut shown = Vec::new();
    p.t.vars(&mut shown);
    let mut all = shown.clone();
    for (a, b) in p.e.iter().chain(p.x.iter().flatten()) {
        a.vars(&mut all);
        b.vars(&mut all);
    }
    for (_, t) in &p.a {
        t.vars(&mut all);
    }
    let hidden = all[shown.len()..].to_vec();
    (shown, hidden)
}

/// Every solution of the problem with the variables of the pattern in
/// `small` and the others in `large`.
fn solutions(ss: &Sorts, p: &Prob, small: &[P], large: &[P]) -> Vec<BTreeMap<usize, P>> {
    let (shown, hidden) = vars_of(p);
    // A value of one variable that breaks a sort naming no other variable is
    // in no solution, so it is left out before the values are combined.
    let alone = |y: usize, t: &P| {
        let mut vs = Vec::new();
        t.vars(&mut vs);
        vs.iter().all(|w| *w == y)
    };
    let fits = |y: usize, v: &P| {
        let sigma: BTreeMap<usize, P> = [(y, v.clone())].into_iter().collect();
        p.a.iter().filter(|(_, t)| alone(y, t)).all(|(n, t)| ss.member(*n, &t.subst(&sigma)))
    };
    let values: Vec<(usize, Vec<P>)> = shown
        .iter()
        .map(|y| (*y, small))
        .chain(hidden.iter().map(|y| (*y, large)))
        .map(|(y, u)| (y, u.iter().filter(|v| fits(y, v)).cloned().collect()))
        .collect();
    if values.iter().any(|(_, u)| u.is_empty()) {
        return Vec::new();
    }
    let vars: Vec<(usize, &[P])> = values.iter().map(|(y, u)| (*y, u.as_slice())).collect();
    let mut out = Vec::new();
    let mut at = vec![0usize; vars.len()];
    loop {
        let sigma: BTreeMap<usize, P> =
            vars.iter().zip(&at).map(|((y, u), i)| (*y, u[*i].clone())).collect();
        if holds(ss, p, &sigma) {
            out.push(sigma);
        }
        let mut i = 0;
        loop {
            if i == at.len() {
                return out;
            }
            at[i] += 1;
            if at[i] < vars[i].1.len() {
                break;
            }
            at[i] = 0;
            i += 1;
        }
    }
}

/// The instances of the pattern of at most `n` symbols.
fn instances(ss: &Sorts, p: &Prob, n: usize) -> BTreeSet<P> {
    // The equations are solved first, so that a variable not in the pattern
    // need not take a value larger than the instance.
    let Some(theta) = mgu(&p.e) else { return BTreeSet::new() };
    let on = |e: &Vec<(P, P)>| e.iter().map(|(a, b)| (a.subst(&theta), b.subst(&theta))).collect();
    let p = &Prob {
        t: p.t.subst(&theta),
        e: Vec::new(),
        a: p.a.iter().map(|(m, t)| (*m, t.subst(&theta))).collect(),
        x: p.x.iter().map(on).collect(),
    };
    let small = universe(n);
    let large = universe(n + 1);
    solutions(ss, p, &small, &large)
        .iter()
        .map(|sigma| p.t.subst(sigma))
        .filter(|t| size(t) <= n)
        .collect()
}

fn random_term(rng: &mut Rng, nvars: usize, depth: usize) -> P {
    let pick = rng.next(if depth == 0 { 4 } else { 7 });
    match pick {
        0..=1 => pv(rng.next(nvars)),
        2 => z(),
        3 => [k(), q()][rng.next(2)].clone(),
        4..=5 => s(random_term(rng, nvars, depth - 1)),
        _ => pair(random_term(rng, nvars, depth - 1), random_term(rng, nvars, depth - 1)),
    }
}

fn random_prob(rng: &mut Rng) -> Prob {
    let nvars = 1 + rng.next(3);
    let names = [NAT, POS, ANY, ZK, KK, NOK, ONE];
    let t = match rng.next(3) {
        0 => pv(0),
        1 => pair(pv(0), pv(rng.next(nvars))),
        _ => random_term(rng, nvars, 2),
    };
    let mut p = prob(t);
    if rng.next(4) == 0 {
        p.e.push((pv(rng.next(nvars)), random_term(rng, nvars, 1)));
    }
    for _ in 0..rng.next(3) {
        let of = if rng.next(2) == 0 { pv(rng.next(nvars)) } else { random_term(rng, nvars, 1) };
        p.a.push((names[rng.next(names.len())], of));
    }
    for _ in 0..rng.next(4) {
        if rng.next(4) == 0 {
            let a = pair(pv(rng.next(nvars)), pv(rng.next(nvars)));
            let b = pair(random_term(rng, nvars, 1), random_term(rng, nvars, 1));
            p.x.push(vec![(a, b)]);
            continue;
        }
        let a = if rng.next(3) == 0 { random_term(rng, nvars, 1) } else { pv(rng.next(nvars)) };
        let mut e = vec![(a, random_term(rng, nvars, 1))];
        if rng.next(3) == 0 {
            e.push((pv(rng.next(nvars)), random_term(rng, nvars, 1)));
        }
        p.x.push(e);
    }
    p
}

#[test]
fn normal_store_has_the_instances_of_the_problem() {
    let ss = sorts();
    let mut rng = Rng(1);
    let (mut dead, mut alive) = (0, 0);
    for round in 0..250 {
        let p = random_prob(&mut rng);
        let want = instances(&ss, &p, 3);
        match normal(&ss, &p) {
            None => {
                dead += 1;
                assert!(want.is_empty(), "round {}: dead, but {:?} has {:?}", round, p, want);
            }
            Some(r) => {
                alive += 1;
                let got = instances(&ss, &r.prob(), 3);
                assert_eq!(got, want, "round {}: {:?} became {:?}", round, p, r);
            }
        }
    }
    assert!(dead > 20 && alive > 100, "{} dead, {} alive", dead, alive);
}

/// The conditions of `Raw.Normal`, the ones on solutions by enumeration.
fn check_normal(ss: &Sorts, r: &Raw, what: &str) {
    let n = r.c.len();
    let mut vars = Vec::new();
    r.t.vars(&mut vars);
    assert_eq!(vars, (0..n).collect::<Vec<_>>(), "{}: variables of {:?}", what, r);
    // The fewer the variables, the larger the terms tried.
    let u = universe(if n <= 1 { 5 } else { 3 });
    let sols = solutions(ss, &r.prob(), &u, &u);
    for y in 0..n {
        let roots: BTreeSet<(u32, usize)> = sols
            .iter()
            .map(|sigma| match &sigma[&y] {
                P::F(f, args) => (*f, args.len()),
                P::V(_) => unreachable!(),
            })
            .collect();
        assert!(roots.len() >= 2, "{}: ${} has the roots {:?} in {:?}", what, y, roots, r);
        for name in ss.names() {
            let all = sols.iter().all(|sigma| ss.member(name, &sigma[&y]));
            assert_eq!(
                r.c[y].contains(&name),
                all,
                "{}: sort {} of ${} in {:?}",
                what,
                name,
                y,
                r
            );
        }
    }
    for b in &r.x {
        assert!(!b.is_empty(), "{}: empty exclusion in {:?}", what, r);
        for (i, (y, p)) in b.iter().enumerate() {
            assert!(*y < n);
            assert!(i == 0 || b[i - 1].0 < *y, "{}: order of {:?}", what, b);
            let mut vs = Vec::new();
            p.vars(&mut vs);
            assert!(vs.iter().all(|w| *w < n && b.iter().all(|(y2, _)| y2 != w)));
            if let P::V(w) = p {
                assert!(w < y, "{}: alias in {:?}", what, b);
            }
        }
    }
    for w in r.x.windows(2) {
        assert_eq!(binds_cmp(&w[0], &w[1]), std::cmp::Ordering::Less, "{}: {:?}", what, r.x);
    }
}

#[test]
fn normal_store_is_normal() {
    let ss = sorts();
    let mut rng = Rng(2);
    // How many stores keep an exclusion, keep one of two equations, have a
    // pattern the problem did not, and have a sort the problem did not name.
    let (mut excl, mut two, mut extended, mut sorted) = (0, 0, 0, 0);
    for round in 0..2000 {
        let p = random_prob(&mut rng);
        if let Some(r) = normal(&ss, &p) {
            check_normal(&ss, &r, &format!("round {} {:?}", round, p));
            excl += usize::from(!r.x.is_empty());
            two += usize::from(r.x.iter().any(|b| b.len() > 1));
            extended += usize::from(p.e.is_empty() && r.t != normal_names(&p.t));
            sorted += usize::from(r.c.iter().any(|c| c.contains(&KK) || c.contains(&POS)));
        }
    }
    assert!(
        excl > 150 && two > 8 && extended > 60 && sorted > 25,
        "{} with exclusions, {} with two equations, {} extended, {} in a smaller sort",
        excl,
        two,
        extended,
        sorted
    );
}

#[test]
fn normal_store_of_a_normal_store_is_itself() {
    let ss = sorts();
    let mut rng = Rng(3);
    for round in 0..3000 {
        let p = random_prob(&mut rng);
        if let Some(r) = normal(&ss, &p) {
            assert_eq!(normal(&ss, &r.prob()), Some(r.clone()), "round {}: {:?}", round, p);
        }
    }
}

/// The same problem written another way: other names for the variables,
/// the constraints in another order, equations turned round, and the sorts
/// and exclusions of its own normal store added.
fn rewritten(rng: &mut Rng, p: &Prob, r: Option<&Raw>) -> Prob {
    let (shown, hidden) = vars_of(p);
    let mut vars: Vec<usize> = shown.into_iter().chain(hidden).collect();
    let mut to = BTreeMap::new();
    let mut free: Vec<usize> = (0..vars.len() + 3).collect();
    while let Some(y) = vars.pop() {
        to.insert(y, pv(free.remove(rng.next(free.len()))));
    }
    let turn = |rng: &mut Rng, (a, b): &(P, P)| {
        let (a, b) = (a.subst(&to), b.subst(&to));
        if rng.next(2) == 0 {
            (a, b)
        } else {
            (b, a)
        }
    };
    let mut out = prob(p.t.subst(&to));
    for e in &p.e {
        let e = turn(rng, e);
        out.e.insert(rng.next(out.e.len() + 1), e);
    }
    for (n, t) in &p.a {
        out.a.insert(rng.next(out.a.len() + 1), (*n, t.subst(&to)));
    }
    for e in &p.x {
        let e: Vec<(P, P)> = e.iter().map(|q| turn(rng, q)).collect();
        out.x.insert(rng.next(out.x.len() + 1), e);
    }
    // What the normal store says holds of the problem's own pattern, when
    // the pattern was not extended.
    if let Some(r) = r {
        if r.t == normal_names(&p.t) {
            let mut order = Vec::new();
            p.t.vars(&mut order);
            let back: BTreeMap<usize, P> =
                order.iter().enumerate().map(|(i, y)| (i, to[y].clone())).collect();
            for (i, c) in r.c.iter().enumerate() {
                for n in c {
                    if rng.next(2) == 0 {
                        out.a.push((*n, back[&i].clone()));
                    }
                }
            }
            for b in &r.x {
                if rng.next(2) == 0 {
                    out.x.push(b.iter().map(|(y, t)| (back[y].clone(), t.subst(&back))).collect());
                }
            }
        }
    }
    out
}

fn normal_names(t: &P) -> P {
    let mut order = Vec::new();
    t.vars(&mut order);
    let number: BTreeMap<usize, P> = order.iter().enumerate().map(|(i, y)| (*y, pv(i))).collect();
    t.subst(&number)
}

#[test]
fn normal_store_does_not_depend_on_how_the_problem_is_written() {
    let ss = sorts();
    let mut rng = Rng(4);
    for round in 0..3000 {
        let p = random_prob(&mut rng);
        let r = normal(&ss, &p);
        for _ in 0..3 {
            let p2 = rewritten(&mut rng, &p, r.as_ref());
            assert_eq!(normal(&ss, &p2), r, "round {}: {:?} written as {:?}", round, p, p2);
        }
    }
}
