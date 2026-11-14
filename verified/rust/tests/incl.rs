//! Whether every member of a conjunction of sorts is in a sort, on the
//! store, against the specification (`Out` and `Incl` of
//! `lean/RwLog/Sorts/Incl.lean`, by the rounds `GrowsOut` of
//! `lean/RwLog/Sorts/ReachOut.lean`).

mod common;

use common::sorts::*;
use common::spent;
use rwlog_core::sorts::{included, live, out};
use rwlog_core::store::{Node, Store, TermId};
use std::collections::BTreeSet;

// Symbols.
const Z: u32 = 0;
const O: u32 = 1;
const F: u32 = 2;
const G: u32 = 3;
const H: u32 = 4;
const SU: u32 = 5;
const NI: u32 = 6;
const CO: u32 = 7;
const CA: u32 = 8;
const CB: u32 = 9;
const CC: u32 = 10;

// Names.
const A: Name = 100;
const B: Name = 101;
const C: Name = 102;
const D: Name = 103;
const X: Name = 104;
const Y: Name = 105;
const ZS: Name = 106;
const N: Name = 107;
const E: Name = 108;
const OD: Name = 109;
/// Never declared.
const Q: Name = 110;
const M: Name = 111;
const ANY: Name = 112;
const L1: Name = 113;
const L2: Name = 114;
const U: Name = 115;
const W: Name = 116;
const K: Name = 117;

type Case = (u32, Vec<Option<Name>>);

fn cases(cases: Vec<Case>) -> Def {
    Def { cases, rest: None }
}

fn rest(cases: Vec<Case>, ex: Vec<Key>, arg: Option<Name>) -> Def {
    Def { cases, rest: Some((ex, arg)) }
}

fn dead() -> Def {
    cases(vec![])
}

fn zero() -> Def {
    cases(vec![(Z, vec![])])
}

/// Every term.
fn any() -> Def {
    rest(vec![], vec![], None)
}

fn nat(n: Name) -> Def {
    cases(vec![(Z, vec![]), (SU, vec![Some(n)])])
}

struct Fx {
    s: Store,
    ss: Sorts,
    decls: TermId,
    order: Vec<Name>,
    names: TermId,
}

fn fx(defs: Vec<(Name, Def)>) -> Fx {
    let ss = Sorts::new(defs);
    let mut s = Store::new();
    let decls = put_sorts(&mut s, &ss);
    let order = ss.all_names();
    let names = put_names(&mut s, &order);
    Fx { s, ss, decls, order, names }
}

impl Fx {
    fn conj(&mut self, c: &[Name]) -> TermId {
        let set: Conj = c.iter().copied().collect();
        let list = canon(&self.order, &set);
        assert_eq!(list.len(), set.len(), "a conjunction of names of the declarations");
        put_names(&mut self.s, &list)
    }

    fn name(&mut self, n: Name) -> TermId {
        self.s.alloc(Node::Sym(n))
    }

    fn out(&mut self, c: &[Name], n: Name) -> bool {
        let c = self.conj(c);
        let n = self.name(n);
        out(&mut self.s, self.decls, self.names, c, n)
    }

    fn inc(&mut self, c: &[Name], n: Name) -> bool {
        let c = self.conj(c);
        let n = self.name(n);
        included(&mut self.s, self.decls, self.names, c, n)
    }

    fn live(&mut self, c: &[Name]) -> bool {
        let c = self.conj(c);
        live(&mut self.s, self.decls, self.names, c)
    }

    fn ticks(&mut self, c: &[Name], n: Name) -> (bool, u64) {
        let c = self.conj(c);
        let n = self.name(n);
        let (decls, names) = (self.decls, self.names);
        spent(&mut self.s, |s| included(s, decls, names, c, n))
    }
}

fn inc_of(defs: Vec<(Name, Def)>, c: &[Name], n: Name) -> bool {
    fx(defs).inc(c, n)
}

fn subsets(names: &[Name]) -> Vec<Vec<Name>> {
    (0..1usize << names.len())
        .map(|m| names.iter().enumerate().filter(|(i, _)| m >> i & 1 == 1).map(|(_, n)| *n).collect())
        .collect()
}

/// The pairs of a set of names with a name whose conjunction has a member
/// outside the sort: the least set closed under `GrowsOut` of the
/// specification, over every set of the names with every one of the names
/// and one name more that is not declared.
fn out_spec(ss: &Sorts, undeclared: Name) -> BTreeSet<(Conj, Name)> {
    let names = ss.all_names();
    let sets: Vec<Conj> = subsets(&names).into_iter().map(|c| c.into_iter().collect()).collect();
    let mut sorts = names.clone();
    sorts.push(undeclared);
    let def = |n: Name| ss.defs.iter().find(|(m, _)| *m == n).map(|(_, d)| d);
    let rest_ok = |c: &Conj| c.iter().all(|n| def(*n).is_some_and(|d| d.rest.is_some()));
    let case_keys = |c: &Conj| -> BTreeSet<Key> {
        c.iter().filter_map(|n| def(*n)).flat_map(|d| d.cases.iter().map(|(f, a)| (*f, a.len()))).collect()
    };
    // The conjunctions with a member.
    let mut have: BTreeSet<Conj> = BTreeSet::new();
    loop {
        let mut next = have.clone();
        for c in &sets {
            let by_key = case_keys(c).iter().any(|k| match ss.step_conj(c, *k) {
                Some(kids) => kids.iter().all(|k| have.contains(k)),
                None => false,
            });
            if rest_ok(c) || by_key {
                next.insert(c.clone());
            }
        }
        if next == have {
            break;
        }
        have = next;
    }
    let mut outs: BTreeSet<(Conj, Name)> = BTreeSet::new();
    loop {
        let mut next = outs.clone();
        for c in &sets {
            for n in &sorts {
                let own_rest = def(*n).and_then(|d| d.rest.as_ref());
                let no_rest = rest_ok(c) && own_rest.is_none();
                let rest_kids: Conj =
                    c.iter().filter_map(|k| def(*k)?.rest.as_ref()?.1).collect();
                let by_rest = rest_ok(c)
                    && match own_rest {
                        Some((_, Some(m))) => outs.contains(&(rest_kids, *m)),
                        _ => false,
                    };
                let mut keys = case_keys(c);
                if let Some(d) = def(*n) {
                    keys.extend(d.cases.iter().map(|(f, a)| (*f, a.len())));
                    if let Some((ex, _)) = &d.rest {
                        keys.extend(ex.iter().copied());
                    }
                }
                let by_key = keys.iter().any(|k| match ss.step_conj(c, *k) {
                    None => false,
                    Some(kids) => {
                        kids.iter().all(|k| have.contains(k))
                            && match ss.step(*n, *k) {
                                None => true,
                                Some(ms) => kids
                                    .iter()
                                    .zip(ms)
                                    .any(|(kid, m)| m.is_some_and(|m| outs.contains(&(kid.clone(), m)))),
                            }
                    }
                });
                if no_rest || by_rest || by_key {
                    next.insert((c.clone(), *n));
                }
            }
        }
        if next == outs {
            return outs;
        }
        outs = next;
    }
}

/// Every set of the names with every name and an undeclared one: the store
/// agrees with the specification.
fn check_all(defs: Vec<(Name, Def)>) {
    let mut f = fx(defs);
    let spec = out_spec(&f.ss, Q);
    let mut sorts = f.order.clone();
    if !sorts.contains(&Q) {
        sorts.push(Q);
    }
    for c in subsets(&f.order.clone()) {
        let set: Conj = c.iter().copied().collect();
        for n in &sorts {
            let want = spec.contains(&(set.clone(), *n));
            assert_eq!(f.out(&c, *n), want, "out of {:?} in {} under {:?}", c, n, f.ss.defs);
            assert_eq!(f.inc(&c, *n), !want, "inclusion of {:?} in {} under {:?}", c, n, f.ss.defs);
        }
    }
}

struct Rng(u64);

impl Rng {
    fn next(&mut self, n: usize) -> usize {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % n
    }
}

// The empty conjunction is every term.

#[test]
fn every_term_is_in_a_sort_that_is_a_rest_alone() {
    assert!(inc_of(vec![(ANY, any())], &[], ANY));
}

#[test]
fn every_term_is_not_in_a_sort_of_one_constant() {
    assert!(!inc_of(vec![(A, zero())], &[], A));
}

#[test]
fn every_term_is_not_in_a_dead_sort() {
    assert!(!inc_of(vec![(D, dead())], &[], D));
}

#[test]
fn every_term_is_not_in_an_undeclared_sort() {
    assert!(!inc_of(vec![(A, zero())], &[], Q));
    assert!(!inc_of(vec![], &[], Q));
}

#[test]
fn every_term_is_not_in_a_rest_that_excludes_a_root() {
    assert!(!inc_of(vec![(A, rest(vec![], vec![(Z, 0)], None))], &[], A));
    assert!(!inc_of(vec![(A, rest(vec![], vec![(F, 2)], None))], &[], A));
}

#[test]
fn every_term_is_in_a_rest_whose_excluded_root_has_a_case_of_every_term() {
    assert!(inc_of(vec![(A, rest(vec![(F, vec![None, None])], vec![(F, 2)], None))], &[], A));
}

#[test]
fn every_term_is_not_in_a_rest_with_a_case_that_asks_a_sort_of_an_argument() {
    let defs = vec![(A, rest(vec![(F, vec![Some(B)])], vec![], None)), (B, zero())];
    assert!(!inc_of(defs, &[], A));
}

#[test]
fn every_term_is_in_a_rest_with_a_case_that_asks_every_term_by_a_name() {
    let defs = vec![(A, rest(vec![(F, vec![Some(ANY)])], vec![], None)), (ANY, any())];
    assert!(inc_of(defs, &[], A));
}

#[test]
fn every_term_is_not_in_a_rest_that_asks_a_sort_of_the_arguments() {
    let defs = vec![(A, rest(vec![], vec![], Some(B))), (B, zero())];
    assert!(!inc_of(defs, &[], A));
}

#[test]
fn every_term_is_in_a_rest_that_asks_itself_of_the_arguments() {
    // Nothing is ever refused: no root, and no argument at any depth.
    assert!(inc_of(vec![(A, rest(vec![], vec![], Some(A)))], &[], A));
}

#[test]
fn every_term_is_in_a_rest_that_asks_every_term_by_a_name() {
    let defs = vec![(A, rest(vec![], vec![], Some(ANY))), (ANY, any())];
    assert!(inc_of(defs, &[], A));
}

// A conjunction with no member is in every sort.

#[test]
fn a_dead_sort_is_in_every_sort() {
    let defs = || vec![(D, dead()), (A, zero()), (ANY, any())];
    for n in [D, A, ANY, Q] {
        assert!(inc_of(defs(), &[D], n), "in {}", n);
    }
}

#[test]
fn an_undeclared_sort_is_in_every_sort() {
    let defs = || vec![(A, cases(vec![(F, vec![Some(Q)])])), (B, zero())];
    for n in [A, B, Q] {
        assert!(inc_of(defs(), &[Q], n), "in {}", n);
    }
}

#[test]
fn a_conjunction_of_disjoint_sorts_is_in_every_sort() {
    let defs = || vec![(E, nat_even()), (OD, nat_odd()), (D, dead()), (A, cases(vec![(O, vec![])]))];
    for n in [E, OD, D, A, Q] {
        assert!(inc_of(defs(), &[E, OD], n), "in {}", n);
    }
}

#[test]
fn recursion_without_a_base_is_in_every_sort() {
    let defs = || vec![(X, cases(vec![(SU, vec![Some(X)])])), (D, dead())];
    assert!(inc_of(defs(), &[X], D));
    assert!(inc_of(defs(), &[X], Q));
}

#[test]
fn a_conjunction_with_a_dead_sort_and_a_rest_is_in_every_sort() {
    let defs = || vec![(ANY, any()), (D, dead())];
    assert!(inc_of(defs(), &[ANY, D], D));
    assert!(inc_of(defs(), &[ANY, D], Q));
}

// A conjunction with a member is in no sort that has none.

#[test]
fn a_live_sort_is_not_in_a_dead_sort() {
    assert!(!inc_of(vec![(A, zero()), (D, dead())], &[A], D));
}

#[test]
fn a_live_sort_is_not_in_an_undeclared_sort() {
    assert!(!inc_of(vec![(A, zero())], &[A], Q));
    assert!(!inc_of(vec![(A, any())], &[A], Q));
}

#[test]
fn a_live_sort_is_not_in_recursion_without_a_base() {
    let defs = vec![(A, nat(A)), (X, cases(vec![(SU, vec![Some(X)])]))];
    assert!(!inc_of(defs, &[A], X));
}

// Constants and roots.

#[test]
fn a_sort_is_in_itself() {
    assert!(inc_of(vec![(A, zero())], &[A], A));
    assert!(inc_of(vec![(A, nat(A))], &[A], A));
    assert!(inc_of(vec![(A, rest(vec![(F, vec![Some(A)])], vec![(Z, 0)], Some(A)))], &[A], A));
}

#[test]
fn a_conjunction_is_in_each_of_its_sorts() {
    let defs = || vec![(E, nat_even()), (OD, nat_odd()), (N, nat(N))];
    assert!(inc_of(defs(), &[E, N], E));
    assert!(inc_of(defs(), &[E, N], N));
    assert!(inc_of(defs(), &[OD, N], OD));
}

#[test]
fn one_constant_is_in_two_constants_and_not_the_reverse() {
    let defs = || vec![(A, zero()), (B, cases(vec![(Z, vec![]), (O, vec![])]))];
    assert!(inc_of(defs(), &[A], B));
    assert!(!inc_of(defs(), &[B], A));
}

#[test]
fn the_same_symbol_at_another_arity_is_another_root() {
    let defs = || vec![(A, cases(vec![(F, vec![])])), (B, cases(vec![(F, vec![None])]))];
    assert!(!inc_of(defs(), &[A], B));
    assert!(!inc_of(defs(), &[B], A));
}

#[test]
fn a_constant_is_in_a_rest_unless_the_rest_excludes_it() {
    let defs = || {
        vec![
            (A, zero()),
            (B, rest(vec![], vec![], None)),
            (C, rest(vec![], vec![(Z, 0)], None)),
            (X, rest(vec![], vec![(Z, 1)], None)),
        ]
    };
    assert!(inc_of(defs(), &[A], B));
    assert!(!inc_of(defs(), &[A], C));
    assert!(inc_of(defs(), &[A], X));
}

#[test]
fn a_case_of_the_sort_overrides_its_exclusion_of_the_same_root() {
    let defs = vec![(A, zero()), (B, rest(vec![(Z, vec![])], vec![(Z, 0)], None))];
    assert!(inc_of(defs, &[A], B));
}

#[test]
fn a_rest_is_not_in_a_sort_without_a_rest() {
    let defs = vec![(A, any()), (B, cases(vec![(Z, vec![]), (F, vec![None]), (G, vec![None, None])]))];
    assert!(!inc_of(defs, &[A], B));
}

#[test]
fn a_rest_is_in_a_rest_that_excludes_no_more() {
    let defs = || {
        vec![
            (A, rest(vec![], vec![(Z, 0), (F, 1)], None)),
            (B, rest(vec![], vec![(Z, 0)], None)),
        ]
    };
    assert!(inc_of(defs(), &[A], B));
    assert!(!inc_of(defs(), &[B], A));
}

#[test]
fn a_rest_whose_only_missing_root_is_one_the_conjunction_refuses_too() {
    // `B` excludes `z`, and `A` has no `z` either although it names it.
    let defs = vec![
        (A, rest(vec![(Z, vec![Some(D)])], vec![], None)),
        (B, rest(vec![], vec![(Z, 1)], None)),
        (D, dead()),
    ];
    assert!(inc_of(defs, &[A], B));
}

#[test]
fn the_exclusions_of_the_sort_are_looked_at_although_the_conjunction_does_not_name_them() {
    let defs = vec![(A, any()), (B, rest(vec![], vec![(G, 3)], None))];
    assert!(!inc_of(defs, &[A], B));
}

#[test]
fn the_cases_of_the_sort_are_looked_at_although_the_conjunction_does_not_name_them() {
    let defs = || vec![(A, any()), (B, rest(vec![(G, vec![Some(C)])], vec![], None)), (C, zero())];
    assert!(!inc_of(defs(), &[A], B));
    assert!(inc_of(defs(), &[B], A));
}

// Arguments.

#[test]
fn inclusion_goes_through_an_argument() {
    let defs = || {
        vec![
            (A, cases(vec![(F, vec![Some(X)])])),
            (B, cases(vec![(F, vec![Some(Y)])])),
            (X, zero()),
            (Y, cases(vec![(Z, vec![]), (O, vec![])])),
        ]
    };
    assert!(inc_of(defs(), &[A], B));
    assert!(!inc_of(defs(), &[B], A));
}

#[test]
fn an_argument_of_every_term_is_only_in_every_term() {
    let defs = || {
        vec![
            (A, cases(vec![(F, vec![None])])),
            (B, cases(vec![(F, vec![Some(X)])])),
            (C, cases(vec![(F, vec![Some(ANY)])])),
            (X, zero()),
            (ANY, any()),
        ]
    };
    assert!(!inc_of(defs(), &[A], B));
    assert!(inc_of(defs(), &[B], A));
    assert!(inc_of(defs(), &[A], C));
    assert!(inc_of(defs(), &[C], A));
}

#[test]
fn one_argument_out_of_several_is_enough_to_be_out() {
    for bad in 0..3 {
        let mut kids = vec![Some(X); 3];
        kids[bad] = Some(Y);
        let defs = vec![
            (A, cases(vec![(F, kids)])),
            (B, cases(vec![(F, vec![Some(X); 3])])),
            (X, zero()),
            (Y, cases(vec![(Z, vec![]), (O, vec![])])),
        ];
        assert!(!inc_of(defs, &[A], B), "argument {}", bad);
    }
}

#[test]
fn a_root_with_a_dead_argument_is_no_member_and_cannot_be_out() {
    // `f(_, D)` has no instance, so the first argument being outside does
    // not matter.
    let defs = || {
        vec![
            (A, cases(vec![(Z, vec![]), (F, vec![Some(Y), Some(D)])])),
            (B, cases(vec![(Z, vec![]), (F, vec![Some(X), None])])),
            (C, cases(vec![(Z, vec![])])),
            (X, zero()),
            (Y, cases(vec![(Z, vec![]), (O, vec![])])),
            (D, dead()),
        ]
    };
    assert!(inc_of(defs(), &[A], B));
    assert!(inc_of(defs(), &[A], C));
}

#[test]
fn a_root_the_sort_refuses_is_not_out_when_an_argument_is_dead() {
    let defs = vec![(A, cases(vec![(Z, vec![]), (F, vec![Some(D)])])), (B, zero()), (D, dead())];
    assert!(inc_of(defs, &[A], B));
}

#[test]
fn a_root_whose_argument_conjunction_is_dead_is_no_member() {
    // `f` of an even and odd number does not exist.
    let defs = vec![
        (A, cases(vec![(Z, vec![]), (F, vec![Some(E)])])),
        (B, cases(vec![(Z, vec![]), (F, vec![Some(OD)])])),
        (C, zero()),
        (E, nat_even()),
        (OD, nat_odd()),
    ];
    assert!(inc_of(defs, &[A, B], C));
}

#[test]
fn the_sorts_of_the_conjunction_join_at_an_argument() {
    let defs = || {
        vec![
            (A, cases(vec![(F, vec![Some(E)])])),
            (B, cases(vec![(F, vec![Some(N)])])),
            (C, cases(vec![(F, vec![Some(OD)])])),
            (X, cases(vec![(F, vec![Some(M)])])),
            (E, nat_even()),
            (OD, nat_odd()),
            (N, nat(N)),
            (M, nat(M)),
        ]
    };
    assert!(inc_of(defs(), &[A, B], X));
    assert!(!inc_of(defs(), &[A, B], C));
    // `f` of an even number that is odd: nothing.
    assert!(inc_of(defs(), &[A, C], Q));
}

#[test]
fn reads_the_first_of_duplicate_cases_of_the_sort() {
    let defs = || {
        vec![
            (A, cases(vec![(F, vec![Some(Y)])])),
            (B, cases(vec![(F, vec![Some(X)]), (F, vec![Some(Y)])])),
            (C, cases(vec![(F, vec![Some(Y)]), (F, vec![Some(X)])])),
            (X, zero()),
            (Y, cases(vec![(Z, vec![]), (O, vec![])])),
        ]
    };
    assert!(!inc_of(defs(), &[A], B));
    assert!(inc_of(defs(), &[A], C));
}

#[test]
fn reads_the_first_declaration_of_a_name_declared_twice() {
    let defs = || vec![(A, zero()), (B, zero()), (B, dead()), (A, cases(vec![(O, vec![])]))];
    assert!(inc_of(defs(), &[A], B));
    assert!(inc_of(defs(), &[B], A));
}

// Rests.

#[test]
fn rests_compare_by_the_sort_they_ask_of_the_arguments() {
    let defs = || {
        vec![
            (A, rest(vec![], vec![], Some(X))),
            (B, rest(vec![], vec![], Some(Y))),
            (X, zero()),
            (Y, cases(vec![(Z, vec![]), (O, vec![])])),
        ]
    };
    assert!(inc_of(defs(), &[A], B));
    assert!(!inc_of(defs(), &[B], A));
}

#[test]
fn a_rest_of_every_term_is_not_in_a_rest_that_asks_a_sort() {
    let defs = || vec![(A, any()), (B, rest(vec![], vec![], Some(X))), (X, zero())];
    assert!(!inc_of(defs(), &[A], B));
    assert!(inc_of(defs(), &[B], A));
}

#[test]
fn rests_that_ask_dead_sorts_of_the_arguments_are_the_same_constants() {
    // Only the constants are left on both sides.
    let defs = || {
        vec![
            (A, rest(vec![], vec![], Some(D))),
            (B, rest(vec![], vec![], Some(Q))),
            (C, rest(vec![], vec![(Z, 0)], Some(D))),
            (D, dead()),
        ]
    };
    assert!(inc_of(defs(), &[A], B));
    assert!(inc_of(defs(), &[B], A));
    assert!(inc_of(defs(), &[C], A));
    assert!(!inc_of(defs(), &[A], C));
}

#[test]
fn two_rests_join_the_sorts_they_ask() {
    let defs = || {
        vec![
            (A, rest(vec![], vec![], Some(E))),
            (B, rest(vec![], vec![], Some(N))),
            (C, rest(vec![], vec![], Some(OD))),
            (X, rest(vec![], vec![], Some(M))),
            (E, nat_even()),
            (OD, nat_odd()),
            (N, nat(N)),
            (M, nat(M)),
        ]
    };
    assert!(inc_of(defs(), &[A, B], X));
    assert!(!inc_of(defs(), &[A, B], C));
    // Even and odd at once: only the constants, and `C` has them all.
    assert!(inc_of(defs(), &[A, C], B));
}

#[test]
fn a_root_one_sort_takes_by_a_case_and_another_by_its_rest() {
    let defs = || {
        vec![
            (A, cases(vec![(F, vec![Some(Y)])])),
            (B, rest(vec![], vec![], Some(X))),
            (C, cases(vec![(F, vec![Some(X)])])),
            (X, zero()),
            (Y, cases(vec![(Z, vec![]), (O, vec![])])),
        ]
    };
    // `f(z)` only.
    assert!(inc_of(defs(), &[A, B], C));
    assert!(!inc_of(defs(), &[A], C));
    // `B` has other roots.
    assert!(!inc_of(defs(), &[B], C));
}

#[test]
fn an_exclusion_of_one_sort_of_the_conjunction_removes_the_root() {
    let defs = || {
        vec![
            (A, any()),
            (B, rest(vec![], vec![(G, 3)], None)),
            (C, rest(vec![], vec![(G, 3)], None)),
            (X, rest(vec![], vec![(G, 2)], None)),
        ]
    };
    assert!(inc_of(defs(), &[A, B], C));
    assert!(!inc_of(defs(), &[A, X], C));
}

// Recursion.

fn nat_even() -> Def {
    cases(vec![(Z, vec![]), (SU, vec![Some(OD)])])
}

fn nat_odd() -> Def {
    cases(vec![(SU, vec![Some(E)])])
}

fn nats() -> Vec<(Name, Def)> {
    vec![(E, nat_even()), (OD, nat_odd()), (N, nat(N)), (M, nat(M)), (D, dead())]
}

#[test]
fn even_and_odd_are_naturals_and_naturals_are_neither() {
    assert!(inc_of(nats(), &[E], N));
    assert!(inc_of(nats(), &[OD], N));
    assert!(!inc_of(nats(), &[N], E));
    assert!(!inc_of(nats(), &[N], OD));
    assert!(!inc_of(nats(), &[E], OD));
    assert!(!inc_of(nats(), &[OD], E));
}

#[test]
fn two_declarations_of_the_naturals_are_in_each_other() {
    assert!(inc_of(nats(), &[N], M));
    assert!(inc_of(nats(), &[M], N));
}

#[test]
fn a_witness_far_down_is_found() {
    // Numbers up to `n` against numbers up to `n - 1`.
    let upto = |base: Name, n: usize| -> Vec<(Name, Def)> {
        let mut defs: Vec<(Name, Def)> = (0..n).map(|i| (base + i as Name, nat(base + i as Name + 1))).collect();
        defs.push((base + n as Name, zero()));
        defs
    };
    let mut defs = upto(1000, 60);
    defs.extend(upto(2000, 59));
    assert!(!inc_of(defs.clone(), &[1000], 2000));
    assert!(inc_of(defs, &[2000], 1000));
}

#[test]
fn lists_compare_by_their_elements() {
    let list = |me: Name, el: Name| cases(vec![(NI, vec![]), (CO, vec![Some(el), Some(me)])]);
    let defs = || {
        vec![(L1, list(L1, E)), (L2, list(L2, N)), (E, nat_even()), (OD, nat_odd()), (N, nat(N))]
    };
    assert!(inc_of(defs(), &[L1], L2));
    assert!(!inc_of(defs(), &[L2], L1));
}

#[test]
fn mutual_recursion_through_pairs_that_wait_for_each_other() {
    // `A = z | f(B)`, `B = z | f(A)` against `C = z | f(C)`: the pairs
    // reach each other and none is out.
    let defs = || {
        vec![
            (A, cases(vec![(Z, vec![]), (F, vec![Some(B)])])),
            (B, cases(vec![(Z, vec![]), (F, vec![Some(A)])])),
            (C, cases(vec![(Z, vec![]), (F, vec![Some(C)])])),
            (X, cases(vec![(Z, vec![]), (F, vec![Some(Y)])])),
            (Y, cases(vec![(F, vec![Some(X)])])),
        ]
    };
    assert!(inc_of(defs(), &[A], C));
    assert!(inc_of(defs(), &[C], A));
    // `X` has no `f(z)`.
    assert!(!inc_of(defs(), &[A], X));
    assert!(inc_of(defs(), &[X], A));
}

#[test]
fn a_pair_that_only_reaches_itself_is_not_out() {
    let defs = vec![(A, cases(vec![(F, vec![Some(A)]), (Z, vec![])])), (B, cases(vec![(F, vec![Some(B)]), (Z, vec![])]))];
    assert!(inc_of(defs, &[A], B));
}

#[test]
fn a_rest_that_asks_itself_against_another_that_asks_itself() {
    let defs = || {
        vec![
            (A, rest(vec![], vec![(Z, 0)], Some(A))),
            (B, rest(vec![], vec![], Some(B))),
        ]
    };
    assert!(inc_of(defs(), &[A], B));
    // `z` is in `B` and not in `A`.
    assert!(!inc_of(defs(), &[B], A));
}

#[test]
fn a_witness_under_a_rest_far_down() {
    // `B` refuses `z` only as an argument of an argument.
    let defs = || {
        vec![
            (A, any()),
            (B, rest(vec![], vec![], Some(C))),
            (C, rest(vec![], vec![], Some(X))),
            (X, rest(vec![], vec![(Z, 0)], None)),
        ]
    };
    assert!(!inc_of(defs(), &[A], B));
    assert!(inc_of(defs(), &[B], A));
    // `f(z)` is in `B` and not in `C`; `f(g(z))` is in `C` and not in `B`.
    assert!(!inc_of(defs(), &[B], C));
    assert!(!inc_of(defs(), &[C], B));
}

// State and contract.

#[test]
fn out_is_the_negation_of_included() {
    let mut f = fx(nats());
    for (c, n) in [(vec![E], N), (vec![N], E), (vec![E, OD], D), (vec![], N), (vec![D], Q), (vec![N], Q)] {
        assert_eq!(f.out(&c, n), !f.inc(&c, n), "{:?} in {}", c, n);
    }
}

#[test]
fn included_leaves_the_stack_empty() {
    let mut f = fx(nats());
    assert!(f.inc(&[E], N));
    assert!(f.s.pop().is_none());
    assert!(!f.inc(&[N], E));
    assert!(f.s.pop().is_none());
}

#[test]
fn included_gives_the_same_answer_when_called_again() {
    let mut f = fx(nats());
    for _ in 0..3 {
        assert!(f.inc(&[E], N));
        assert!(!f.inc(&[N], E));
        assert!(f.inc(&[N], M));
        assert!(f.inc(&[E, OD], D));
        assert!(!f.inc(&[N], D));
    }
}

#[test]
fn included_does_not_see_flags_of_an_earlier_call() {
    let mut f = fx(nats());
    // Liveness leaves its flags in both tables.
    assert!(f.live(&[N]));
    assert!(f.inc(&[N], M));
    assert!(!f.live(&[E, OD]));
    assert!(!f.inc(&[N], E));
    // A call that flags pairs out, then one whose pairs are not.
    assert!(!f.inc(&[N], D));
    assert!(f.inc(&[E], N));
    assert!(f.live(&[E, N]));
}

#[test]
fn liveness_gives_the_same_answer_after_inclusion() {
    let mut f = fx(nats());
    assert!(!f.inc(&[N], E));
    assert!(!f.live(&[E, OD]));
    assert!(f.live(&[OD, N]));
    assert!(!f.live(&[D]));
}

// More roots, rests and conjunctions, each also against the specification.

/// The answer of the store is `want`, and so is that of the specification.
fn out_is(defs: Vec<(Name, Def)>, c: &[Name], n: Name, want: bool) {
    let mut f = fx(defs);
    let set: Conj = c.iter().copied().collect();
    assert_eq!(out_spec(&f.ss, n).contains(&(set, n)), want, "specification: {:?} in {} under {:?}", c, n, f.ss.defs);
    assert_eq!(f.out(c, n), want, "{:?} in {} under {:?}", c, n, f.ss.defs);
    assert_eq!(f.inc(c, n), !want);
}

fn one(f: u32) -> Def {
    cases(vec![(f, vec![])])
}

fn two(f: u32, g: u32) -> Def {
    cases(vec![(f, vec![]), (g, vec![])])
}

/// `X = ca | cb`, `Y = cb | cc`, `W = cb`, `U = ca`, `ZS = z`, `D` dead.
fn with_sets(mut defs: Vec<(Name, Def)>) -> Vec<(Name, Def)> {
    defs.extend(vec![(X, two(CA, CB)), (Y, two(CB, CC)), (W, one(CB)), (U, one(CA)), (ZS, zero()), (D, dead())]);
    defs
}

#[test]
fn a_conjunction_with_an_undeclared_name_is_never_out() {
    let defs = || vec![(A, zero()), (B, cases(vec![(F, vec![Some(Q)])]))];
    for n in [A, B, Q] {
        out_is(defs(), &[A, Q], n, false);
    }
}

#[test]
fn a_conjunction_of_a_name_the_declarations_never_mention_is_never_out() {
    let mut f = fx(vec![(A, zero())]);
    let c = put_names(&mut f.s, &[Q]);
    let n = f.name(A);
    assert!(!out(&mut f.s, f.decls, f.names, c, n));
}

#[test]
fn an_argument_asked_in_an_undeclared_sort() {
    let defs = |x: Def| vec![(A, cases(vec![(F, vec![Some(X)])])), (N, cases(vec![(F, vec![Some(Q)])])), (X, x)];
    out_is(defs(zero()), &[A], N, true);
    out_is(defs(dead()), &[A], N, false);
}

#[test]
fn every_term_against_a_case_with_a_dead_argument_under_a_rest() {
    out_is(vec![(N, rest(vec![(F, vec![Some(D)])], vec![], None)), (D, dead())], &[], N, true);
}

#[test]
fn every_term_against_a_case_that_narrows_the_excluded_root() {
    out_is(vec![(N, rest(vec![(H, vec![Some(ZS)])], vec![(H, 1)], None)), (ZS, zero())], &[], N, true);
}

#[test]
fn every_term_through_the_sort_a_rest_asks() {
    let defs = |m: Def| vec![(N, rest(vec![], vec![], Some(M))), (M, m)];
    out_is(defs(rest(vec![], vec![], Some(N))), &[], N, false);
    out_is(defs(any()), &[], N, false);
    out_is(defs(zero()), &[], N, true);
}

#[test]
fn every_term_against_a_recursive_case() {
    out_is(vec![(N, rest(vec![(F, vec![Some(N), None])], vec![], None))], &[], N, false);
    out_is(vec![(N, cases(vec![(F, vec![Some(N)]), (Z, vec![])]))], &[], N, true);
}

#[test]
fn the_naturals_against_at_most_one() {
    let defs = || vec![(N, nat(N)), (A, cases(vec![(Z, vec![]), (SU, vec![Some(ZS)])])), (ZS, zero())];
    out_is(defs(), &[A], N, false);
    out_is(defs(), &[N], A, true);
}

#[test]
fn each_argument_is_paired_with_its_own_position() {
    let defs = || {
        with_sets(vec![
            (A, cases(vec![(F, vec![Some(U), Some(X)])])),
            (B, cases(vec![(F, vec![Some(U), Some(X)])])),
            (C, cases(vec![(F, vec![Some(X), Some(U)])])),
        ])
    };
    out_is(defs(), &[A], B, false);
    out_is(defs(), &[A], C, true);
}

#[test]
fn out_at_the_last_of_three_arguments_only() {
    let defs = |n: Name| {
        with_sets(vec![
            (A, cases(vec![(F, vec![Some(U), Some(U), Some(X)])])),
            (B, cases(vec![(F, vec![Some(n); 3])])),
        ])
    };
    out_is(defs(U), &[A], B, true);
    out_is(defs(X), &[A], B, false);
}

#[test]
fn an_argument_out_beside_an_argument_with_no_member_is_not_out() {
    let defs = |d: Name, last: Option<Name>| {
        with_sets(vec![
            (A, cases(vec![(F, vec![Some(X), Some(d)])])),
            (B, cases(vec![(F, vec![Some(U), last])])),
        ])
    };
    out_is(defs(D, None), &[A], B, false);
    out_is(defs(ZS, None), &[A], B, true);
    out_is(defs(D, Some(D)), &[A], B, false);
}

#[test]
fn an_argument_of_every_term_in_the_sort_asks_nothing() {
    let defs = || {
        with_sets(vec![
            (A, cases(vec![(F, vec![Some(X)])])),
            (B, cases(vec![(F, vec![None])])),
            (C, cases(vec![(F, vec![Some(X), Some(D)])])),
            (N, cases(vec![(F, vec![None, None])])),
        ])
    };
    out_is(defs(), &[A], B, false);
    out_is(defs(), &[C], N, false);
}

#[test]
fn an_argument_of_every_term_in_the_conjunction() {
    let defs = |k: Def| vec![(A, cases(vec![(F, vec![None])])), (N, cases(vec![(F, vec![Some(K)])])), (K, k), (ZS, zero())];
    out_is(defs(zero()), &[A], N, true);
    out_is(defs(any()), &[A], N, false);
    out_is(defs(rest(vec![(Z, vec![])], vec![], None)), &[A], N, false);
    out_is(defs(rest(vec![], vec![(Z, 0)], None)), &[A], N, true);
    out_is(defs(rest(vec![], vec![], Some(K))), &[A], N, false);
    out_is(defs(rest(vec![], vec![], Some(ZS))), &[A], N, true);
}

#[test]
fn every_term_in_one_sort_and_a_sort_in_another_at_one_argument() {
    let defs = || {
        with_sets(vec![
            (A, cases(vec![(F, vec![None])])),
            (B, cases(vec![(F, vec![Some(X)])])),
            (N, cases(vec![(F, vec![Some(X)])])),
        ])
    };
    out_is(defs(), &[A, B], N, false);
    out_is(defs(), &[A], N, true);
}

#[test]
fn the_same_symbol_at_several_arities_in_one_sort() {
    let a = || (A, cases(vec![(F, vec![None]), (F, vec![None, None])]));
    out_is(vec![a(), (N, cases(vec![(F, vec![None])]))], &[A], N, true);
    out_is(vec![a(), (N, cases(vec![(F, vec![None, None]), (F, vec![None])]))], &[A], N, false);
    out_is(vec![(A, cases(vec![(F, vec![]), (F, vec![None])])), (N, cases(vec![(F, vec![])]))], &[A], N, true);
}

#[test]
fn reads_the_first_of_duplicate_cases_of_the_conjunction() {
    let defs = |first: Name, second: Name| {
        with_sets(vec![
            (A, cases(vec![(F, vec![Some(first)]), (F, vec![Some(second)])])),
            (N, cases(vec![(F, vec![Some(U)])])),
        ])
    };
    out_is(defs(U, W), &[A], N, false);
    out_is(defs(W, U), &[A], N, true);
}

#[test]
fn reads_the_first_declaration_of_each_side() {
    out_is(vec![(A, zero()), (A, one(O)), (N, zero())], &[A], N, false);
    out_is(vec![(A, one(O)), (A, zero()), (N, zero())], &[A], N, true);
    out_is(vec![(N, zero()), (N, two(Z, O)), (A, one(O))], &[A], N, true);
    out_is(vec![(N, two(Z, O)), (N, zero()), (A, one(O))], &[A], N, false);
    // Whether every sort has a rest is read from the first declaration too.
    out_is(vec![(A, zero()), (A, any()), (N, zero())], &[A], N, false);
}

#[test]
fn sort_names_that_are_also_symbols() {
    let defs = || vec![(A, cases(vec![(A, vec![]), (F, vec![Some(B)])])), (B, cases(vec![(A, vec![])]))];
    out_is(defs(), &[B], A, false);
    out_is(defs(), &[A], B, true);
}

#[test]
fn many_roots_with_no_member_and_one_the_sort_refuses() {
    let defs = |g: Name| {
        let mut a: Vec<Case> = (0..50).map(|i| (1000 + i, vec![Some(D)])).collect();
        a.push((G, vec![Some(g)]));
        let n: Vec<Case> = (0..50).map(|i| (1000 + i, vec![None])).collect();
        vec![(A, cases(a)), (N, cases(n)), (ZS, zero()), (D, dead())]
    };
    out_is(defs(ZS), &[A], N, true);
    out_is(defs(D), &[A], N, false);
}

#[test]
fn the_sort_takes_by_its_rest_what_the_conjunction_has_by_a_case() {
    let defs = |n: Def| vec![(A, cases(vec![(Z, vec![]), (F, vec![Some(A)])])), (N, n), (D, dead())];
    out_is(defs(any()), &[A], N, false);
    out_is(defs(rest(vec![], vec![], Some(N))), &[A], N, false);
    out_is(defs(rest(vec![], vec![], Some(A))), &[A], N, false);
    out_is(defs(rest(vec![], vec![], Some(D))), &[A], N, true);
}

#[test]
fn the_sort_the_rest_asks_is_asked_of_the_arguments_of_a_case() {
    let defs = |k: Def| with_sets(vec![(A, cases(vec![(F, vec![Some(X)])])), (N, rest(vec![], vec![], Some(K))), (K, k)]);
    out_is(defs(one(CA)), &[A], N, true);
    out_is(defs(cases(vec![(CA, vec![]), (CB, vec![]), (CC, vec![])])), &[A], N, false);
}

#[test]
fn an_exclusion_of_the_sort_against_a_case_of_the_conjunction() {
    let defs = |arg: Option<Name>, ex: Key| {
        vec![(A, cases(vec![(Z, vec![]), (H, vec![arg])])), (N, rest(vec![], vec![ex], None)), (D, dead())]
    };
    out_is(defs(None, (H, 1)), &[A], N, true);
    out_is(defs(Some(D), (H, 1)), &[A], N, false);
    out_is(defs(None, (H, 2)), &[A], N, false);
    out_is(defs(None, (H, 0)), &[A], N, false);
}

#[test]
fn an_exclusion_reached_through_a_rest_that_asks_a_dead_sort() {
    let defs = |ex: Key| vec![(A, rest(vec![], vec![], Some(D))), (N, rest(vec![], vec![ex], None)), (D, dead())];
    out_is(defs((H, 1)), &[A], N, false);
    out_is(defs((H, 0)), &[A], N, true);
}

#[test]
fn an_exclusion_both_rests_share() {
    let defs = |ex: Key| vec![(A, rest(vec![], vec![ex], None)), (N, rest(vec![], vec![(H, 1)], None))];
    out_is(defs((H, 1)), &[A], N, false);
    out_is(defs((H, 2)), &[A], N, true);
}

#[test]
fn a_case_of_the_sort_narrows_its_own_exclusion() {
    let defs = |a: Option<Name>| {
        vec![(A, cases(vec![(H, vec![a])])), (N, rest(vec![(H, vec![Some(ZS)])], vec![(H, 1)], None)), (ZS, zero())]
    };
    out_is(defs(None), &[A], N, true);
    out_is(defs(Some(ZS)), &[A], N, false);
}

#[test]
fn one_sort_by_a_case_and_one_by_its_rest_join_at_the_argument() {
    let defs = |k: u32| {
        with_sets(vec![
            (A, rest(vec![], vec![], Some(X))),
            (B, cases(vec![(F, vec![Some(Y)]), (Z, vec![])])),
            (N, cases(vec![(F, vec![Some(K)]), (Z, vec![])])),
            (K, one(k)),
        ])
    };
    out_is(defs(CB), &[A, B], N, false);
    out_is(defs(CA), &[A, B], N, true);
}

#[test]
fn a_conjunction_of_rests_against_a_sort_without_a_rest() {
    let defs = |a: Def, n: Def| vec![(A, a), (N, n), (D, dead())];
    out_is(defs(any(), cases(vec![(Z, vec![]), (F, vec![None])])), &[A], N, true);
    out_is(defs(any(), dead()), &[A], N, true);
    out_is(defs(any(), zero()), &[A], Q, true);
    // A constant no declaration names needs no argument.
    out_is(defs(rest(vec![], vec![], Some(D)), zero()), &[A], N, true);
}

#[test]
fn a_root_no_declaration_names_needs_a_rest_in_every_sort() {
    let defs = |n: Def| vec![(A, any()), (B, zero()), (N, n)];
    out_is(defs(zero()), &[A, B], N, false);
    out_is(defs(one(O)), &[A, B], N, true);
}

#[test]
fn the_sort_the_rest_asks_is_compared_only_when_every_sort_has_a_rest() {
    // The members are `z` and `f(z)`, and `N` has both by its cases.
    let defs = vec![
        (A, rest(vec![], vec![], Some(ZS))),
        (B, cases(vec![(Z, vec![]), (F, vec![None])])),
        (N, rest(vec![(Z, vec![]), (F, vec![None])], vec![], Some(D))),
        (ZS, zero()),
        (D, dead()),
    ];
    out_is(defs, &[A, B], N, false);
}

#[test]
fn rests_of_a_conjunction_join_the_sorts_they_ask() {
    let defs = |n: Name| {
        with_sets(vec![
            (A, rest(vec![], vec![], Some(X))),
            (B, rest(vec![], vec![], Some(Y))),
            (N, rest(vec![], vec![], Some(n))),
        ])
    };
    out_is(defs(W), &[A, B], N, false);
    out_is(defs(W), &[A], N, true);
    out_is(defs(U), &[A, B], N, true);
}

#[test]
fn a_case_of_the_sort_with_a_dead_argument_under_its_rest() {
    let defs = |a: Def| vec![(A, a), (N, rest(vec![(F, vec![Some(D)])], vec![], None)), (ZS, zero()), (D, dead())];
    out_is(defs(any()), &[A], N, true);
    out_is(defs(rest(vec![], vec![], Some(ZS))), &[A], N, true);
    out_is(defs(rest(vec![], vec![(F, 1)], None)), &[A], N, false);
    out_is(defs(rest(vec![], vec![], Some(D))), &[A], N, false);
}

#[test]
fn a_case_of_the_sort_against_the_sort_the_rest_of_the_conjunction_asks() {
    let defs = |k: Def| with_sets(vec![(A, rest(vec![], vec![], Some(X))), (N, rest(vec![(F, vec![Some(K)])], vec![], None)), (K, k)]);
    out_is(defs(one(CA)), &[A], N, true);
    out_is(defs(two(CA, CB)), &[A], N, false);
}

#[test]
fn recursion_through_rests() {
    let defs = |n: Def| vec![(A, rest(vec![], vec![], Some(A))), (N, n)];
    out_is(defs(rest(vec![], vec![], Some(N))), &[A], N, false);
    out_is(defs(rest(vec![(Z, vec![])], vec![], Some(N))), &[A], N, false);
    out_is(defs(rest(vec![], vec![(H, 0)], Some(N))), &[A], N, true);
}

#[test]
fn a_chain_of_rests_is_out_from_the_far_end() {
    for flip in [false, true] {
        for (last, want) in [(O, true), (Z, false)] {
            let k = 500;
            let mut defs: Vec<(Name, Def)> = Vec::new();
            for i in 0..k {
                defs.push((link(i), rest(vec![], vec![], Some(link(i + 1)))));
                defs.push((side(i), rest(vec![], vec![], Some(side(i + 1)))));
            }
            defs.push((link(k), zero()));
            defs.push((side(k), one(last)));
            if flip {
                defs.reverse();
            }
            assert_eq!(fx(defs).out(&[link(0)], side(0)), want, "last {} flipped {}", last, flip);
        }
    }
}

#[test]
fn a_conjunction_is_included_although_neither_sort_is() {
    out_is(with_sets(vec![]), &[X, Y], W, false);
    out_is(with_sets(vec![]), &[X], W, true);
    out_is(with_sets(vec![]), &[Y], W, true);
}

#[test]
fn a_conjunction_with_no_member_although_each_sort_has_one() {
    let defs = || {
        vec![
            (A, cases(vec![(Z, vec![]), (SU, vec![Some(A)])])),
            (B, cases(vec![(O, vec![]), (SU, vec![Some(B)])])),
            (D, dead()),
        ]
    };
    out_is(defs(), &[A, B], D, false);
    out_is(defs(), &[A], B, true);
}

/// `A = f(A)`, `B = f(C)`, `C = f(B)`, with `z` in the sorts of `base`.
fn cycle(base: &[Name]) -> Vec<(Name, Def)> {
    let with = |n: Name, k: Name| {
        let mut cs = vec![(F, vec![Some(k)])];
        if base.contains(&n) {
            cs.push((Z, vec![]));
        }
        (n, cases(cs))
    };
    vec![with(A, A), with(B, C), with(C, B)]
}

#[test]
fn a_cycle_of_pairs_through_conjunctions() {
    out_is(cycle(&[A, B, C]), &[A, B], C, false);
    out_is(cycle(&[A, B]), &[A, B], C, true);
    // `f(z)` is in `A` and `C`, and `z` is not in `C`.
    out_is(cycle(&[A, B]), &[A, C], B, true);
    out_is(cycle(&[A]), &[A, C], B, false);
}

#[test]
fn the_pair_of_one_sort_with_another_is_not_their_conjunction() {
    // The pair of `B` with `A` is out, and the conjunction of `A` and `B`
    // has no member: `h` of it, with a dead sort beside, is nothing.
    let defs = vec![
        (X, cases(vec![(F, vec![Some(A)]), (H, vec![Some(B), Some(D)])])),
        (Y, cases(vec![(F, vec![Some(B)]), (H, vec![Some(B), Some(D)])])),
        (N, cases(vec![(H, vec![Some(A), None])])),
        (A, one(CA)),
        (B, one(CB)),
        (D, dead()),
    ];
    out_is(defs, &[X, Y], N, false);
}

#[test]
fn a_guard_found_to_have_a_member_only_after_many_rounds() {
    let table = |base: bool| {
        let mut defs: Vec<(Name, Def)> =
            (0..500).map(|i| (link(i), cases(vec![(F, vec![Some(link(i + 1))])]))).collect();
        defs.push((link(500), if base { zero() } else { dead() }));
        defs.push((A, cases(vec![(F, vec![Some(X), Some(link(0))])])));
        defs.push((N, cases(vec![(F, vec![Some(U), None])])));
        defs.push((X, two(CA, CB)));
        defs.push((U, one(CA)));
        defs
    };
    assert!(fx(table(true)).out(&[A], N));
    assert!(!fx(table(false)).out(&[A], N));
}

#[test]
fn a_chain_against_a_shorter_chain_and_a_chain_without_a_base() {
    let mut defs = chains(300, false);
    // `T299` is `z` already: one link fewer.
    defs.retain(|(n, _)| *n != side(299));
    defs.push((side(299), zero()));
    assert!(fx(defs).out(&[link(0)], side(0)));
    let mut defs = chains(300, true);
    defs.retain(|(n, _)| *n != link(300));
    defs.push((link(300), dead()));
    assert!(!fx(defs).out(&[link(0)], side(0)));
}

#[test]
fn does_not_reuse_flags_found_under_other_declarations() {
    let mut f = fx(vec![(A, zero()), (N, zero())]);
    let d1 = f.decls;
    let d2 = put_sorts(&mut f.s, &Sorts::new(vec![(A, zero()), (N, one(O))]));
    let d3 = put_sorts(&mut f.s, &Sorts::new(vec![(A, dead()), (N, one(O))]));
    let c = f.conj(&[A]);
    let n = f.name(N);
    for (d, want) in [(d1, false), (d2, true), (d3, false), (d1, false), (d2, true)] {
        assert_eq!(out(&mut f.s, d, f.names, c, n), want);
    }
}

#[test]
fn a_sort_with_1000_cases_and_1000_exclusions() {
    let wide = |with_z: bool| {
        let mut cs: Vec<Case> = (0..1000).map(|i| (2000 + i, vec![])).collect();
        if with_z {
            cs.push((Z, vec![]));
        }
        let ex: Vec<Key> = (0..1000).map(|i| (4000 + i, 1)).chain([(Z, 0)]).collect();
        vec![(A, zero()), (N, rest(cs, ex, None))]
    };
    let mut f = fx(wide(true));
    let (r, ticks) = f.ticks(&[A], N);
    assert!(r);
    assert!(ticks <= 200 * 2000, "{} ticks", ticks);
    assert!(fx(wide(false)).out(&[A], N));
}

#[test]
fn out_means_a_member_and_a_sort_of_the_conjunction_is_never_out() {
    let mut r = Rng(43);
    for _ in 0..150 {
        let mut f = fx(random_table(&mut r));
        let names = f.order.clone();
        for c in subsets(&names) {
            let has = f.live(&c);
            assert_eq!(f.out(&c, Q), has, "{:?} against an undeclared sort under {:?}", c, f.ss.defs);
            for n in &names {
                if f.out(&c, *n) {
                    assert!(has, "{:?} out of {} under {:?}", c, n, f.ss.defs);
                    assert!(!c.contains(n), "{:?} out of {} under {:?}", c, n, f.ss.defs);
                }
            }
        }
    }
}

// Against the specification.

#[test]
fn every_pair_agrees_with_the_specification_on_the_naturals() {
    check_all(nats());
}

#[test]
fn every_pair_agrees_with_the_specification_on_tables_of_odd_declarations() {
    check_all(vec![
        (A, cases(vec![(Z, vec![]), (SU, vec![Some(A)])])),
        (B, cases(vec![(SU, vec![None])])),
        (C, rest(vec![], vec![], None)),
        (X, rest(vec![(SU, vec![Some(A)])], vec![(F, 2), (Z, 0)], None)),
        (Y, cases(vec![(SU, vec![Some(D)]), (SU, vec![None]), (SU, vec![None, None])])),
        (ZS, rest(vec![], vec![], Some(A))),
        (N, cases(vec![(SU, vec![Some(Q)])])),
        (A, cases(vec![(O, vec![Some(E)])])),
        (D, dead()),
    ]);
}

#[test]
fn every_pair_agrees_with_the_specification_on_rests() {
    check_all(vec![
        (A, rest(vec![], vec![], Some(B))),
        (B, rest(vec![(Z, vec![])], vec![(F, 1)], Some(A))),
        (C, rest(vec![(F, vec![Some(A)])], vec![(Z, 0), (G, 2)], None)),
        (X, rest(vec![], vec![(Z, 0)], Some(X))),
        (Y, cases(vec![(Z, vec![]), (F, vec![Some(Y)]), (G, vec![Some(X), Some(A)])])),
        (D, dead()),
    ]);
}

fn random_table(r: &mut Rng) -> Vec<(Name, Def)> {
    let pool = [A, B, C, D, Q];
    let kid = |r: &mut Rng| if r.next(3) == 0 { None } else { Some(pool[r.next(pool.len())]) };
    let n = 1 + r.next(4);
    let mut defs = Vec::new();
    for _ in 0..n {
        let name = pool[r.next(4)];
        let mut cs = Vec::new();
        for _ in 0..r.next(4) {
            let arity = r.next(3);
            cs.push((r.next(3) as u32, (0..arity).map(|_| kid(r)).collect()));
        }
        let rest = if r.next(2) == 0 {
            let ex = (0..r.next(3)).map(|_| (r.next(3) as u32, r.next(3))).collect();
            Some((ex, kid(r)))
        } else {
            None
        };
        defs.push((name, Def { cases: cs, rest }));
    }
    defs
}

#[test]
fn every_pair_agrees_with_the_specification_on_random_small_tables() {
    let mut r = Rng(23);
    for _ in 0..400 {
        check_all(random_table(&mut r));
    }
}

/// The ground terms over the symbols `0..3` and one more, to a depth.
fn ground(depth: usize) -> Vec<P> {
    let mut out: Vec<P> = (0..4).map(|f| pf(f, vec![])).collect();
    for _ in 0..depth {
        let small = out.clone();
        for f in 0..4 {
            for a in &small {
                out.push(pf(f, vec![a.clone()]));
            }
            for a in small.iter().take(6) {
                for b in small.iter().take(6) {
                    out.push(pf(f, vec![a.clone(), b.clone()]));
                }
            }
        }
        out.sort();
        out.dedup();
    }
    out
}

#[test]
fn a_small_member_outside_the_sort_refutes_inclusion() {
    let mut r = Rng(29);
    let terms = ground(2);
    for _ in 0..150 {
        let mut f = fx(random_table(&mut r));
        let names = f.order.clone();
        for c in subsets(&names) {
            for n in names.iter().chain([&Q]) {
                let witness = terms.iter().find(|t| c.iter().all(|k| f.ss.member(*k, t)) && !f.ss.member(*n, t));
                if let Some(t) = witness {
                    assert!(!f.inc(&c, *n), "{:?} is in {:?} and not in {} under {:?}", t, c, n, f.ss.defs);
                }
            }
        }
    }
}

#[test]
fn inclusion_holds_of_every_small_member() {
    let mut r = Rng(31);
    let terms = ground(2);
    for _ in 0..150 {
        let mut f = fx(random_table(&mut r));
        let names = f.order.clone();
        for c in subsets(&names) {
            for n in &names {
                if f.inc(&c, *n) {
                    for t in &terms {
                        if c.iter().all(|k| f.ss.member(*k, t)) {
                            assert!(f.ss.member(*n, t), "{:?} of {:?} is not in {} under {:?}", t, c, n, f.ss.defs);
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn inclusion_is_transitive_on_random_small_tables() {
    let mut r = Rng(37);
    for _ in 0..150 {
        let mut f = fx(random_table(&mut r));
        let names = f.order.clone();
        for a in &names {
            for b in &names {
                for c in &names {
                    if f.inc(&[*a], *b) && f.inc(&[*b], *c) {
                        assert!(f.inc(&[*a], *c), "{} in {} in {} under {:?}", a, b, c, f.ss.defs);
                    }
                }
            }
        }
    }
}

#[test]
fn a_larger_conjunction_is_still_included_on_random_small_tables() {
    let mut r = Rng(41);
    for _ in 0..150 {
        let mut f = fx(random_table(&mut r));
        let names = f.order.clone();
        for c in subsets(&names) {
            for n in &names {
                if f.inc(&c, *n) {
                    for more in &names {
                        let mut bigger = c.clone();
                        if !bigger.contains(more) {
                            bigger.push(*more);
                        }
                        assert!(f.inc(&bigger, *n), "{:?} in {} under {:?}", bigger, n, f.ss.defs);
                    }
                }
            }
        }
    }
}

// Stress and ticks.

const LONG: usize = 100_000;

fn link(i: usize) -> Name {
    1000 + i as Name
}

fn side(i: usize) -> Name {
    500_000 + i as Name
}

/// `S0 = f(S1)`, ..., `S(n-1) = f(Sn)`, `Sn = z`, and the same for `T`
/// with `Tn` the constant `z`, or `o` when `differ`.
fn chains(n: usize, differ: bool) -> Vec<(Name, Def)> {
    let mut defs: Vec<(Name, Def)> = Vec::new();
    for i in 0..n {
        defs.push((link(i), cases(vec![(F, vec![Some(link(i + 1))])])));
        defs.push((side(i), cases(vec![(F, vec![Some(side(i + 1))])])));
    }
    defs.push((link(n), zero()));
    defs.push((side(n), if differ { cases(vec![(O, vec![])]) } else { zero() }));
    defs
}

#[test]
fn chains_of_2000_that_agree_and_that_differ_at_the_end() {
    assert!(inc_of(chains(2000, false), &[link(0)], side(0)));
    assert!(!inc_of(chains(2000, true), &[link(0)], side(0)));
}

#[test]
fn a_case_with_100000_arguments() {
    let defs = || {
        vec![
            (A, cases(vec![(F, vec![Some(X); LONG])])),
            (B, cases(vec![(F, vec![Some(Y); LONG])])),
            (X, zero()),
            (Y, cases(vec![(Z, vec![]), (O, vec![])])),
        ]
    };
    let mut f = fx(defs());
    let (r, ticks) = f.ticks(&[A], B);
    assert!(r);
    assert!(ticks <= 200 * LONG as u64, "{} ticks", ticks);
    assert!(!inc_of(defs(), &[B], A));
}

#[test]
fn a_case_with_100000_arguments_out_at_the_last() {
    let mut kids = vec![Some(X); LONG];
    kids[LONG - 1] = Some(Y);
    let defs = vec![
        (A, cases(vec![(F, kids)])),
        (B, cases(vec![(F, vec![Some(X); LONG])])),
        (X, zero()),
        (Y, cases(vec![(Z, vec![]), (O, vec![])])),
    ];
    assert!(!inc_of(defs, &[A], B));
}

#[test]
fn a_conjunction_of_many_sorts() {
    let mut defs: Vec<(Name, Def)> = (0..200).map(|i| (link(i), nat(link(i)))).collect();
    defs.push((N, nat(N)));
    defs.push((E, nat_even()));
    defs.push((OD, nat_odd()));
    let c: Vec<Name> = (0..200).map(link).collect();
    assert!(inc_of(defs.clone(), &c, N));
    assert!(!inc_of(defs, &c, E));
}

#[test]
fn ticks_are_at_most_cubic_in_the_chain_length() {
    for differ in [false, true] {
        let mut last = 0;
        for n in [100usize, 200, 400] {
            let mut f = fx(chains(n, differ));
            let (r, ticks) = f.ticks(&[link(0)], side(0));
            assert_eq!(r, !differ);
            let n = n as u64;
            assert!(ticks <= 100 * n * n * n + 1000, "chains of {}: {} ticks", n, ticks);
            assert!(ticks > last);
            last = ticks;
        }
    }
}

#[test]
fn ticks_grow_with_the_pairs_reached_not_the_table() {
    let table = |extra: usize| {
        let mut defs = vec![
            (A, cases(vec![(F, vec![Some(B)])])),
            (B, cases(vec![(F, vec![Some(C)])])),
            (C, zero()),
            (X, cases(vec![(F, vec![Some(Y)])])),
            (Y, cases(vec![(F, vec![Some(C)]), (Z, vec![])])),
        ];
        defs.extend((0..extra).map(|i| (link(i), cases(vec![(F, vec![Some(link(i))])]))));
        defs
    };
    let ticks = |extra: usize| {
        let (r, t) = fx(table(extra)).ticks(&[A], X);
        assert!(r);
        t
    };
    let (t0, t1, t2) = (ticks(0), ticks(1000), ticks(2000));
    // Only the list of names and the table get longer: a fixed number of
    // ticks for each name, for each conjunction made and each sort looked
    // up.
    assert!(t1 - t0 <= 400 * 1000, "{} then {}", t0, t1);
    assert!(t2 - t1 <= 400 * 1000, "{} then {}", t1, t2);
}
