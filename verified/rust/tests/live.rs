//! Whether a conjunction of sorts has a member, and how many it has, on the
//! store, against the specification (`live` of
//! `lean/RwLog/Sorts/Empty.lean` and `count` of
//! `lean/RwLog/Sorts/Count.lean`).

mod common;

use common::sorts::*;
use common::{get, put, spent, T};
use rwlog_core::sorts::{conj_of, count, live, member, Count};
use rwlog_core::store::{Node, Store, TermId};
use std::collections::{BTreeMap, BTreeSet};

// Symbols.
const Z: u32 = 0;
const O: u32 = 1;
const F: u32 = 2;
const G: u32 = 3;
const H: u32 = 4;
const SU: u32 = 5;
const CA: u32 = 6;
const CB: u32 = 7;
const CC: u32 = 8;

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

    fn live(&mut self, c: &[Name]) -> bool {
        let c = self.conj(c);
        live(&mut self.s, self.decls, self.names, c)
    }

    fn ticks(&mut self, c: &[Name]) -> (bool, u64) {
        let c = self.conj(c);
        let (decls, names) = (self.decls, self.names);
        spent(&mut self.s, |s| live(s, decls, names, c))
    }
}

fn live_of(defs: Vec<(Name, Def)>, c: &[Name]) -> bool {
    fx(defs).live(c)
}

/// `live` of the specification: saturation of `grow` over every set of
/// names.
fn live_spec(ss: &Sorts) -> BTreeSet<Conj> {
    let names = ss.all_names();
    let subsets: Vec<Conj> = (0..1usize << names.len())
        .map(|m| names.iter().enumerate().filter(|(i, _)| m >> i & 1 == 1).map(|(_, n)| *n).collect())
        .collect();
    let def = |n: Name| ss.defs.iter().find(|(m, _)| *m == n).map(|(_, d)| d);
    let mut have: BTreeSet<Conj> = BTreeSet::new();
    loop {
        let mut next = have.clone();
        for c in &subsets {
            let rest_ok = c.iter().all(|n| def(*n).is_some_and(|d| d.rest.is_some()));
            let keys: BTreeSet<Key> = c
                .iter()
                .filter_map(|n| def(*n))
                .flat_map(|d| d.cases.iter().map(|(f, a)| (*f, a.len())))
                .collect();
            let by_key = keys.iter().any(|k| match ss.step_conj(c, *k) {
                Some(kids) => kids.iter().all(|k| have.contains(k)),
                None => false,
            });
            if rest_ok || by_key {
                next.insert(c.clone());
            }
        }
        if next == have {
            return have;
        }
        have = next;
    }
}

/// Every subset of the names: the store agrees with the specification.
fn check_all(defs: Vec<(Name, Def)>) {
    let mut f = fx(defs);
    let spec = live_spec(&f.ss);
    let names = f.order.clone();
    for m in 0..1usize << names.len() {
        let c: Vec<Name> = names.iter().enumerate().filter(|(i, _)| m >> i & 1 == 1).map(|(_, n)| *n).collect();
        let set: Conj = c.iter().copied().collect();
        assert_eq!(f.live(&c), spec.contains(&set), "{:?} under {:?}", c, f.ss.defs);
    }
}

struct Rng(u64);

impl Rng {
    fn next(&mut self, n: usize) -> usize {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % n
    }
}

// Basics.

#[test]
fn live_of_the_empty_conjunction_with_no_declarations() {
    assert!(live_of(vec![], &[]));
}

#[test]
fn live_of_the_empty_conjunction_with_only_dead_sorts() {
    assert!(live_of(vec![(A, dead())], &[]));
}

#[test]
fn live_of_an_undeclared_unmentioned_name_is_false() {
    let mut f = fx(vec![(A, zero())]);
    let c = put_names(&mut f.s, &[Q]);
    assert!(!live(&mut f.s, f.decls, f.names, c));
}

#[test]
fn live_of_a_mentioned_but_undeclared_name_is_false() {
    let defs = || vec![(A, cases(vec![(F, vec![Some(Q)])]))];
    assert!(!live_of(defs(), &[Q]));
    assert!(!live_of(defs(), &[A]));
}

#[test]
fn live_of_a_live_sort_with_an_undeclared_name_is_false() {
    assert!(!live_of(vec![(A, zero()), (B, cases(vec![(F, vec![Some(Q)])]))], &[A, Q]));
}

#[test]
fn live_of_a_sort_with_no_cases_and_no_rest_is_false() {
    assert!(!live_of(vec![(A, dead())], &[A]));
}

#[test]
fn live_of_a_constant_case() {
    assert!(live_of(vec![(A, zero())], &[A]));
}

#[test]
fn live_reads_the_first_declaration_of_a_name_declared_twice() {
    assert!(!live_of(vec![(A, dead()), (A, zero())], &[A]));
    assert!(live_of(vec![(A, zero()), (A, dead())], &[A]));
}

// Rest.

#[test]
fn live_of_a_rest_alone() {
    assert!(live_of(vec![(A, rest(vec![], vec![], None))], &[A]));
}

#[test]
fn live_of_a_rest_whose_argument_sort_is_dead() {
    assert!(live_of(vec![(A, rest(vec![], vec![], Some(D))), (D, dead())], &[A]));
}

#[test]
fn live_of_a_rest_whose_argument_sort_is_undeclared() {
    assert!(live_of(vec![(A, rest(vec![], vec![], Some(Q)))], &[A]));
}

#[test]
fn live_of_a_rest_with_exclusions() {
    assert!(live_of(vec![(A, rest(vec![], vec![(CA, 0), (F, 2)], None))], &[A]));
}

#[test]
fn live_of_a_rest_with_only_dead_cases() {
    assert!(live_of(vec![(A, rest(vec![(F, vec![Some(D)])], vec![], None)), (D, dead())], &[A]));
}

#[test]
fn live_of_two_sorts_with_rests_excluding_each_others_symbols() {
    let defs = vec![(A, rest(vec![], vec![(CA, 0)], None)), (B, rest(vec![], vec![(CB, 0)], None))];
    assert!(live_of(defs, &[A, B]));
}

#[test]
fn live_of_a_rest_and_a_dead_sort_is_false() {
    assert!(!live_of(vec![(A, rest(vec![], vec![], None)), (B, dead())], &[A, B]));
}

#[test]
fn live_through_a_case_one_sort_accepts_by_its_rest() {
    let defs = vec![(A, rest(vec![], vec![], None)), (B, cases(vec![(CA, vec![])]))];
    assert!(live_of(defs, &[A, B]));
}

#[test]
fn live_is_false_when_the_rest_excludes_the_only_shared_key() {
    let defs = vec![(A, rest(vec![], vec![(CA, 0)], None)), (B, cases(vec![(CA, vec![])]))];
    assert!(!live_of(defs, &[A, B]));
}

#[test]
fn live_takes_the_rest_argument_sort_for_a_key_accepted_by_rest() {
    let defs = |d: Def| vec![(A, rest(vec![], vec![], Some(D))), (B, cases(vec![(F, vec![None])])), (D, d)];
    assert!(!live_of(defs(dead()), &[A, B]));
    assert!(live_of(defs(zero()), &[A, B]));
}

#[test]
fn live_exclusion_of_another_arity_does_not_refuse() {
    let defs = |n: usize| vec![(A, rest(vec![], vec![(F, n)], None)), (B, cases(vec![(F, vec![None])]))];
    assert!(live_of(defs(2), &[A, B]));
    assert!(!live_of(defs(1), &[A, B]));
}

#[test]
fn live_case_overrides_the_exclusion_of_the_same_key() {
    let defs = vec![(A, rest(vec![(CA, vec![])], vec![(CA, 0)], None)), (B, cases(vec![(CA, vec![])]))];
    assert!(live_of(defs, &[A, B]));
}

// Conjunctions and keys.

#[test]
fn live_of_two_sorts_with_disjoint_cases_is_false() {
    let defs = || vec![(A, cases(vec![(CA, vec![])])), (B, cases(vec![(CB, vec![])]))];
    assert!(!live_of(defs(), &[A, B]));
    assert!(live_of(defs(), &[A]));
    assert!(live_of(defs(), &[B]));
}

#[test]
fn live_of_two_sorts_sharing_one_key() {
    let defs = vec![
        (A, cases(vec![(CA, vec![]), (CB, vec![])])),
        (B, cases(vec![(CB, vec![]), (CC, vec![])])),
    ];
    assert!(live_of(defs, &[A, B]));
}

#[test]
fn live_joins_the_argument_sorts_of_a_shared_key() {
    let defs = |y: u32| {
        vec![
            (A, cases(vec![(F, vec![Some(X)])])),
            (B, cases(vec![(F, vec![Some(Y)])])),
            (X, cases(vec![(CA, vec![]), (CB, vec![])])),
            (Y, cases(vec![(y, vec![])])),
        ]
    };
    assert!(live_of(defs(CB), &[A, B]));
    assert!(!live_of(defs(CC), &[A, B]));
}

#[test]
fn live_same_symbol_at_different_arities_are_different_keys() {
    let defs = vec![(A, cases(vec![(F, vec![None])])), (B, cases(vec![(F, vec![None, None])]))];
    assert!(!live_of(defs, &[A, B]));
    let defs = vec![(A, cases(vec![(F, vec![Some(D)]), (F, vec![None, None])])), (D, dead())];
    assert!(live_of(defs, &[A]));
}

#[test]
fn live_reads_the_first_of_duplicate_cases() {
    let defs = |first: Name, second: Name| {
        vec![
            (A, cases(vec![(F, vec![Some(first)]), (F, vec![Some(second)])])),
            (D, dead()),
            (ZS, zero()),
        ]
    };
    assert!(!live_of(defs(D, ZS), &[A]));
    assert!(live_of(defs(ZS, D), &[A]));
}

#[test]
fn live_of_a_case_with_any_term_arguments() {
    assert!(live_of(vec![(A, cases(vec![(F, vec![None, None])]))], &[A]));
}

#[test]
fn live_argument_any_term_in_one_sort_and_a_sort_in_another() {
    let defs = |d: Def| vec![(A, cases(vec![(F, vec![None])])), (B, cases(vec![(F, vec![Some(D)])])), (D, d)];
    assert!(!live_of(defs(dead()), &[A, B]));
    assert!(live_of(defs(zero()), &[A, B]));
}

#[test]
fn live_is_false_when_one_argument_is_dead() {
    let base = || vec![(D, dead()), (ZS, zero())];
    let mut defs = base();
    defs.push((A, cases(vec![(F, vec![Some(ZS), Some(D)])])));
    assert!(!live_of(defs, &[A]));
    let mut defs = base();
    defs.push((A, cases(vec![(F, vec![Some(ZS), Some(D)]), (G, vec![Some(ZS), Some(ZS)])])));
    assert!(live_of(defs, &[A]));
}

#[test]
fn live_dead_first_alternative_live_last_and_the_reverse() {
    let alts = vec![(F, vec![Some(D)]), (G, vec![Some(D)]), (H, vec![Some(ZS)])];
    let mut rev = alts.clone();
    rev.reverse();
    for a in [alts, rev] {
        assert!(live_of(vec![(A, cases(a)), (D, dead()), (ZS, zero())], &[A]));
    }
}

#[test]
fn live_argument_conjunction_is_the_empty_conjunction_among_sorted_ones() {
    let defs = |m: Name| vec![(A, cases(vec![(F, vec![None, Some(m), None])])), (D, dead()), (ZS, zero())];
    assert!(live_of(defs(ZS), &[A]));
    assert!(!live_of(defs(D), &[A]));
}

// Recursion and cycles.

#[test]
fn live_of_recursion_without_a_base_case_is_false() {
    assert!(!live_of(vec![(A, cases(vec![(F, vec![Some(A)])]))], &[A]));
    assert!(!live_of(vec![(A, cases(vec![(F, vec![Some(A), Some(A)])]))], &[A]));
}

#[test]
fn live_of_recursion_with_a_base_case() {
    assert!(live_of(vec![(N, cases(vec![(Z, vec![]), (SU, vec![Some(N)])]))], &[N]));
}

#[test]
fn live_of_recursion_with_a_rest_as_base() {
    assert!(live_of(vec![(A, rest(vec![(F, vec![Some(A)])], vec![], None))], &[A]));
}

#[test]
fn live_of_mutual_recursion_without_a_base_is_false() {
    let defs = || vec![(A, cases(vec![(F, vec![Some(B)])])), (B, cases(vec![(G, vec![Some(A)])]))];
    assert!(!live_of(defs(), &[A]));
    assert!(!live_of(defs(), &[B]));
}

#[test]
fn live_of_mutual_recursion_with_a_base_in_one() {
    let defs =
        || vec![(A, cases(vec![(F, vec![Some(B)])])), (B, cases(vec![(G, vec![Some(A)]), (Z, vec![])]))];
    assert!(live_of(defs(), &[A]));
    assert!(live_of(defs(), &[B]));
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
fn live_of_a_cycle_through_conjunctions_without_a_base_is_false() {
    assert!(!live_of(cycle(&[]), &[A, B]));
}

#[test]
fn live_of_a_cycle_through_conjunctions_with_a_base_far_away() {
    assert!(live_of(cycle(&[A, B, C]), &[A, B]));
    // `{A, C}` has `z`, and `{A, B}` reaches it by `f`.
    assert!(live_of(cycle(&[A, C]), &[A, B]));
    assert!(!live_of(cycle(&[A]), &[A, B]));
}

#[test]
fn live_of_a_conjunction_dead_although_each_sort_is_live() {
    let defs = || {
        vec![
            (A, cases(vec![(Z, vec![]), (SU, vec![Some(A)])])),
            (B, cases(vec![(O, vec![]), (SU, vec![Some(B)])])),
        ]
    };
    assert!(!live_of(defs(), &[A, B]));
    assert!(live_of(defs(), &[A]));
    assert!(live_of(defs(), &[B]));
}

#[test]
fn live_of_even_and_odd_naturals_is_false_but_even_and_nat_is_true() {
    let defs = || {
        vec![
            (E, cases(vec![(Z, vec![]), (SU, vec![Some(OD)])])),
            (OD, cases(vec![(SU, vec![Some(E)])])),
            (N, cases(vec![(Z, vec![]), (SU, vec![Some(N)])])),
        ]
    };
    assert!(!live_of(defs(), &[E, OD]));
    assert!(live_of(defs(), &[E, N]));
    assert!(live_of(defs(), &[OD, N]));
}

#[test]
fn live_shrinking_conjunction() {
    let defs = vec![
        (A, cases(vec![(F, vec![Some(X)])])),
        (B, cases(vec![(F, vec![Some(X)])])),
        (X, zero()),
    ];
    assert!(live_of(defs, &[A, B]));
}

// Propagation order.

fn link(i: usize) -> Name {
    1000 + i as Name
}

/// `S0 = f(S1)`, ..., `S(n-1) = f(Sn)`, and `Sn` the constant `z` or
/// nothing.
fn chain(n: usize, base: bool, base_first: bool) -> Vec<(Name, Def)> {
    let mut defs: Vec<(Name, Def)> = (0..n).map(|i| (link(i), cases(vec![(F, vec![Some(link(i + 1))])]))).collect();
    defs.push((link(n), if base { zero() } else { dead() }));
    if base_first {
        defs.reverse();
    }
    defs
}

#[test]
fn live_chain_declared_base_last() {
    assert!(live_of(chain(2000, true, false), &[link(0)]));
}

#[test]
fn live_chain_declared_base_first() {
    assert!(live_of(chain(2000, true, true), &[link(0)]));
}

#[test]
fn live_chain_without_a_base_is_false() {
    assert!(!live_of(chain(2000, false, false), &[link(0)]));
    assert!(!live_of(chain(2000, false, true), &[link(0)]));
}

#[test]
fn live_chain_queried_in_the_middle() {
    // The links before the middle have no member of their own.
    let mut defs = chain(200, true, false);
    for d in defs.iter_mut().take(100) {
        d.1 = dead();
    }
    assert!(live_of(defs.clone(), &[link(100)]));
    assert!(!live_of(defs, &[link(50)]));
}

fn side(i: usize) -> Name {
    5000 + i as Name
}

/// `Si = f(S(i+1), T(i+1))` and `Ti` likewise, with the given bases.
fn ladder(n: usize, s_base: bool, t_base: bool) -> Vec<(Name, Def)> {
    let mut defs = Vec::new();
    for i in 0..n {
        let step = || cases(vec![(F, vec![Some(link(i + 1)), Some(side(i + 1))])]);
        defs.push((link(i), step()));
        defs.push((side(i), step()));
    }
    defs.push((link(n), if s_base { zero() } else { dead() }));
    defs.push((side(n), if t_base { zero() } else { dead() }));
    defs
}

#[test]
fn live_two_argument_chain_needs_both_branches() {
    assert!(live_of(ladder(100, true, true), &[link(0)]));
    assert!(!live_of(ladder(100, true, false), &[link(0)]));
    assert!(!live_of(ladder(100, false, true), &[link(0)]));
}

// State and contract.

fn nat_table() -> Vec<(Name, Def)> {
    vec![
        (E, cases(vec![(Z, vec![]), (SU, vec![Some(OD)])])),
        (OD, cases(vec![(SU, vec![Some(E)])])),
        (N, cases(vec![(Z, vec![]), (SU, vec![Some(N)])])),
        (D, dead()),
    ]
}

#[test]
fn live_leaves_the_stack_empty() {
    let mut f = fx(nat_table());
    assert!(f.live(&[OD, N]));
    assert!(f.s.pop().is_none());
    assert!(!f.live(&[E, OD]));
    assert!(f.s.pop().is_none());
}

#[test]
fn live_gives_the_same_answer_when_called_again() {
    let mut f = fx(nat_table());
    for _ in 0..3 {
        assert!(f.live(&[OD, N]));
    }
    for _ in 0..3 {
        assert!(!f.live(&[E, OD]));
        assert!(f.live(&[E, N]));
        assert!(!f.live(&[D]));
    }
}

#[test]
fn live_does_not_see_flags_of_an_earlier_call_in_tables_a_and_b() {
    let mut f = fx(nat_table());
    let n = f.s.alloc(Node::Sym(N));
    let z = f.s.alloc(Node::Sym(Z));
    assert!(member(&mut f.s, f.decls, n, z));
    assert!(f.s.pop().is_none());
    let list = put_names(&mut f.s, &[E, OD, D]);
    conj_of(&mut f.s, f.names, list);
    assert!(f.live(&[E, N]));
    assert!(!f.live(&[E, OD]));
    assert!(!f.live(&[D]));
    assert!(f.live(&[]));
}

#[test]
fn live_of_every_subset_agrees_with_the_specification_on_tables_of_odd_declarations() {
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
        let rest = if r.next(3) == 0 {
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
fn live_agrees_with_the_specification_on_random_small_tables() {
    let mut r = Rng(7);
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
fn live_is_true_whenever_a_small_member_exists() {
    let mut r = Rng(11);
    let terms = ground(1);
    for _ in 0..150 {
        let mut f = fx(random_table(&mut r));
        let names = f.order.clone();
        for m in 0..1usize << names.len() {
            let c: Vec<Name> = names.iter().enumerate().filter(|(i, _)| m >> i & 1 == 1).map(|(_, n)| *n).collect();
            if terms.iter().any(|t| c.iter().all(|n| f.ss.member(*n, t))) {
                assert!(f.live(&c), "{:?} has a member under {:?}", c, f.ss.defs);
            }
        }
    }
}

// Stress and ticks.

const LONG: usize = 100_000;

#[test]
fn live_of_a_case_with_100000_arguments() {
    let mut f = fx(vec![(A, cases(vec![(F, vec![Some(ZS); LONG])])), (ZS, zero())]);
    let (r, ticks) = f.ticks(&[A]);
    assert!(r);
    assert!(ticks <= 60 * LONG as u64, "{} ticks", ticks);
}

#[test]
fn live_of_100000_argument_case_with_the_last_argument_dead() {
    let mut kids = vec![Some(ZS); LONG];
    kids[LONG - 1] = Some(D);
    assert!(!live_of(vec![(A, cases(vec![(F, kids)])), (ZS, zero()), (D, dead())], &[A]));
}

#[test]
fn live_of_a_conjunction_of_many_sorts() {
    let defs: Vec<(Name, Def)> =
        (0..300).map(|i| (link(i), cases(vec![(Z, vec![]), (SU, vec![Some(link(i))])]))).collect();
    let c: Vec<Name> = (0..300).map(link).collect();
    assert!(live_of(defs, &c));
}

#[test]
fn live_ticks_are_at_most_quadratic_in_the_chain_length() {
    for base_first in [false, true] {
        let mut last = 0;
        for n in [250usize, 500, 1000] {
            let mut f = fx(chain(n, true, base_first));
            let (r, ticks) = f.ticks(&[link(0)]);
            assert!(r);
            let n = n as u64;
            assert!(ticks <= 40 * n * n + 1000, "chain of {}: {} ticks", n, ticks);
            assert!(ticks > last);
            last = ticks;
        }
    }
}

#[test]
fn live_ticks_grow_with_the_reachable_set_not_the_table() {
    let table = |extra: usize| {
        let mut defs = vec![
            (A, cases(vec![(F, vec![Some(B)])])),
            (B, cases(vec![(F, vec![Some(C)])])),
            (C, zero()),
        ];
        defs.extend((0..extra).map(|i| (link(i), cases(vec![(F, vec![Some(link(i))])]))));
        defs
    };
    let ticks = |extra: usize| fx(table(extra)).ticks(&[A]).1;
    let (t0, t1, t2) = (ticks(0), ticks(1000), ticks(2000));
    // Only the list of names gets longer: a fixed number of ticks for each
    // name, for each conjunction made.
    assert!(t1 - t0 <= 100 * 1000, "{} then {}", t0, t1);
    assert!(t2 - t1 <= 100 * 1000, "{} then {}", t1, t2);
}

#[test]
fn live_of_one_sort_among_many_reaches_few_conjunctions() {
    let mut defs: Vec<(Name, Def)> = (0..20).map(|i| (link(i), cases(vec![(F, vec![Some(link(i))])]))).collect();
    defs.push((A, zero()));
    let mut f = fx(defs);
    let (r, ticks) = f.ticks(&[A]);
    assert!(r);
    assert!(ticks <= 2000, "{} ticks", ticks);
    let (r, ticks) = f.ticks(&[link(3)]);
    assert!(!r);
    assert!(ticks <= 2000, "{} ticks", ticks);
}

// How many members.

/// How many members, with the member read back.
#[derive(Clone, Debug, PartialEq)]
enum Cnt {
    None,
    One(T),
    Many,
}

fn one(p: P) -> Cnt {
    Cnt::One(p.tree())
}

fn c0(f: u32) -> P {
    pf(f, vec![])
}

fn z() -> P {
    c0(Z)
}

fn f1(a: P) -> P {
    pf(F, vec![a])
}

impl Fx {
    fn count_node(&mut self, c: &[Name]) -> Count {
        let c = self.conj(c);
        count(&mut self.s, self.decls, self.names, c)
    }

    fn count(&mut self, c: &[Name]) -> Cnt {
        match self.count_node(c) {
            Count::None => Cnt::None,
            Count::One(t) => Cnt::One(get(&mut self.s, t)),
            Count::Many => Cnt::Many,
        }
    }

    /// Is the answer this one member, as a node? The term is not read back.
    fn counts_one(&mut self, c: &[Name], t: TermId) -> bool {
        match self.count_node(c) {
            Count::One(m) => self.s.same(m, t),
            _ => false,
        }
    }

    fn count_ticks(&mut self, c: &[Name]) -> (Count, u64) {
        let c = self.conj(c);
        let (decls, names) = (self.decls, self.names);
        spent(&mut self.s, |s| count(s, decls, names, c))
    }
}

fn count_of(defs: Vec<(Name, Def)>, c: &[Name]) -> Cnt {
    fx(defs).count(c)
}

fn subsets(names: &[Name]) -> Vec<Vec<Name>> {
    (0..1usize << names.len())
        .map(|m| names.iter().enumerate().filter(|(i, _)| m >> i & 1 == 1).map(|(_, n)| *n).collect())
        .collect()
}

/// `count` of the specification, for every set of names: `live`, and the
/// rounds of `one` until none finds a new member.
fn count_spec(ss: &Sorts) -> BTreeMap<Conj, Cnt> {
    let names = ss.all_names();
    let live = live_spec(ss);
    let def = |n: Name| ss.defs.iter().find(|(m, _)| *m == n).map(|(_, d)| d);
    let all: Vec<Conj> = subsets(&names).into_iter().map(|c| c.into_iter().collect()).collect();
    let mut have: BTreeMap<Conj, P> = BTreeMap::new();
    loop {
        let mut next = have.clone();
        for c in &all {
            let rest_ok = c.iter().all(|n| def(*n).is_some_and(|d| d.rest.is_some()));
            let keys: BTreeSet<Key> = c
                .iter()
                .filter_map(|n| def(*n))
                .flat_map(|d| d.cases.iter().map(|(f, a)| (*f, a.len())))
                .collect();
            let live_keys: Vec<(Key, Vec<Conj>)> = keys
                .iter()
                .filter_map(|k| ss.step_conj(c, *k).map(|kids| (*k, kids)))
                .filter(|(_, kids)| kids.iter().all(|k| live.contains(k)))
                .collect();
            if rest_ok || live_keys.len() != 1 {
                continue;
            }
            let ((f, _), kids) = &live_keys[0];
            let args: Option<Vec<P>> = kids.iter().map(|k| have.get(k).cloned()).collect();
            if let Some(args) = args {
                next.insert(c.clone(), pf(*f, args));
            }
        }
        if next == have {
            break;
        }
        have = next;
    }
    all.into_iter()
        .map(|c| {
            let n = match have.get(&c) {
                Some(t) => one(t.clone()),
                None if live.contains(&c) => Cnt::Many,
                None => Cnt::None,
            };
            (c, n)
        })
        .collect()
}

/// Every subset of the names: the store agrees with the specification.
fn check_all_counts(defs: Vec<(Name, Def)>) {
    let mut f = fx(defs);
    let spec = count_spec(&f.ss);
    for c in subsets(&f.order.clone()) {
        let set: Conj = c.iter().copied().collect();
        assert_eq!(f.count(&c), spec[&set], "{:?} under {:?}", c, f.ss.defs);
    }
}

fn nat() -> Def {
    cases(vec![(Z, vec![]), (SU, vec![Some(N)])])
}

// Counting: basics.

#[test]
fn count_of_the_empty_conjunction_with_no_declarations_is_many() {
    assert_eq!(count_of(vec![], &[]), Cnt::Many);
}

#[test]
fn count_of_the_empty_conjunction_with_only_dead_sorts_is_many() {
    assert_eq!(count_of(vec![(A, dead())], &[]), Cnt::Many);
}

#[test]
fn count_of_an_undeclared_unmentioned_name_is_none() {
    let mut f = fx(vec![(A, zero())]);
    let c = put_names(&mut f.s, &[Q]);
    assert!(matches!(count(&mut f.s, f.decls, f.names, c), Count::None));
}

#[test]
fn count_of_a_mentioned_but_undeclared_name_is_none() {
    let defs = || vec![(A, cases(vec![(F, vec![Some(Q)])]))];
    assert_eq!(count_of(defs(), &[Q]), Cnt::None);
    assert_eq!(count_of(defs(), &[A]), Cnt::None);
}

#[test]
fn count_of_a_unique_sort_with_an_undeclared_name_is_none() {
    assert_eq!(count_of(vec![(A, zero()), (B, cases(vec![(F, vec![Some(Q)])]))], &[A, Q]), Cnt::None);
}

#[test]
fn count_ignores_a_root_whose_argument_is_undeclared() {
    assert_eq!(count_of(vec![(A, cases(vec![(F, vec![Some(Q)]), (Z, vec![])]))], &[A]), one(z()));
}

#[test]
fn count_of_a_sort_with_no_cases_and_no_rest_is_none() {
    assert_eq!(count_of(vec![(A, dead())], &[A]), Cnt::None);
}

#[test]
fn count_of_a_constant_case_is_that_constant() {
    assert_eq!(count_of(vec![(A, zero())], &[A]), one(z()));
}

#[test]
fn count_of_two_constants_is_many() {
    assert_eq!(count_of(vec![(A, cases(vec![(CA, vec![]), (CB, vec![])]))], &[A]), Cnt::Many);
}

#[test]
fn count_reads_the_first_declaration_of_a_name_declared_twice() {
    assert_eq!(count_of(vec![(A, dead()), (A, zero())], &[A]), Cnt::None);
    assert_eq!(count_of(vec![(A, zero()), (A, dead())], &[A]), one(z()));
    assert_eq!(count_of(vec![(A, zero()), (A, cases(vec![(Z, vec![]), (O, vec![])]))], &[A]), one(z()));
}

// Counting: rest.

#[test]
fn count_of_a_rest_alone_is_many() {
    assert_eq!(count_of(vec![(A, rest(vec![], vec![], None))], &[A]), Cnt::Many);
}

#[test]
fn count_of_a_rest_whose_argument_sort_is_dead_is_many() {
    assert_eq!(count_of(vec![(A, rest(vec![], vec![], Some(D))), (D, dead())], &[A]), Cnt::Many);
}

#[test]
fn count_of_a_rest_whose_argument_sort_is_undeclared_is_many() {
    assert_eq!(count_of(vec![(A, rest(vec![], vec![], Some(Q)))], &[A]), Cnt::Many);
}

#[test]
fn count_of_a_rest_with_exclusions_is_many() {
    assert_eq!(count_of(vec![(A, rest(vec![], vec![(CA, 0), (F, 2)], None))], &[A]), Cnt::Many);
}

#[test]
fn count_of_a_rest_with_only_dead_cases_is_many() {
    let defs = vec![(A, rest(vec![(F, vec![Some(D)])], vec![], None)), (D, dead())];
    assert_eq!(count_of(defs, &[A]), Cnt::Many);
}

#[test]
fn count_of_two_rests_is_many() {
    let defs = vec![(A, rest(vec![], vec![(CA, 0)], None)), (B, rest(vec![], vec![(CB, 0)], None))];
    assert_eq!(count_of(defs, &[A, B]), Cnt::Many);
}

#[test]
fn count_of_a_rest_and_a_dead_sort_is_none() {
    assert_eq!(count_of(vec![(A, rest(vec![], vec![], None)), (B, dead())], &[A, B]), Cnt::None);
}

#[test]
fn count_of_a_rest_and_a_one_constant_sort_is_that_constant() {
    let defs = vec![(A, rest(vec![], vec![], None)), (B, cases(vec![(CA, vec![])]))];
    assert_eq!(count_of(defs, &[A, B]), one(c0(CA)));
}

#[test]
fn count_is_none_when_the_rest_excludes_the_only_shared_root() {
    let defs = vec![(A, rest(vec![], vec![(CA, 0)], None)), (B, cases(vec![(CA, vec![])]))];
    assert_eq!(count_of(defs, &[A, B]), Cnt::None);
}

#[test]
fn count_a_case_shadowed_by_another_sorts_exclusion_leaves_one_root() {
    let defs = || vec![(A, rest(vec![], vec![(CB, 0)], None)), (B, cases(vec![(CA, vec![]), (CB, vec![])]))];
    assert_eq!(count_of(defs(), &[A, B]), one(c0(CA)));
    assert_eq!(count_of(defs(), &[B]), Cnt::Many);
}

#[test]
fn count_exclusion_of_another_arity_does_not_refuse() {
    let defs = |n: usize| {
        vec![(A, rest(vec![], vec![(F, n)], None)), (B, cases(vec![(F, vec![Some(ZS)])])), (ZS, zero())]
    };
    assert_eq!(count_of(defs(2), &[A, B]), one(f1(z())));
    assert_eq!(count_of(defs(1), &[A, B]), Cnt::None);
}

#[test]
fn count_case_overrides_the_exclusion_of_the_same_root() {
    let defs = vec![(A, rest(vec![(CA, vec![])], vec![(CA, 0)], None)), (B, cases(vec![(CA, vec![])]))];
    assert_eq!(count_of(defs, &[A, B]), one(c0(CA)));
}

#[test]
fn count_takes_the_rest_argument_sort_for_a_root_accepted_by_rest() {
    let defs = |d: Def| vec![(A, rest(vec![], vec![], Some(D))), (B, cases(vec![(F, vec![None])])), (D, d), (N, nat())];
    assert_eq!(count_of(defs(zero()), &[A, B]), one(f1(z())));
    assert_eq!(count_of(defs(cases(vec![(Z, vec![]), (SU, vec![Some(D)])])), &[A, B]), Cnt::Many);
    assert_eq!(count_of(defs(dead()), &[A, B]), Cnt::None);
    assert_eq!(count_of(defs(rest(vec![], vec![], None)), &[A, B]), Cnt::Many);
}

#[test]
fn count_rest_fills_every_argument_with_its_sort() {
    let defs = vec![
        (A, rest(vec![], vec![], Some(D))),
        (B, cases(vec![(F, vec![None, Some(X)])])),
        (D, zero()),
        (X, cases(vec![(Z, vec![]), (O, vec![])])),
    ];
    assert_eq!(count_of(defs, &[A, B]), one(pf(F, vec![z(), z()])));
}

#[test]
fn count_rest_with_any_term_argument_and_any_term_case_is_many() {
    let defs = vec![(A, rest(vec![], vec![], None)), (B, cases(vec![(F, vec![None])]))];
    assert_eq!(count_of(defs, &[A, B]), Cnt::Many);
}

#[test]
fn count_a_dead_case_is_not_rescued_by_the_same_sorts_rest() {
    let defs = vec![
        (A, rest(vec![(F, vec![Some(D)])], vec![], None)),
        (B, cases(vec![(F, vec![Some(ZS)])])),
        (D, dead()),
        (ZS, zero()),
    ];
    assert_eq!(count_of(defs, &[A, B]), Cnt::None);
}

#[test]
fn count_two_rests_and_a_case_sort_narrow_to_one() {
    let defs = vec![
        (A, rest(vec![], vec![], None)),
        (B, rest(vec![], vec![(CA, 0)], None)),
        (C, cases(vec![(CA, vec![]), (CB, vec![])])),
    ];
    assert_eq!(count_of(defs, &[A, B, C]), one(c0(CB)));
}

// Counting: roots.

#[test]
fn count_the_same_root_through_two_sorts_is_one_root() {
    let defs = vec![(A, cases(vec![(F, vec![Some(X)])])), (B, cases(vec![(F, vec![Some(X)])])), (X, zero())];
    assert_eq!(count_of(defs, &[A, B]), one(f1(z())));
}

#[test]
fn count_the_same_root_through_three_sorts_interleaved_with_dead_roots() {
    let defs = vec![
        (A, cases(vec![(G, vec![Some(D)]), (F, vec![Some(X)])])),
        (B, cases(vec![(F, vec![Some(X)]), (G, vec![Some(D)])])),
        (C, cases(vec![(F, vec![Some(X)])])),
        (X, zero()),
        (D, dead()),
    ];
    assert_eq!(count_of(defs, &[A, B, C]), one(f1(z())));
}

#[test]
fn count_duplicate_root_around_a_second_live_root_is_many() {
    let defs = vec![
        (A, cases(vec![(F, vec![Some(ZS)]), (G, vec![Some(ZS)])])),
        (B, cases(vec![(G, vec![Some(ZS)]), (F, vec![Some(ZS)])])),
        (ZS, zero()),
    ];
    assert_eq!(count_of(defs, &[A, B]), Cnt::Many);
}

#[test]
fn count_two_roots_with_the_same_argument_conjunctions_is_many() {
    let defs = vec![(A, cases(vec![(F, vec![Some(B)]), (G, vec![Some(B)])])), (B, zero())];
    assert_eq!(count_of(defs, &[A]), Cnt::Many);
}

#[test]
fn count_two_sorts_sharing_one_root() {
    let defs = vec![
        (A, cases(vec![(CA, vec![]), (CB, vec![])])),
        (B, cases(vec![(CB, vec![]), (CC, vec![])])),
    ];
    assert_eq!(count_of(defs, &[A, B]), one(c0(CB)));
}

#[test]
fn count_two_sorts_with_disjoint_cases_is_none() {
    let defs = || vec![(A, cases(vec![(CA, vec![])])), (B, cases(vec![(CB, vec![])]))];
    assert_eq!(count_of(defs(), &[A, B]), Cnt::None);
    assert_eq!(count_of(defs(), &[A]), one(c0(CA)));
    assert_eq!(count_of(defs(), &[B]), one(c0(CB)));
}

#[test]
fn count_same_symbol_at_different_arities_are_two_roots() {
    let defs = vec![(A, cases(vec![(F, vec![Some(ZS)]), (F, vec![Some(ZS), Some(ZS)])])), (ZS, zero())];
    assert_eq!(count_of(defs, &[A]), Cnt::Many);
}

#[test]
fn count_same_symbol_no_argument_and_one_argument() {
    let defs = |k: Name| vec![(A, cases(vec![(F, vec![]), (F, vec![Some(k)])])), (ZS, zero()), (D, dead())];
    assert_eq!(count_of(defs(ZS), &[A]), Cnt::Many);
    assert_eq!(count_of(defs(D), &[A]), one(c0(F)));
}

#[test]
fn count_same_symbol_different_arity_one_dead() {
    let defs = vec![
        (A, cases(vec![(F, vec![Some(D)]), (F, vec![Some(ZS), Some(ZS)])])),
        (D, dead()),
        (ZS, zero()),
    ];
    assert_eq!(count_of(defs, &[A]), one(pf(F, vec![z(), z()])));
}

#[test]
fn count_same_symbol_different_arity_across_sorts_is_none() {
    let defs = vec![(A, cases(vec![(F, vec![None])])), (B, cases(vec![(F, vec![None, None])]))];
    assert_eq!(count_of(defs, &[A, B]), Cnt::None);
}

#[test]
fn count_reads_the_first_of_duplicate_cases() {
    let defs = |first: Name, second: Name| {
        vec![
            (A, cases(vec![(F, vec![Some(first)]), (F, vec![Some(second)])])),
            (D, dead()),
            (ZS, zero()),
            (N, nat()),
        ]
    };
    assert_eq!(count_of(defs(D, ZS), &[A]), Cnt::None);
    assert_eq!(count_of(defs(ZS, D), &[A]), one(f1(z())));
    assert_eq!(count_of(defs(ZS, N), &[A]), one(f1(z())));
    assert_eq!(count_of(defs(N, ZS), &[A]), Cnt::Many);
}

#[test]
fn count_duplicate_constant_case_is_one_root() {
    assert_eq!(count_of(vec![(A, cases(vec![(Z, vec![]), (Z, vec![])]))], &[A]), one(z()));
}

#[test]
fn count_joins_the_argument_sorts_of_a_shared_root() {
    let defs = || {
        vec![
            (A, cases(vec![(F, vec![Some(X)])])),
            (B, cases(vec![(F, vec![Some(Y)])])),
            (X, cases(vec![(CA, vec![]), (CB, vec![])])),
            (Y, cases(vec![(CB, vec![]), (CC, vec![])])),
        ]
    };
    assert_eq!(count_of(defs(), &[A, B]), one(f1(c0(CB))));
    assert_eq!(count_of(defs(), &[A]), Cnt::Many);
    assert_eq!(count_of(defs(), &[B]), Cnt::Many);
}

#[test]
fn count_keeps_the_arguments_in_order() {
    let defs = vec![
        (A, cases(vec![(F, vec![Some(X), Some(Y), Some(X)])])),
        (X, cases(vec![(CA, vec![])])),
        (Y, cases(vec![(CB, vec![])])),
    ];
    assert_eq!(count_of(defs, &[A]), one(pf(F, vec![c0(CA), c0(CB), c0(CA)])));
}

// Counting: dead roots, roots with many members, any term.

#[test]
fn count_ignores_a_root_with_a_dead_argument() {
    let defs = vec![
        (A, cases(vec![(F, vec![Some(ZS), Some(D)]), (G, vec![Some(ZS), Some(ZS)])])),
        (D, dead()),
        (ZS, zero()),
    ];
    assert_eq!(count_of(defs, &[A]), one(pf(G, vec![z(), z()])));
    let alts = vec![(F, vec![Some(D)]), (G, vec![Some(D)]), (H, vec![Some(ZS)])];
    let mut rev = alts.clone();
    rev.reverse();
    for a in [alts, rev] {
        assert_eq!(count_of(vec![(A, cases(a)), (D, dead()), (ZS, zero())], &[A]), one(pf(H, vec![z()])));
    }
}

#[test]
fn count_one_live_root_whose_argument_is_many_is_many() {
    assert_eq!(count_of(vec![(A, cases(vec![(F, vec![Some(N)])])), (N, nat())], &[A]), Cnt::Many);
}

#[test]
fn count_one_unique_root_and_one_many_root_is_many() {
    let defs = vec![(A, cases(vec![(F, vec![Some(ZS)]), (G, vec![Some(N)])])), (ZS, zero()), (N, nat())];
    assert_eq!(count_of(defs, &[A]), Cnt::Many);
}

#[test]
fn count_dead_argument_beside_a_many_argument_is_none() {
    let defs = vec![(A, cases(vec![(F, vec![Some(D), Some(N)])])), (D, dead()), (N, nat())];
    assert_eq!(count_of(defs, &[A]), Cnt::None);
}

#[test]
fn count_of_a_case_with_an_any_term_argument_is_many() {
    for kids in [vec![None], vec![None, Some(ZS)], vec![Some(ZS), None, Some(ZS)]] {
        assert_eq!(count_of(vec![(A, cases(vec![(F, kids)])), (ZS, zero())], &[A]), Cnt::Many);
    }
}

#[test]
fn count_any_term_in_one_sort_and_a_sort_in_another() {
    let defs = |d: Def| vec![(A, cases(vec![(F, vec![None])])), (B, cases(vec![(F, vec![Some(D)])])), (D, d)];
    assert_eq!(count_of(defs(zero()), &[A, B]), one(f1(z())));
    assert_eq!(count_of(defs(dead()), &[A, B]), Cnt::None);
    assert_eq!(count_of(defs(cases(vec![(Z, vec![]), (SU, vec![Some(D)])])), &[A, B]), Cnt::Many);
}

#[test]
fn count_any_term_argument_beside_a_dead_argument_is_none() {
    assert_eq!(count_of(vec![(A, cases(vec![(F, vec![None, Some(D)])])), (D, dead())], &[A]), Cnt::None);
}

#[test]
fn count_of_a_finite_sort_with_two_members_differing_deep_is_many() {
    let defs = vec![
        (A, cases(vec![(F, vec![Some(B)])])),
        (B, cases(vec![(G, vec![Some(C)])])),
        (C, cases(vec![(CA, vec![]), (CB, vec![])])),
    ];
    assert_eq!(count_of(defs, &[A]), Cnt::Many);
}

// Counting: recursion and cycles.

#[test]
fn count_of_recursion_without_a_base_case_is_none() {
    assert_eq!(count_of(vec![(A, cases(vec![(F, vec![Some(A)])]))], &[A]), Cnt::None);
    assert_eq!(count_of(vec![(A, cases(vec![(F, vec![Some(A), Some(A)])]))], &[A]), Cnt::None);
}

#[test]
fn count_of_a_nonrecursive_chain_is_its_one_member() {
    assert_eq!(count_of(vec![(A, cases(vec![(F, vec![Some(B)])])), (B, zero())], &[A]), one(f1(z())));
}

#[test]
fn count_of_recursion_with_a_base_and_a_step_is_many() {
    assert_eq!(count_of(vec![(N, nat())], &[N]), Cnt::Many);
}

#[test]
fn count_of_recursion_with_a_rest_as_base_is_many() {
    assert_eq!(count_of(vec![(A, rest(vec![(F, vec![Some(A)])], vec![], None))], &[A]), Cnt::Many);
}

#[test]
fn count_of_mutual_recursion_without_a_base_is_none() {
    let defs = || vec![(A, cases(vec![(F, vec![Some(B)])])), (B, cases(vec![(G, vec![Some(A)])]))];
    assert_eq!(count_of(defs(), &[A]), Cnt::None);
    assert_eq!(count_of(defs(), &[B]), Cnt::None);
}

#[test]
fn count_of_mutual_recursion_with_a_base_is_many() {
    let defs = || vec![(A, cases(vec![(F, vec![Some(B)])])), (B, cases(vec![(G, vec![Some(A)]), (Z, vec![])]))];
    assert_eq!(count_of(defs(), &[A]), Cnt::Many);
    assert_eq!(count_of(defs(), &[B]), Cnt::Many);
}

#[test]
fn count_of_a_self_cycle_with_the_base_elsewhere_is_one() {
    let defs = || {
        vec![
            (A, cases(vec![(F, vec![Some(A)]), (Z, vec![])])),
            (B, cases(vec![(F, vec![Some(C)])])),
            (C, zero()),
        ]
    };
    assert_eq!(count_of(defs(), &[A, B]), one(f1(z())));
    assert_eq!(count_of(defs(), &[A]), Cnt::Many);
}

#[test]
fn count_of_a_cycle_through_conjunctions() {
    assert_eq!(count_of(cycle(&[]), &[A, B]), Cnt::None);
    assert_eq!(count_of(cycle(&[A, C]), &[A, B]), Cnt::Many);
    assert_eq!(count_of(cycle(&[A]), &[A, B]), Cnt::None);
}

#[test]
fn count_of_a_conjunction_dead_although_each_sort_is_many() {
    let defs = || {
        vec![
            (A, cases(vec![(Z, vec![]), (SU, vec![Some(A)])])),
            (B, cases(vec![(O, vec![]), (SU, vec![Some(B)])])),
        ]
    };
    assert_eq!(count_of(defs(), &[A, B]), Cnt::None);
    assert_eq!(count_of(defs(), &[A]), Cnt::Many);
}

#[test]
fn count_of_even_odd_and_nat() {
    assert_eq!(count_of(nat_table(), &[E, OD]), Cnt::None);
    assert_eq!(count_of(nat_table(), &[E, N]), Cnt::Many);
    assert_eq!(count_of(nat_table(), &[OD, N]), Cnt::Many);
}

#[test]
fn count_of_an_interval_of_naturals() {
    let defs = || {
        vec![
            (A, zero()),
            (B, cases(vec![(Z, vec![]), (SU, vec![Some(A)])])),
            (C, cases(vec![(Z, vec![]), (SU, vec![Some(B)])])),
            (X, cases(vec![(SU, vec![Some(N)])])),
            (N, nat()),
        ]
    };
    // At most one and at least one: one.
    assert_eq!(count_of(defs(), &[B, X]), one(pf(SU, vec![z()])));
    // At most two and at least one: one and two.
    assert_eq!(count_of(defs(), &[C, X]), Cnt::Many);
}

#[test]
fn count_of_a_conjunction_whose_root_leads_back_to_itself_is_none() {
    let defs = vec![(A, cases(vec![(F, vec![Some(B)])])), (B, cases(vec![(F, vec![Some(A)]), (Z, vec![])]))];
    assert_eq!(count_of(defs, &[A, B]), Cnt::None);
}

// Counting: order of rounds, depth, sharing.

/// `f` applied `n` times to `z`, as a node.
fn tower(s: &mut Store, n: usize) -> TermId {
    let f = s.alloc(Node::Sym(F));
    let mut t = s.alloc(Node::Sym(Z));
    for _ in 0..n {
        t = s.alloc(Node::App(f, t));
    }
    t
}

#[test]
fn count_chain_declared_base_last_and_base_first() {
    for base_first in [false, true] {
        let mut f = fx(chain(2000, true, base_first));
        let t = tower(&mut f.s, 2000);
        assert!(f.counts_one(&[link(0)], t));
        assert_eq!(count_of(chain(2000, false, base_first), &[link(0)]), Cnt::None);
    }
}

/// `R = h(S0, ..., Sk)`, `Si = f(S(i+1))` and `Sk` as given: the links are
/// reached in the order that settles one of them in each round.
fn comb(k: usize, last: Def) -> Vec<(Name, Def)> {
    let mut defs = vec![(A, cases(vec![(H, (0..=k).map(|i| Some(link(i))).collect())]))];
    defs.extend((0..k).map(|i| (link(i), cases(vec![(F, vec![Some(link(i + 1))])]))));
    defs.push((link(k), last));
    defs
}

#[test]
fn count_comb_resolves_against_graph_order() {
    let k = 40;
    let mut f = fx(comb(k, zero()));
    let mut t = f.s.alloc(Node::Sym(H));
    for i in 0..=k {
        let a = tower(&mut f.s, k - i);
        t = f.s.alloc(Node::App(t, a));
    }
    assert!(f.counts_one(&[A], t));
}

#[test]
fn count_comb_with_a_many_tail_is_many_and_with_a_dead_tail_is_none() {
    let many = cases(vec![(Z, vec![]), (O, vec![])]);
    assert_eq!(count_of(comb(40, many), &[A]), Cnt::Many);
    assert_eq!(count_of(comb(40, dead()), &[A]), Cnt::None);
}

#[test]
fn count_two_argument_ladder() {
    let mut f = fx(ladder(100, true, true));
    let g = f.s.alloc(Node::Sym(F));
    let mut t = f.s.alloc(Node::Sym(Z));
    for _ in 0..100 {
        let l = f.s.alloc(Node::App(g, t));
        t = f.s.alloc(Node::App(l, t));
    }
    assert!(f.counts_one(&[link(0)], t));
    assert_eq!(count_of(ladder(100, true, false), &[link(0)]), Cnt::None);
    assert_eq!(count_of(ladder(100, false, true), &[link(0)]), Cnt::None);
}

#[test]
fn count_member_with_an_exponential_tree_is_a_linear_dag() {
    let n = 64;
    let mut defs = vec![(link(0), zero())];
    defs.extend((1..=n).map(|i| (link(i), cases(vec![(F, vec![Some(link(i - 1)), Some(link(i - 1))])]))));
    let mut f = fx(defs);
    let g = f.s.alloc(Node::Sym(F));
    let mut t = f.s.alloc(Node::Sym(Z));
    for _ in 0..n {
        let l = f.s.alloc(Node::App(g, t));
        t = f.s.alloc(Node::App(l, t));
    }
    let c = f.conj(&[link(n)]);
    let (decls, names) = (f.decls, f.names);
    let (r, ticks) = spent(&mut f.s, |s| count(s, decls, names, c));
    match r {
        Count::One(m) => assert!(f.s.same(m, t)),
        _ => panic!("one member"),
    }
    assert!(ticks <= 200_000, "{} ticks", ticks);
}

#[test]
fn count_of_a_case_with_100000_arguments() {
    let table = |last: Name| {
        let mut kids = vec![Some(ZS); LONG];
        kids[LONG - 1] = Some(last);
        vec![(A, cases(vec![(F, kids)])), (ZS, zero()), (D, dead()), (N, nat())]
    };
    let mut f = fx(table(ZS));
    let (r, ticks) = f.count_ticks(&[A]);
    assert!(matches!(r, Count::One(_)));
    assert!(ticks <= 80 * LONG as u64, "{} ticks", ticks);
    assert!(matches!(fx(table(D)).count_node(&[A]), Count::None));
    assert!(matches!(fx(table(N)).count_node(&[A]), Count::Many));
}

#[test]
fn count_of_a_conjunction_of_many_sorts() {
    let c: Vec<Name> = (0..300).map(link).collect();
    let many: Vec<(Name, Def)> =
        (0..300).map(|i| (link(i), cases(vec![(Z, vec![]), (SU, vec![Some(link(i))])]))).collect();
    assert_eq!(count_of(many, &c), Cnt::Many);
    let mut f = fx((0..300).map(|i| (link(i), zero())).collect());
    let (r, ticks) = f.count_ticks(&c);
    match r {
        Count::One(m) => assert_eq!(get(&mut f.s, m), z().tree()),
        _ => panic!("one member"),
    }
    // Each of the 300 sorts gives the root once, and each time the step of
    // each of the 300 sorts is taken, which looks its declaration up among
    // 300. The copies of the root are not compared with each other.
    assert!(ticks <= 2 * 300 * 300 * 300, "{} ticks", ticks);
}

#[test]
fn count_of_a_sort_with_many_dead_cases_and_one_live() {
    for live_first in [false, true] {
        let mut cs: Vec<Case> = (0..2000).map(|i| (1000 + i as u32, vec![Some(D)])).collect();
        if live_first {
            cs.insert(0, (H, vec![Some(ZS)]));
        } else {
            cs.push((H, vec![Some(ZS)]));
        }
        let mut f = fx(vec![(A, cases(cs)), (D, dead()), (ZS, zero())]);
        let (r, ticks) = f.count_ticks(&[A]);
        match r {
            Count::One(m) => assert_eq!(get(&mut f.s, m), pf(H, vec![z()]).tree()),
            _ => panic!("one member"),
        }
        assert!(ticks <= 2000 * 2000 * 4, "{} ticks", ticks);
    }
}

// Counting: state and contract.

#[test]
fn count_leaves_the_stack_empty() {
    let mut f = fx(nat_table());
    assert_eq!(f.count(&[E, OD]), Cnt::None);
    assert!(f.s.pop().is_none());
    assert_eq!(f.count(&[E, N]), Cnt::Many);
    assert!(f.s.pop().is_none());
    let mut f = fx(vec![(A, cases(vec![(F, vec![Some(B)])])), (B, zero())]);
    assert_eq!(f.count(&[A]), one(f1(z())));
    assert!(f.s.pop().is_none());
}

#[test]
fn count_gives_the_same_answer_when_called_again() {
    let mut defs = nat_table();
    defs.push((A, cases(vec![(SU, vec![Some(B)])])));
    defs.push((B, zero()));
    let mut f = fx(defs);
    let t = put(&mut f.s, &pf(SU, vec![z()]).tree());
    for _ in 0..3 {
        assert_eq!(f.count(&[E, OD]), Cnt::None);
        assert!(f.counts_one(&[A], t));
        assert_eq!(f.count(&[E, N]), Cnt::Many);
        assert!(f.counts_one(&[A, N], t));
        assert_eq!(f.count(&[D]), Cnt::None);
    }
}

#[test]
fn count_after_live_and_live_after_count_agree() {
    let mut defs = nat_table();
    defs.push((A, zero()));
    let mut f = fx(defs);
    for c in subsets(&f.order.clone()) {
        let l = f.live(&c);
        let n = f.count(&c);
        assert_eq!(l, n != Cnt::None, "{:?}", c);
        assert_eq!(f.live(&c), l, "{:?}", c);
    }
}

#[test]
fn count_does_not_see_tables_of_an_earlier_call() {
    let mut defs = nat_table();
    defs.push((A, zero()));
    let mut f = fx(defs);
    let n = f.s.alloc(Node::Sym(N));
    let zn = f.s.alloc(Node::Sym(Z));
    assert!(member(&mut f.s, f.decls, n, zn));
    let list = put_names(&mut f.s, &[E, OD, D, A]);
    conj_of(&mut f.s, f.names, list);
    assert_eq!(f.count(&[E, N]), Cnt::Many);
    assert_eq!(f.count(&[A]), one(z()));
    assert_eq!(f.count(&[E, OD]), Cnt::None);
    assert_eq!(f.count(&[D]), Cnt::None);
    assert_eq!(f.count(&[]), Cnt::Many);
}

#[test]
fn count_does_not_reuse_a_member_found_under_other_declarations() {
    let mut s = Store::new();
    let d1 = put_sorts(&mut s, &Sorts::new(vec![(A, zero())]));
    let d2 = put_sorts(&mut s, &Sorts::new(vec![(A, cases(vec![(Z, vec![]), (O, vec![])]))]));
    let d3 = put_sorts(&mut s, &Sorts::new(vec![(A, dead())]));
    let names = put_names(&mut s, &[A]);
    let c = put_names(&mut s, &[A]);
    assert!(matches!(count(&mut s, d1, names, c), Count::One(_)));
    assert!(matches!(count(&mut s, d2, names, c), Count::Many));
    assert!(matches!(count(&mut s, d3, names, c), Count::None));
    assert!(matches!(count(&mut s, d1, names, c), Count::One(_)));
}

#[test]
fn count_one_is_a_member_of_every_sort_of_the_conjunction() {
    let mut r = Rng(5);
    let mut seen = 0;
    for _ in 0..300 {
        let mut f = fx(random_table(&mut r));
        for c in subsets(&f.order.clone()) {
            if let Count::One(t) = f.count_node(&c) {
                seen += 1;
                for n in &c {
                    let n = f.s.alloc(Node::Sym(*n));
                    assert!(member(&mut f.s, f.decls, n, t), "{:?} under {:?}", c, f.ss.defs);
                }
            }
        }
    }
    assert!(seen > 50, "only {} conjunctions with one member", seen);
}

#[test]
fn count_of_every_subset_agrees_with_the_specification_on_tables_of_odd_declarations() {
    check_all_counts(vec![
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
    check_all_counts(vec![
        (A, cases(vec![(Z, vec![]), (F, vec![Some(B)])])),
        (B, cases(vec![(F, vec![Some(C)]), (G, vec![Some(D)])])),
        (C, cases(vec![(Z, vec![])])),
        (X, rest(vec![], vec![(Z, 0)], Some(C))),
        (Y, cases(vec![(F, vec![None]), (Z, vec![])])),
        (D, dead()),
    ]);
}

#[test]
fn count_agrees_with_the_specification_on_random_small_tables() {
    let mut r = Rng(7);
    for _ in 0..400 {
        check_all_counts(random_table(&mut r));
    }
}

#[test]
fn count_agrees_with_small_members_enumerated() {
    let mut r = Rng(11);
    let terms = ground(1);
    for _ in 0..150 {
        let mut f = fx(random_table(&mut r));
        for c in subsets(&f.order.clone()) {
            let members: Vec<&P> = terms.iter().filter(|t| c.iter().all(|n| f.ss.member(*n, t))).collect();
            match f.count(&c) {
                Cnt::None => assert!(members.is_empty(), "{:?} has a member under {:?}", c, f.ss.defs),
                Cnt::One(t) => {
                    assert!(members.iter().all(|m| m.tree() == t), "{:?} has another member under {:?}", c, f.ss.defs)
                }
                Cnt::Many => {}
            }
            if members.len() >= 2 {
                assert_eq!(f.count(&c), Cnt::Many, "{:?} under {:?}", c, f.ss.defs);
            }
        }
    }
}

#[test]
fn count_with_sort_names_that_are_also_symbols() {
    // The sort `A` has the constant `A` and `f(B)`, and `B` the constant `A`.
    let defs = || vec![(A, cases(vec![(A, vec![]), (F, vec![Some(B)])])), (B, cases(vec![(A, vec![])]))];
    assert_eq!(count_of(defs(), &[A]), Cnt::Many);
    assert_eq!(count_of(defs(), &[B]), one(c0(A)));
    assert_eq!(count_of(defs(), &[A, B]), one(c0(A)));
}

#[test]
fn count_ticks_are_at_most_quadratic_in_the_chain_and_the_comb_length() {
    for base_first in [false, true] {
        let mut last = 0;
        for n in [250usize, 500, 1000] {
            let mut f = fx(chain(n, true, base_first));
            let (r, ticks) = f.count_ticks(&[link(0)]);
            assert!(matches!(r, Count::One(_)));
            let n = n as u64;
            assert!(ticks <= 60 * n * n + 1000, "chain of {}: {} ticks", n, ticks);
            assert!(ticks > last);
            last = ticks;
        }
    }
    for k in [50usize, 100, 200] {
        let mut f = fx(comb(k, zero()));
        let (r, ticks) = f.count_ticks(&[A]);
        assert!(matches!(r, Count::One(_)));
        let k = k as u64;
        assert!(ticks <= 60 * k * k + 2000, "comb of {}: {} ticks", k, ticks);
    }
}

#[test]
fn count_ticks_grow_with_the_reachable_set_not_the_table() {
    let table = |extra: usize| {
        let mut defs = vec![
            (A, cases(vec![(F, vec![Some(B)])])),
            (B, cases(vec![(F, vec![Some(C)])])),
            (C, zero()),
        ];
        defs.extend((0..extra).map(|i| (link(i), cases(vec![(F, vec![Some(link(i))])]))));
        defs
    };
    let ticks = |extra: usize| fx(table(extra)).count_ticks(&[A]).1;
    let (t0, t1, t2) = (ticks(0), ticks(1000), ticks(2000));
    assert!(t1 - t0 <= 100 * 1000, "{} then {}", t0, t1);
    assert!(t2 - t1 <= 100 * 1000, "{} then {}", t1, t2);
}
