//! Whether a conjunction of sorts has a member, on the store, against the
//! specification (`live` of `lean/RwLog/Sorts/Empty.lean`).

mod common;

use common::sorts::*;
use common::spent;
use rwlog_core::sorts::{conj_of, live, member};
use rwlog_core::store::{Node, Store, TermId};
use std::collections::BTreeSet;

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

const LONG: usize = 400_000;

#[test]
fn live_of_a_case_with_400000_arguments() {
    let mut f = fx(vec![(A, cases(vec![(F, vec![Some(ZS); LONG])])), (ZS, zero())]);
    let (r, ticks) = f.ticks(&[A]);
    assert!(r);
    assert!(ticks <= 60 * LONG as u64, "{} ticks", ticks);
}

#[test]
fn live_of_400000_argument_case_with_the_last_argument_dead() {
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
