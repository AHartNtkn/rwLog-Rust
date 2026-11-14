//! Pushing a sort down a pattern (`sorts::push_sort`) against `push` of the
//! specification, as the reference on trees has it.

mod common;

use std::collections::BTreeSet;

use common::sorts::*;
use common::{get_list, put, spent, T};
use rwlog_core::sorts::{member, push_sort};
use rwlog_core::store::{Node, Store, Tbl, TermId};

const Z: u32 = 0;
const K: u32 = 1;
const Q: u32 = 2;
const S: u32 = 3;
const PAIR: u32 = 4;

const NAT: Name = 10;
const POS: Name = 11;
const ANY: Name = 12;
const ZK: Name = 13;
const KK: Name = 14;
const NOK: Name = 15;
const NIL: Name = 17;
const NOPAIR: Name = 18;
const TWICE: Name = 19;
const MIX: Name = 20;
const UNDECLARED: Name = 99;

/// The sorts of `sorts.rs`, and `MIX`, whose cases give their arguments
/// different sorts, any term, and a sort with no declaration.
fn sorts() -> Sorts {
    let def = |cases: Vec<(u32, Vec<Option<Name>>)>, rest| Def { cases, rest };
    Sorts::new(vec![
        (NAT, def(vec![(Z, vec![]), (S, vec![Some(NAT)])], None)),
        (POS, def(vec![(S, vec![None])], None)),
        (ANY, def(vec![], Some((vec![], None)))),
        (ZK, def(vec![(Z, vec![]), (K, vec![]), (PAIR, vec![Some(ZK), Some(ZK)])], None)),
        (KK, def(vec![(K, vec![]), (PAIR, vec![Some(ZK), Some(ZK)])], None)),
        (NOK, def(vec![], Some((vec![(K, 0)], Some(NOK))))),
        (NIL, def(vec![], None)),
        (NOPAIR, def(vec![(S, vec![Some(NAT)])], Some((vec![(PAIR, 2), (K, 0)], None)))),
        (TWICE, def(vec![(S, vec![Some(NIL)]), (S, vec![None]), (S, vec![None, None])], None)),
        (
            MIX,
            def(
                vec![
                    (PAIR, vec![Some(NOK), Some(ZK)]),
                    (S, vec![None, Some(NAT)]),
                    (Q, vec![Some(UNDECLARED)]),
                ],
                None,
            ),
        ),
        // A second declaration of a name is not read.
        (NAT, def(vec![(K, vec![])], None)),
    ])
}

const NAMES: [Name; 11] = [NAT, POS, ANY, ZK, KK, NOK, NIL, NOPAIR, TWICE, MIX, UNDECLARED];

type Atoms = BTreeSet<(usize, Name)>;

fn c(f: u32) -> P {
    pf(f, vec![])
}

fn atoms(list: &[(usize, Name)]) -> Option<Atoms> {
    Some(list.iter().copied().collect())
}

/// The number of the variable a tree is.
fn var_of(t: &T) -> usize {
    match t {
        T::V(n) => *n as usize,
        other => panic!("an atom's first part is not a variable: {:?}", other),
    }
}

/// The atoms of a list of `App(variable, sort)`.
fn read_atoms(s: &mut Store, list: TermId) -> Atoms {
    get_list(s, list)
        .iter()
        .map(|a| match a {
            T::A(x, n) => match **n {
                T::S(m) => (var_of(x), m),
                ref other => panic!("an atom's second part is not a sort: {:?}", other),
            },
            other => panic!("not an atom: {:?}", other),
        })
        .collect()
}

/// `push_sort` on a new store, with the stack checked empty afterwards.
fn run(p: &P, name: Name) -> Option<Atoms> {
    let mut s = Store::new();
    let table = put_sorts(&mut s, &sorts());
    let node = s.alloc(Node::Sym(name));
    let id = put_pat(&mut s, p);
    let got = push_sort(&mut s, table, node, id);
    assert!(s.pop().is_none(), "the stack is not empty after {:?} : {}", p, name);
    got.map(|l| read_atoms(&mut s, l))
}

// A variable alone.

#[test]
fn a_variable_alone_gets_the_sort() {
    assert_eq!(run(&pv(0), NAT), atoms(&[(0, NAT)]));
}

#[test]
fn left_and_right_variables_are_variables() {
    assert_eq!(run(&pv(1), NAT), atoms(&[(1, NAT)]));
    assert_eq!(run(&pv(2), NAT), atoms(&[(2, NAT)]));
    assert_eq!(run(&pv(5), ZK), atoms(&[(5, ZK)]));
}

#[test]
fn a_variable_alone_gets_a_sort_with_no_declaration() {
    assert_eq!(run(&pv(0), UNDECLARED), atoms(&[(0, UNDECLARED)]));
}

#[test]
fn a_variable_alone_gets_a_sort_with_no_member() {
    assert_eq!(run(&pv(0), NIL), atoms(&[(0, NIL)]));
}

#[test]
fn a_variable_alone_gets_the_declared_sort_of_every_term() {
    assert_eq!(run(&pv(0), ANY), atoms(&[(0, ANY)]));
}

// Ground patterns.

#[test]
fn a_ground_pattern_has_no_atoms_exactly_when_it_is_a_member() {
    let ss = sorts();
    let mut rng = Rng(11);
    let (mut yes, mut no) = (0, 0);
    for round in 0..2000 {
        let t = random_pat(&mut rng, 4, 0);
        let name = NAMES[rng.next(NAMES.len())];
        let want = if ss.member(name, &t) { atoms(&[]) } else { None };
        let got = run(&t, name);
        assert_eq!(got, want, "round {}: {:?} : {}", round, t, name);
        if got.is_some() {
            yes += 1
        } else {
            no += 1
        }
    }
    assert!(yes > 300 && no > 300, "{} in, {} out", yes, no);
}

#[test]
fn a_constant_of_the_sort_has_no_atoms() {
    assert_eq!(run(&c(Z), NAT), atoms(&[]));
}

#[test]
fn a_constant_fails_in_a_sort_with_no_member_or_no_declaration() {
    assert_eq!(run(&c(Z), NIL), None);
    assert_eq!(run(&c(Z), UNDECLARED), None);
}

#[test]
fn a_second_declaration_of_a_name_is_not_read() {
    assert_eq!(run(&c(K), NAT), None);
    assert_eq!(run(&pf(S, vec![c(K)]), NAT), None);
}

#[test]
fn a_rest_accepts_a_constant_it_does_not_exclude() {
    assert_eq!(run(&c(Q), ANY), atoms(&[]));
    assert_eq!(run(&c(Q), NOK), atoms(&[]));
    assert_eq!(run(&c(K), NOK), None);
    assert_eq!(run(&c(K), NOPAIR), None);
}

// Arguments that may be any term.

#[test]
fn a_variable_where_any_term_may_be_gets_no_sort() {
    assert_eq!(run(&pf(S, vec![pv(0)]), POS), atoms(&[]));
}

#[test]
fn nothing_is_looked_at_where_any_term_may_be() {
    assert_eq!(run(&pf(S, vec![pf(PAIR, vec![c(Q), pv(0)])]), POS), atoms(&[]));
}

#[test]
fn a_rest_of_any_term_gives_no_sort() {
    assert_eq!(run(&pf(Q, vec![pv(0), pv(1)]), ANY), atoms(&[]));
    assert_eq!(run(&pf(S, vec![pv(0), pv(1)]), TWICE), atoms(&[]));
}

#[test]
fn a_sort_keeps_its_place_beside_any_term() {
    assert_eq!(run(&pf(S, vec![pv(0), pv(1)]), MIX), atoms(&[(1, NAT)]));
}

// Atoms from cases and rests.

#[test]
fn a_case_gives_its_argument_its_sort() {
    assert_eq!(run(&pf(S, vec![pv(0)]), NAT), atoms(&[(0, NAT)]));
    assert_eq!(run(&pf(S, vec![pf(S, vec![pf(S, vec![pv(0)])])]), NAT), atoms(&[(0, NAT)]));
}

#[test]
fn the_sort_of_an_atom_is_the_sort_of_the_argument() {
    assert_eq!(run(&pf(PAIR, vec![pv(0), pv(1)]), ZK), atoms(&[(0, ZK), (1, ZK)]));
    assert_eq!(run(&pf(PAIR, vec![pv(0), pv(1)]), KK), atoms(&[(0, ZK), (1, ZK)]));
}

#[test]
fn a_rest_gives_every_argument_its_sort() {
    assert_eq!(run(&pf(Q, vec![pv(0), pv(1), pv(0)]), NOK), atoms(&[(0, NOK), (1, NOK)]));
}

#[test]
fn an_exclusion_is_of_a_symbol_with_a_number_of_arguments() {
    assert_eq!(run(&pf(K, vec![pv(0)]), NOK), atoms(&[(0, NOK)]));
    assert_eq!(run(&pf(PAIR, vec![pv(0), pv(1)]), NOPAIR), None);
    assert_eq!(run(&pf(PAIR, vec![pv(0)]), NOPAIR), atoms(&[]));
    assert_eq!(run(&pf(PAIR, vec![pv(0), pv(1), pv(2)]), NOPAIR), atoms(&[]));
}

#[test]
fn a_case_is_read_before_the_rest() {
    assert_eq!(run(&pf(S, vec![pv(0)]), NOPAIR), atoms(&[(0, NAT)]));
    assert_eq!(run(&pf(S, vec![pv(0), pv(1)]), NOPAIR), atoms(&[]));
    assert_eq!(run(&pf(S, vec![c(K)]), NOPAIR), None);
}

#[test]
fn the_first_case_of_a_root_is_the_one_read() {
    assert_eq!(run(&pf(S, vec![pv(0)]), TWICE), atoms(&[(0, NIL)]));
    assert_eq!(run(&pf(S, vec![c(Z)]), TWICE), None);
}

#[test]
fn an_argument_sort_with_no_declaration_is_an_atom_on_a_variable_only() {
    assert_eq!(run(&pf(Q, vec![pv(0)]), MIX), atoms(&[(0, UNDECLARED)]));
    assert_eq!(run(&pf(Q, vec![c(Z)]), MIX), None);
}

// The same variable or subterm several times.

#[test]
fn a_variable_twice_under_one_sort_is_one_atom() {
    assert_eq!(run(&pf(PAIR, vec![pv(0), pv(0)]), ZK), atoms(&[(0, ZK)]));
}

#[test]
fn a_variable_under_two_sorts_is_two_atoms() {
    assert_eq!(run(&pf(PAIR, vec![pv(0), pv(0)]), MIX), atoms(&[(0, NOK), (0, ZK)]));
}

#[test]
fn a_shared_subterm_under_one_sort_keeps_its_atoms() {
    let t = pf(PAIR, vec![pv(0), pv(1)]);
    assert_eq!(run(&pf(PAIR, vec![t.clone(), t]), ZK), atoms(&[(0, ZK), (1, ZK)]));
}

#[test]
fn a_shared_subterm_under_two_sorts_is_read_for_each() {
    let t = pf(PAIR, vec![pv(0), pv(1)]);
    assert_eq!(
        run(&pf(PAIR, vec![t.clone(), t]), MIX),
        atoms(&[(0, NOK), (1, NOK), (0, ZK), (1, ZK)])
    );
}

#[test]
fn a_shared_ground_subterm_must_be_in_both_sorts() {
    assert_eq!(run(&pf(PAIR, vec![c(Z), c(Z)]), MIX), atoms(&[]));
    assert_eq!(run(&pf(PAIR, vec![c(K), c(K)]), MIX), None);
}

#[test]
fn a_variable_under_different_parents_is_found_under_each() {
    let t = pf(PAIR, vec![pf(PAIR, vec![pv(0), pv(1)]), pf(PAIR, vec![pv(1), pv(0)])]);
    assert_eq!(run(&t, ZK), atoms(&[(0, ZK), (1, ZK)]));
}

// Failure.

#[test]
fn a_variable_under_a_rejected_symbol_fails() {
    assert_eq!(run(&pf(Q, vec![pv(0)]), NAT), None);
    assert_eq!(run(&pf(S, vec![pf(Q, vec![pv(0)])]), NAT), None);
}

#[test]
fn a_failure_before_or_after_an_atom_is_a_failure() {
    assert_eq!(run(&pf(PAIR, vec![pv(0), c(Q)]), ZK), None);
    assert_eq!(run(&pf(PAIR, vec![c(Q), pv(0)]), ZK), None);
}

#[test]
fn a_failure_between_waiting_arguments_empties_the_stack() {
    // `run` checks the stack.
    assert_eq!(run(&pf(Q, vec![pv(0), c(K), pv(1)]), NOK), None);
}

#[test]
fn one_argument_failing_fails_the_pattern() {
    assert_eq!(run(&pf(PAIR, vec![pv(0), pf(S, vec![pv(1)])]), MIX), None);
}

#[test]
fn a_wrong_number_of_arguments_fails_without_a_rest() {
    assert_eq!(run(&pf(S, vec![pv(0), pv(1)]), NAT), None);
    assert_eq!(run(&pf(Z, vec![pv(0)]), NAT), None);
    assert_eq!(run(&c(S), NAT), None);
    assert_eq!(run(&pf(PAIR, vec![pv(0)]), ZK), None);
    assert_eq!(run(&pf(PAIR, vec![pv(0), pv(1), pv(2)]), ZK), None);
}

#[test]
fn a_symbol_of_another_sort_fails() {
    assert_eq!(run(&pf(PAIR, vec![pv(0), pv(1)]), NAT), None);
    assert_eq!(run(&pf(S, vec![pv(0)]), ZK), None);
}

#[test]
fn a_symbol_fails_in_a_sort_with_no_member_or_no_declaration() {
    assert_eq!(run(&pf(S, vec![pv(0)]), UNDECLARED), None);
    assert_eq!(run(&pf(S, vec![pv(0)]), NIL), None);
}

#[test]
fn a_failure_at_the_end_of_a_chain_fails() {
    assert_eq!(run(&pf(S, vec![pf(S, vec![pf(S, vec![c(Q)])])]), NAT), None);
}

// Calls one after another.

#[test]
fn a_call_does_not_depend_on_the_calls_before_it() {
    let ss = sorts();
    let mut s = Store::new();
    let table = put_sorts(&mut s, &ss);
    let nat = s.alloc(Node::Sym(NAT));
    let zk = s.alloc(Node::Sym(ZK));
    let k = put_pat(&mut s, &c(K));
    assert!(push_sort(&mut s, table, nat, k).is_none());
    // The same pair again: the flag of the first call must not answer it.
    assert!(push_sort(&mut s, table, nat, k).is_none());
    let t = put_pat(&mut s, &pf(PAIR, vec![pv(0), pv(1)]));
    let first = push_sort(&mut s, table, zk, t).map(|l| read_atoms(&mut s, l));
    let second = push_sort(&mut s, table, zk, t).map(|l| read_atoms(&mut s, l));
    assert_eq!(first, atoms(&[(0, ZK), (1, ZK)]));
    assert_eq!(second, atoms(&[(0, ZK), (1, ZK)]));
}

#[test]
fn the_flags_of_member_do_not_answer_a_call() {
    let mut s = Store::new();
    let table = put_sorts(&mut s, &sorts());
    let zk = s.alloc(Node::Sym(ZK));
    let t = put_pat(&mut s, &pf(PAIR, vec![pv(0), c(Z)]));
    let g = put_pat(&mut s, &pf(PAIR, vec![c(Z), c(Z)]));
    s.clear(Tbl::B);
    assert!(member(&mut s, table, zk, g));
    // Pretend the pair of `ZK` with `t` was asked about.
    let pair = s.alloc(Node::App(zk, t));
    s.set_flag(Tbl::B, pair, true);
    let got = push_sort(&mut s, table, zk, t).map(|l| read_atoms(&mut s, l));
    assert_eq!(got, atoms(&[(0, ZK)]));
}

#[test]
fn table_a_is_not_written() {
    let mut s = Store::new();
    let table = put_sorts(&mut s, &sorts());
    let zk = s.alloc(Node::Sym(ZK));
    let t = put_pat(&mut s, &pf(PAIR, vec![pv(0), c(Z)]));
    s.clear(Tbl::A);
    s.set_flag(Tbl::A, t, true);
    assert!(push_sort(&mut s, table, zk, t).is_some());
    assert_eq!(s.get_flag(Tbl::A, t), Some(true));
    let pair = s.alloc(Node::App(zk, t));
    assert_eq!(s.get_flag(Tbl::A, pair), None);
}

// Depth, and sharing.

const DEEP: usize = 100_000;

/// `f` applied `n` times to `leaf`.
fn chain(s: &mut Store, f: u32, leaf: TermId, n: usize) -> TermId {
    let f = s.alloc(Node::Sym(f));
    let mut t = leaf;
    for _ in 0..n {
        t = s.alloc(Node::App(f, t));
    }
    t
}

#[test]
fn a_deep_chain_is_walked_in_ticks_linear_in_its_depth() {
    let mut s = Store::new();
    let table = put_sorts(&mut s, &sorts());
    let nat = s.alloc(Node::Sym(NAT));
    let x = put(&mut s, &T::V(0));
    let t = chain(&mut s, S, x, DEEP);
    let (got, ticks) = spent(&mut s, |s| push_sort(s, table, nat, t));
    let got = got.map(|l| read_atoms(&mut s, l));
    assert_eq!(got, atoms(&[(0, NAT)]));
    assert!(ticks < 60 * DEEP as u64, "{} ticks", ticks);
    assert!(s.pop().is_none());
}

#[test]
fn a_deep_chain_under_any_term_is_not_walked() {
    let mut s = Store::new();
    let table = put_sorts(&mut s, &sorts());
    let pos = s.alloc(Node::Sym(POS));
    let x = put(&mut s, &T::V(0));
    let t = chain(&mut s, S, x, DEEP);
    let (got, ticks) = spent(&mut s, |s| push_sort(s, table, pos, t));
    let got = got.map(|l| read_atoms(&mut s, l));
    assert_eq!(got, atoms(&[]));
    assert!(ticks < 200, "{} ticks", ticks);
}

#[test]
fn a_deep_chain_that_fails_at_its_end_fails() {
    let mut s = Store::new();
    let table = put_sorts(&mut s, &sorts());
    let nat = s.alloc(Node::Sym(NAT));
    let q = put(&mut s, &T::S(Q));
    let t = chain(&mut s, S, q, DEEP);
    assert!(push_sort(&mut s, table, nat, t).is_none());
    assert!(s.pop().is_none());
}

#[test]
fn a_pattern_nested_to_the_left_is_walked_in_linear_ticks() {
    // pair(pair(... pair($0, $1) ..., $1), $1)
    let mut s = Store::new();
    let table = put_sorts(&mut s, &sorts());
    let zk = s.alloc(Node::Sym(ZK));
    let pair = s.alloc(Node::Sym(PAIR));
    let y = put(&mut s, &T::V(1));
    let mut t = put(&mut s, &T::V(0));
    for _ in 0..DEEP {
        let half = s.alloc(Node::App(pair, t));
        t = s.alloc(Node::App(half, y));
    }
    let (got, ticks) = spent(&mut s, |s| push_sort(s, table, zk, t));
    let got = got.map(|l| read_atoms(&mut s, l));
    assert_eq!(got, atoms(&[(0, ZK), (1, ZK)]));
    assert!(ticks < 100 * DEEP as u64, "{} ticks", ticks);
}

#[test]
fn a_symbol_with_many_arguments_is_walked_in_linear_ticks() {
    let mut s = Store::new();
    let table = put_sorts(&mut s, &sorts());
    let nok = s.alloc(Node::Sym(NOK));
    let x = put(&mut s, &T::V(0));
    let mut t = s.alloc(Node::Sym(Q));
    for _ in 0..DEEP {
        t = s.alloc(Node::App(t, x));
    }
    let (got, ticks) = spent(&mut s, |s| push_sort(s, table, nok, t));
    let got = got.map(|l| read_atoms(&mut s, l));
    assert_eq!(got, atoms(&[(0, NOK)]));
    assert!(ticks < 100 * DEEP as u64, "{} ticks", ticks);
}

/// A full tree of `pair` with 2^40 leaves `leaf`: 41 nodes in the store.
fn full(s: &mut Store, leaf: TermId) -> TermId {
    let pair = s.alloc(Node::Sym(PAIR));
    let mut t = leaf;
    for _ in 0..40 {
        let half = s.alloc(Node::App(pair, t));
        t = s.alloc(Node::App(half, t));
    }
    t
}

#[test]
fn a_shared_subterm_is_read_once_for_each_sort() {
    let mut s = Store::new();
    let table = put_sorts(&mut s, &sorts());
    let x = put(&mut s, &T::V(0));
    let t = full(&mut s, x);
    for (name, want) in [
        (ZK, atoms(&[(0, ZK)])),
        (KK, atoms(&[(0, ZK)])),
        (NOK, atoms(&[(0, NOK)])),
        (NAT, None),
        (NOPAIR, None),
        (ANY, atoms(&[])),
    ] {
        let node = s.alloc(Node::Sym(name));
        let (got, ticks) = spent(&mut s, |s| push_sort(s, table, node, t));
        let got = got.map(|l| read_atoms(&mut s, l));
        assert_eq!(got, want, "sort {}", name);
        assert!(ticks < 6000, "sort {}: {} ticks", name, ticks);
    }
}

#[test]
fn a_shared_subterm_under_two_sorts_costs_twice() {
    let mut s = Store::new();
    let table = put_sorts(&mut s, &sorts());
    let x = put(&mut s, &T::V(0));
    let half = full(&mut s, x);
    let pair = s.alloc(Node::Sym(PAIR));
    let l = s.alloc(Node::App(pair, half));
    let t = s.alloc(Node::App(l, half));
    let mix = s.alloc(Node::Sym(MIX));
    let (got, ticks) = spent(&mut s, |s| push_sort(s, table, mix, t));
    let got = got.map(|l| read_atoms(&mut s, l));
    assert_eq!(got, atoms(&[(0, NOK), (0, ZK)]));
    assert!(ticks < 12000, "{} ticks", ticks);
}

// Against the references.

struct Rng(u64);

impl Rng {
    fn next(&mut self, n: usize) -> usize {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % n
    }
}

/// A random pattern; one leaf in `vars + 3` is each variable below `vars`.
fn random_pat(rng: &mut Rng, depth: usize, vars: usize) -> P {
    match rng.next(if depth == 0 { 3 + vars } else { 8 + vars }) {
        0 => c(Z),
        1 => c(K),
        2 => c(Q),
        n if n < 3 + vars => pv(n - 3),
        n if n < 5 + vars => pf(S, vec![random_pat(rng, depth - 1, vars)]),
        n if n < 7 + vars => {
            pf(PAIR, vec![random_pat(rng, depth - 1, vars), random_pat(rng, depth - 1, vars)])
        }
        _ => pf(S, vec![random_pat(rng, depth - 1, vars), random_pat(rng, depth - 1, vars)]),
    }
}

#[test]
fn the_atoms_are_those_of_the_reference() {
    let ss = sorts();
    let mut rng = Rng(5);
    let (mut some, mut none) = (0, 0);
    for round in 0..4000 {
        let p = random_pat(&mut rng, 4, 4);
        let name = NAMES[rng.next(NAMES.len())];
        let got = run(&p, name);
        assert_eq!(got, push(&ss, name, &p), "round {}: {:?} : {}", round, p, name);
        match got {
            Some(a) if !a.is_empty() => some += 1,
            Some(_) => {}
            None => none += 1,
        }
    }
    assert!(some > 300 && none > 300, "{} with atoms, {} failing", some, none);
}

#[test]
fn an_instance_is_a_member_exactly_when_the_atoms_hold() {
    let ss = sorts();
    let mut rng = Rng(23);
    let (mut held, mut failed) = (0, 0);
    for round in 0..4000 {
        let p = random_pat(&mut rng, 3, 3);
        let name = NAMES[rng.next(NAMES.len())];
        let sigma: std::collections::BTreeMap<usize, P> =
            (0..3).map(|x| (x, random_pat(&mut rng, 2, 0))).collect();
        let inst = p.subst(&sigma);
        let is = ss.member(name, &inst);
        match run(&p, name) {
            None => assert!(!is, "round {}: {:?} : {} failed, {:?} is a member", round, p, name, inst),
            Some(a) => {
                let hold = a.iter().all(|(x, m)| ss.member(*m, &sigma[x]));
                assert_eq!(is, hold, "round {}: {:?} : {} with {:?}", round, p, name, sigma);
                if hold {
                    held += 1
                } else {
                    failed += 1
                }
            }
        }
    }
    assert!(held > 200 && failed > 200, "{} held, {} did not", held, failed);
}

#[test]
fn every_atom_is_a_variable_of_the_pattern_with_a_sort() {
    let mut rng = Rng(41);
    for _ in 0..1000 {
        let p = random_pat(&mut rng, 4, 4);
        let name = NAMES[rng.next(NAMES.len())];
        let mut vars = Vec::new();
        p.vars(&mut vars);
        // `read_atoms` panics on anything that is not a variable with a sort.
        if let Some(a) = run(&p, name) {
            for (x, _) in a {
                assert!(vars.contains(&x), "{:?} : {} names ${}", p, name, x);
            }
        }
    }
}
