//! Sorts on the store against the reference on trees.

mod common;

use common::sorts::*;
use common::{put, spent, T};
use rwlog_core::sorts::{member, same_len, spine, step};
use rwlog_core::store::{Node, Store, Tbl};

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
const ONE: Name = 16;
const NIL: Name = 17;
const NOPAIR: Name = 18;
const TWICE: Name = 19;

/// The sorts of `sorts_reference.rs`, and two more: every term but those of
/// `pair` with two arguments, and a sort with two cases for one root.
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
        (NOPAIR, def(vec![(S, vec![Some(NAT)])], Some((vec![(PAIR, 2), (K, 0)], None)))),
        (TWICE, def(vec![(S, vec![Some(NIL)]), (S, vec![None]), (S, vec![None, None])], None)),
        // A second declaration of a name is not read.
        (NAT, def(vec![(K, vec![])], None)),
    ])
}

const NAMES: [Name; 11] = [NAT, POS, ANY, ZK, KK, NOK, ONE, NIL, NOPAIR, TWICE, 99];

fn c(f: u32) -> P {
    pf(f, vec![])
}

struct Rng(u64);

impl Rng {
    fn next(&mut self, n: usize) -> usize {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % n
    }
}

fn random_ground(rng: &mut Rng, depth: usize) -> P {
    match rng.next(if depth == 0 { 3 } else { 8 }) {
        0 => c(Z),
        1 => c(K),
        2 => c(Q),
        3..=4 => pf(S, vec![random_ground(rng, depth - 1)]),
        5..=6 => pf(PAIR, vec![random_ground(rng, depth - 1), random_ground(rng, depth - 1)]),
        _ => pf(S, vec![random_ground(rng, depth - 1), random_ground(rng, depth - 1)]),
    }
}

#[test]
fn spine_is_the_symbol_and_the_arguments_in_order() {
    let mut s = Store::new();
    let t = put_pat(&mut s, &pf(PAIR, vec![c(Z), pf(S, vec![c(K)])]));
    let (head, args) = spine(&mut s, t);
    assert!(matches!(s.read(head), Node::Sym(PAIR)));
    let want = vec![c(Z).tree(), pf(S, vec![c(K)]).tree()];
    assert_eq!(common::get_list(&mut s, args), want);
}

#[test]
fn spine_of_a_constant_has_no_argument() {
    let mut s = Store::new();
    let t = put_pat(&mut s, &c(K));
    let (head, args) = spine(&mut s, t);
    assert!(matches!(s.read(head), Node::Sym(K)));
    assert!(matches!(s.read(args), Node::Nil));
}

#[test]
fn spine_spends_two_ticks_for_each_argument_and_two() {
    let mut s = Store::new();
    let t = put_pat(&mut s, &pf(PAIR, vec![c(Z), c(K), c(Q)]));
    let (_, ticks) = spent(&mut s, |s| spine(s, t));
    assert_eq!(ticks, 2 * 3 + 2);
}

#[test]
fn same_len_compares_lengths() {
    let mut s = Store::new();
    let lists: Vec<_> = (0..4).map(|n| put_pats(&mut s, &vec![c(Z); n])).collect();
    let other: Vec<_> = (0..4).map(|n| put_pats(&mut s, &vec![c(K); n])).collect();
    for (i, a) in lists.iter().enumerate() {
        for (j, b) in other.iter().enumerate() {
            assert_eq!(same_len(&mut s, *a, *b), i == j, "{} and {}", i, j);
        }
    }
}

#[test]
fn step_is_the_step_of_the_reference() {
    let ss = sorts();
    let mut s = Store::new();
    let table = put_sorts(&mut s, &ss);
    for name in NAMES {
        for f in [Z, K, Q, S, PAIR] {
            for n in 0..4 {
                let node = s.alloc(Node::Sym(name));
                let head = s.alloc(Node::Sym(f));
                let args = put_pats(&mut s, &vec![c(Q); n]);
                let got = step(&mut s, table, node, head, args).map(|kids| get_kids(&mut s, kids));
                assert_eq!(got, ss.step(name, (f, n)), "sort {} at {}/{}", name, f, n);
            }
        }
    }
}

#[test]
fn member_is_the_member_of_the_reference() {
    let ss = sorts();
    let mut s = Store::new();
    let table = put_sorts(&mut s, &ss);
    let mut rng = Rng(7);
    let (mut yes, mut no) = (0, 0);
    for round in 0..3000 {
        let t = random_ground(&mut rng, 4);
        let name = NAMES[rng.next(NAMES.len())];
        let node = s.alloc(Node::Sym(name));
        let id = put_pat(&mut s, &t);
        s.clear(Tbl::B);
        let got = member(&mut s, table, node, id);
        assert_eq!(got, ss.member(name, &t), "round {}: {:?} in {}", round, t, name);
        if got {
            yes += 1
        } else {
            no += 1
        }
    }
    assert!(yes > 500 && no > 500, "{} in, {} out", yes, no);
}

#[test]
fn member_reads_a_shared_term_once_for_each_sort() {
    // A full tree of `pair` with 2^40 leaves `z` is 41 nodes in the store.
    let mut s = Store::new();
    let table = put_sorts(&mut s, &sorts());
    let pair = s.alloc(Node::Sym(PAIR));
    let mut t = put(&mut s, &T::S(Z));
    for _ in 0..40 {
        let half = s.alloc(Node::App(pair, t));
        t = s.alloc(Node::App(half, t));
    }
    for (name, want) in [(ZK, true), (KK, true), (NAT, false), (NOK, true)] {
        let node = s.alloc(Node::Sym(name));
        s.clear(Tbl::B);
        let (got, ticks) = spent(&mut s, |s| member(s, table, node, t));
        assert_eq!(got, want, "sort {}", name);
        assert!(ticks < 6000, "sort {}: {} ticks", name, ticks);
    }
}

#[test]
fn member_leaves_the_stack_empty() {
    let ss = sorts();
    let mut s = Store::new();
    let table = put_sorts(&mut s, &ss);
    let nat = s.alloc(Node::Sym(NAT));
    // Fails at the first argument, with the second still waiting.
    let t = put_pat(&mut s, &pf(PAIR, vec![c(Q), c(Z)]));
    let zk = s.alloc(Node::Sym(ZK));
    s.clear(Tbl::B);
    assert!(!member(&mut s, table, zk, t));
    assert!(s.pop().is_none());
    let u = put_pat(&mut s, &pf(S, vec![c(Z)]));
    s.clear(Tbl::B);
    assert!(member(&mut s, table, nat, u));
    assert!(s.pop().is_none());
}
