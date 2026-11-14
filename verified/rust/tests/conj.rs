//! Conjunctions of sorts on the store against the reference on trees.

mod common;

use common::sorts::*;
use common::spent;
use rwlog_core::sorts::{conj_meet, conj_of, member, names, step_conj};
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
const ONE: Name = 16;
const NIL: Name = 17;
const NOPAIR: Name = 18;
const TWICE: Name = 19;
/// Said of an argument by the second declaration of `NAT` only.
const HID: Name = 20;
/// Said of an argument, never declared.
const UND: Name = 21;
/// Every term, each argument in `NAT`.
const RK: Name = 22;
/// One case, whose argument is in `UND`.
const HOLE: Name = 23;

const LONG: usize = 400_000;

fn def(cases: Vec<(u32, Vec<Option<Name>>)>, rest: Option<(Vec<Key>, Option<Name>)>) -> Def {
    Def { cases, rest }
}

fn sorts() -> Sorts {
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
        (RK, def(vec![], Some((vec![], Some(NAT))))),
        (HOLE, def(vec![(S, vec![Some(UND)])], None)),
        // A second declaration of a name is not read, but what it says of an
        // argument is a name.
        (NAT, def(vec![(K, vec![Some(HID)])], None)),
    ])
}

/// A store with declarations in it, and the names as the reference lists
/// them.
struct Fx {
    s: Store,
    ss: Sorts,
    decls: TermId,
    order: Vec<Name>,
    names: TermId,
}

fn fx(ss: Sorts) -> Fx {
    let mut s = Store::new();
    let decls = put_sorts(&mut s, &ss);
    let order = ss.all_names();
    let names = put_names(&mut s, &order);
    Fx { s, ss, decls, order, names }
}

impl Fx {
    /// The node of a conjunction, built by the reference.
    fn conj(&mut self, c: &[Name]) -> TermId {
        let set: Conj = c.iter().copied().collect();
        let list = canon(&self.order, &set);
        put_names(&mut self.s, &list)
    }

    fn sym(&mut self, f: u32) -> TermId {
        self.s.alloc(Node::Sym(f))
    }

    fn nil(&mut self) -> TermId {
        self.s.alloc(Node::Nil)
    }

    /// `n` arguments, each the constant `q`.
    fn args(&mut self, n: usize) -> TermId {
        let q = self.sym(Q);
        let mut l = self.nil();
        for _ in 0..n {
            l = self.s.alloc(Node::App(q, l));
        }
        l
    }

    /// `step_conj` of the conjunction `c` at the root `f` with `n` arguments.
    fn step(&mut self, c: &[Name], f: u32, n: usize) -> Option<TermId> {
        let c = self.conj(c);
        let head = self.sym(f);
        let args = self.args(n);
        step_conj(&mut self.s, self.decls, self.names, c, head, args)
    }

    /// The same, read back.
    fn step_read(&mut self, c: &[Name], f: u32, n: usize) -> Option<Vec<Vec<Name>>> {
        self.step(c, f, n).map(|k| get_conjs(&mut self.s, k))
    }

    fn same(&mut self, a: TermId, b: TermId) -> bool {
        self.s.same(a, b)
    }
}

struct Rng(u64);

impl Rng {
    fn next(&mut self, n: usize) -> usize {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % n
    }
}

fn subsets(names: &[Name]) -> Vec<Vec<Name>> {
    (0..1usize << names.len())
        .map(|m| names.iter().enumerate().filter(|(i, _)| m >> i & 1 == 1).map(|(_, n)| *n).collect())
        .collect()
}

/// The names of the declarations, read back.
fn names_of(defs: Vec<(Name, Def)>) -> Vec<Name> {
    let mut s = Store::new();
    let decls = put_sorts(&mut s, &Sorts::new(defs));
    let r = names(&mut s, decls);
    get_names(&mut s, r)
}

fn case(f: u32, kids: &[Name]) -> (u32, Vec<Option<Name>>) {
    (f, kids.iter().map(|k| Some(*k)).collect())
}

// names

#[test]
fn names_of_no_declaration_is_nil() {
    let mut s = Store::new();
    let decls = s.alloc(Node::Nil);
    let r = names(&mut s, decls);
    assert!(s.same(r, decls));
}

#[test]
fn names_of_one_declaration_without_cases_or_rest_is_its_name() {
    assert_eq!(names_of(vec![(NIL, def(vec![], None))]), vec![NIL]);
}

#[test]
fn names_are_in_reverse_order_of_first_occurrence() {
    let got = names_of(vec![
        (1, def(vec![case(Z, &[2, 3])], Some((vec![], Some(4))))),
        (5, def(vec![], None)),
    ]);
    assert_eq!(got, vec![5, 4, 3, 2, 1]);
}

#[test]
fn names_reads_cases_in_order_and_kids_in_order_before_the_rest() {
    let got = names_of(vec![(
        1,
        def(vec![case(Z, &[2]), case(K, &[3, 4])], Some((vec![], Some(5)))),
    )]);
    assert_eq!(got, vec![5, 4, 3, 2, 1]);
}

#[test]
fn names_has_a_self_mentioned_name_once() {
    assert_eq!(names_of(vec![(NAT, def(vec![case(S, &[NAT])], None))]), vec![NAT]);
}

#[test]
fn names_has_a_name_mentioned_many_times_once() {
    let got = names_of(vec![
        (ZK, def(vec![case(PAIR, &[ZK, ZK])], None)),
        (KK, def(vec![case(PAIR, &[ZK, ZK])], None)),
    ]);
    assert_eq!(got, vec![KK, ZK]);
}

#[test]
fn names_places_a_name_mentioned_before_its_declaration_at_the_mention() {
    let got = names_of(vec![
        (1, def(vec![case(Z, &[2])], None)),
        (3, def(vec![], None)),
        (2, def(vec![], None)),
    ]);
    assert_eq!(got, vec![3, 2, 1]);
}

#[test]
fn names_has_an_undeclared_mentioned_name() {
    assert_eq!(names_of(vec![(1, def(vec![case(Z, &[UND])], None))]), vec![UND, 1]);
}

#[test]
fn names_has_a_name_declared_twice_once_at_its_first_place() {
    let got = names_of(vec![
        (NAT, def(vec![], None)),
        (POS, def(vec![], None)),
        (NAT, def(vec![], None)),
    ]);
    assert_eq!(got, vec![POS, NAT]);
}

#[test]
fn names_has_the_kids_of_a_second_declaration_of_a_name() {
    let got = names_of(vec![
        (NAT, def(vec![(Z, vec![])], None)),
        (NAT, def(vec![case(K, &[HID])], None)),
    ]);
    assert_eq!(got, vec![HID, NAT]);
}

#[test]
fn names_has_the_kid_of_a_rest() {
    assert_eq!(names_of(vec![(RK, def(vec![], Some((vec![], Some(NAT)))))]), vec![NAT, RK]);
}

#[test]
fn names_of_a_rest_with_any_term_adds_nothing() {
    assert_eq!(names_of(vec![(ANY, def(vec![], Some((vec![], None))))]), vec![ANY]);
}

#[test]
fn names_leaves_out_any_term_in_a_case() {
    assert_eq!(names_of(vec![(POS, def(vec![(S, vec![None, None])], None))]), vec![POS]);
}

#[test]
fn names_leaves_out_case_symbols() {
    assert_eq!(names_of(vec![(ONE, def(vec![(Z, vec![])], None))]), vec![ONE]);
}

#[test]
fn names_leaves_out_excluded_symbols() {
    let got = names_of(vec![(NOK, def(vec![], Some((vec![(K, 0), (S, 2)], Some(NOK)))))]);
    assert_eq!(got, vec![NOK]);
}

#[test]
fn names_keeps_a_name_whose_number_is_an_earlier_case_symbol() {
    let got = names_of(vec![(1, def(vec![(7, vec![])], None)), (7, def(vec![], None))]);
    assert_eq!(got, vec![7, 1]);
}

#[test]
fn names_keeps_a_name_whose_number_is_an_earlier_excluded_symbol() {
    let got = names_of(vec![
        (1, def(vec![], Some((vec![(7, 0)], None)))),
        (7, def(vec![], None)),
    ]);
    assert_eq!(got, vec![7, 1]);
}

#[test]
fn names_is_the_names_of_the_reference() {
    let mut f = fx(sorts());
    let r = names(&mut f.s, f.decls);
    assert_eq!(get_names(&mut f.s, r), f.order);
    assert!(f.same(r, f.names));
    assert_eq!(
        f.order,
        vec![HID, UND, HOLE, RK, TWICE, NOPAIR, NIL, ONE, NOK, KK, ZK, ANY, POS, NAT]
    );
}

#[test]
fn names_does_not_need_table_a_cleared() {
    let mut f = fx(sorts());
    let nat = f.sym(NAT);
    f.s.set_flag(Tbl::A, nat, true);
    let r = names(&mut f.s, f.decls);
    assert!(f.same(r, f.names));
    let again = names(&mut f.s, f.decls);
    assert!(f.same(again, f.names));
}

#[test]
fn names_leaves_table_b_and_the_stack_as_they_were() {
    let mut f = fx(sorts());
    let nat = f.sym(NAT);
    let pos = f.sym(POS);
    f.s.set_flag(Tbl::B, nat, true);
    names(&mut f.s, f.decls);
    assert_eq!(f.s.get_flag(Tbl::B, nat), Some(true));
    assert_eq!(f.s.get_flag(Tbl::B, pos), None);
    assert!(f.s.pop().is_none());
}

/// `n` declarations, each with one case of two arguments and a rest.
fn many(n: usize) -> Vec<(Name, Def)> {
    (0..n as u32)
        .map(|i| (100 + i, def(vec![case(S, &[100, 101])], Some((vec![], Some(100 + i))))))
        .collect()
}

#[test]
fn names_spends_at_most_a_fixed_number_of_ticks_for_each_declaration_case_and_argument() {
    for n in [0, 1, 2, 50, 100] {
        let mut s = Store::new();
        let decls = put_sorts(&mut s, &Sorts::new(many(n)));
        let (_, ticks) = spent(&mut s, |s| names(s, decls));
        // 13 for a declaration, 3 for a case, 5 for an argument of a case.
        let bound = 3 + (13 + 3 + 2 * 5) * n as u64;
        assert!(ticks <= bound, "{} declarations: {} ticks, bound {}", n, ticks, bound);
    }
}

#[test]
fn names_of_400000_declarations() {
    let mut s = Store::new();
    let name = |i: usize| 100 + i as u32;
    let empty = {
        let nil = s.alloc(Node::Nil);
        s.alloc(Node::App(nil, nil))
    };
    let mut decls = s.alloc(Node::Nil);
    for i in (0..LONG).rev() {
        let n = s.alloc(Node::Sym(name(i)));
        let d = s.alloc(Node::App(n, empty));
        decls = s.alloc(Node::App(d, decls));
    }
    let r = names(&mut s, decls);
    let got = get_names(&mut s, r);
    assert_eq!(got.len(), LONG);
    assert_eq!(got[0], name(LONG - 1));
    assert_eq!(got[LONG - 1], name(0));
}

#[test]
fn names_of_one_declaration_with_400000_cases_of_one_argument() {
    let mut s = Store::new();
    let nil = s.alloc(Node::Nil);
    let kid = s.alloc(Node::Sym(ZK));
    let kids = s.alloc(Node::App(kid, nil));
    let f = s.alloc(Node::Sym(S));
    let one = s.alloc(Node::App(f, kids));
    let mut cases = nil;
    for _ in 0..LONG {
        cases = s.alloc(Node::App(one, cases));
    }
    let d = s.alloc(Node::App(cases, nil));
    let n = s.alloc(Node::Sym(NAT));
    let e = s.alloc(Node::App(n, d));
    let decls = s.alloc(Node::App(e, nil));
    let (r, ticks) = spent(&mut s, |s| names(s, decls));
    assert_eq!(get_names(&mut s, r), vec![ZK, NAT]);
    assert!(ticks <= 3 + 13 + (3 + 5) * LONG as u64, "{} ticks", ticks);
}

// conj_of

#[test]
fn conj_of_the_empty_list_is_nil() {
    let mut f = fx(sorts());
    let nil = f.nil();
    let r = conj_of(&mut f.s, f.names, nil);
    assert!(f.same(r, nil));
    let none = conj_of(&mut f.s, nil, nil);
    assert!(f.same(none, nil));
}

#[test]
fn conj_of_one_name_is_that_name() {
    let mut f = fx(sorts());
    let l = put_names(&mut f.s, &[ZK]);
    let r = conj_of(&mut f.s, f.names, l);
    assert_eq!(get_names(&mut f.s, r), vec![ZK]);
}

#[test]
fn conj_of_a_repeated_name_has_it_once() {
    let mut f = fx(sorts());
    let l = put_names(&mut f.s, &[ZK, ZK, ZK]);
    let r = conj_of(&mut f.s, f.names, l);
    assert_eq!(get_names(&mut f.s, r), vec![ZK]);
}

#[test]
fn conj_of_is_in_the_order_of_names_from_its_end() {
    let mut s = Store::new();
    let names = put_names(&mut s, &[3, 2, 1]);
    let l = put_names(&mut s, &[3, 1]);
    let r = conj_of(&mut s, names, l);
    assert_eq!(get_names(&mut s, r), vec![1, 3]);
}

#[test]
fn conj_of_any_order_is_the_same_node() {
    let mut f = fx(sorts());
    let want = f.conj(&[NAT, ZK, NOK]);
    for l in [
        [NAT, ZK, NOK],
        [NAT, NOK, ZK],
        [ZK, NAT, NOK],
        [ZK, NOK, NAT],
        [NOK, NAT, ZK],
        [NOK, ZK, NAT],
    ] {
        let l = put_names(&mut f.s, &l);
        let r = conj_of(&mut f.s, f.names, l);
        assert!(f.same(r, want));
    }
}

#[test]
fn conj_of_names_is_every_name_from_the_end() {
    let mut f = fx(sorts());
    let r = conj_of(&mut f.s, f.names, f.names);
    let mut want = f.order.clone();
    want.reverse();
    assert_eq!(get_names(&mut f.s, r), want);
}

#[test]
fn conj_of_a_conjunction_is_itself() {
    let mut f = fx(sorts());
    for c in subsets(&[NAT, ZK, UND, HID]) {
        let c = f.conj(&c);
        let r = conj_of(&mut f.s, f.names, c);
        assert!(f.same(r, c));
    }
}

#[test]
fn conj_of_the_first_name_only_and_of_the_last_name_only() {
    let mut f = fx(sorts());
    for n in [f.order[0], f.order[f.order.len() - 1]] {
        let l = put_names(&mut f.s, &[n]);
        let r = conj_of(&mut f.s, f.names, l);
        assert_eq!(get_names(&mut f.s, r), vec![n]);
    }
}

#[test]
fn conj_of_is_the_set_of_the_reference() {
    let mut f = fx(sorts());
    let mut rng = Rng(11);
    for round in 0..500 {
        let len = rng.next(9);
        let l: Vec<Name> = (0..len).map(|_| f.order[rng.next(f.order.len())]).collect();
        let want = f.conj(&l);
        let list = put_names(&mut f.s, &l);
        let r = conj_of(&mut f.s, f.names, list);
        assert!(f.same(r, want), "round {}: {:?}", round, l);
    }
}

#[test]
fn conj_of_does_not_see_the_flags_of_an_earlier_call() {
    let mut f = fx(sorts());
    names(&mut f.s, f.decls);
    let zk = put_names(&mut f.s, &[ZK]);
    let r = conj_of(&mut f.s, f.names, zk);
    assert!(f.same(r, zk));
    let nat = put_names(&mut f.s, &[NAT]);
    conj_of(&mut f.s, f.names, nat);
    let again = conj_of(&mut f.s, f.names, zk);
    assert!(f.same(again, zk));
}

#[test]
fn conj_of_leaves_table_b_and_the_stack_as_they_were() {
    let mut f = fx(sorts());
    let nat = f.sym(NAT);
    let zk = f.sym(ZK);
    f.s.set_flag(Tbl::B, nat, true);
    let l = put_names(&mut f.s, &[NAT, ZK]);
    conj_of(&mut f.s, f.names, l);
    assert_eq!(f.s.get_flag(Tbl::B, nat), Some(true));
    assert_eq!(f.s.get_flag(Tbl::B, zk), None);
    assert!(f.s.pop().is_none());
}

#[test]
fn conj_of_spends_two_ticks_for_each_member_and_three_for_each_name_and_four() {
    for n in [0usize, 1, 7, 100] {
        for len in [0usize, 1, 5, 200] {
            let mut s = Store::new();
            let order: Vec<Name> = (0..n as u32).collect();
            let names = put_names(&mut s, &order);
            let l: Vec<Name> = if n == 0 { vec![] } else { (0..len).map(|i| (i % n) as u32).collect() };
            let list = put_names(&mut s, &l);
            let (_, ticks) = spent(&mut s, |s| conj_of(s, names, list));
            let bound = (2 * l.len() + 3 * n + 4) as u64;
            assert!(ticks <= bound, "{} names, {} members: {} ticks", n, l.len(), ticks);
        }
    }
}

#[test]
fn conj_of_a_list_400000_long_of_two_names() {
    let mut f = fx(sorts());
    let l: Vec<Name> = (0..LONG).map(|i| if i % 2 == 0 { NAT } else { ZK }).collect();
    let list = put_names(&mut f.s, &l);
    let want = f.conj(&[NAT, ZK]);
    let r = conj_of(&mut f.s, f.names, list);
    assert!(f.same(r, want));
}

#[test]
fn conj_of_400000_names_all_of_them() {
    let mut s = Store::new();
    let order: Vec<Name> = (0..LONG as u32).collect();
    let names = put_names(&mut s, &order);
    let r = conj_of(&mut s, names, names);
    let got = get_names(&mut s, r);
    assert_eq!(got.len(), LONG);
    assert_eq!(got[0], LONG as u32 - 1);
}

// conj_meet

#[test]
fn conj_meet_of_nil_and_nil_is_nil() {
    let mut f = fx(sorts());
    let nil = f.nil();
    let r = conj_meet(&mut f.s, f.names, nil, nil);
    assert!(f.same(r, nil));
}

#[test]
fn conj_meet_with_nil_is_the_other() {
    let mut f = fx(sorts());
    let nil = f.nil();
    let a = f.conj(&[NAT, NOK, UND]);
    let l = conj_meet(&mut f.s, f.names, nil, a);
    assert!(f.same(l, a));
    let r = conj_meet(&mut f.s, f.names, a, nil);
    assert!(f.same(r, a));
}

#[test]
fn conj_meet_with_itself_is_itself() {
    let mut f = fx(sorts());
    let a = f.conj(&[NAT, NOK, UND]);
    let r = conj_meet(&mut f.s, f.names, a, a);
    assert!(f.same(r, a));
}

#[test]
fn conj_meet_is_the_union_of_the_reference() {
    let mut f = fx(sorts());
    let all = subsets(&[NAT, ZK, NOK, HID]);
    for a in &all {
        for b in &all {
            let mut both = a.clone();
            both.extend(b);
            let want = f.conj(&both);
            let ia = f.conj(a);
            let ib = f.conj(b);
            let r = conj_meet(&mut f.s, f.names, ia, ib);
            assert!(f.same(r, want), "{:?} and {:?}", a, b);
        }
    }
}

#[test]
fn conj_meet_is_commutative_and_associative() {
    let mut f = fx(sorts());
    let all = subsets(&[NAT, ZK, NOK]);
    let names = f.names;
    for a in &all {
        for b in &all {
            for c in &all {
                let (a, b, c) = (f.conj(a), f.conj(b), f.conj(c));
                let ab = conj_meet(&mut f.s, names, a, b);
                let ba = conj_meet(&mut f.s, names, b, a);
                assert!(f.same(ab, ba));
                let bc = conj_meet(&mut f.s, names, b, c);
                let l = conj_meet(&mut f.s, names, ab, c);
                let r = conj_meet(&mut f.s, names, a, bc);
                assert!(f.same(l, r));
            }
        }
    }
}

#[test]
fn conj_meet_of_overlapping_sets_has_the_shared_name_once() {
    let mut f = fx(sorts());
    let a = f.conj(&[NAT, ZK]);
    let b = f.conj(&[ZK, NOK]);
    let r = conj_meet(&mut f.s, f.names, a, b);
    assert_eq!(get_names(&mut f.s, r), vec![NAT, ZK, NOK]);
}

#[test]
fn conj_meet_of_every_name_with_anything_is_every_name() {
    let mut f = fx(sorts());
    let order = f.order.clone();
    let all = f.conj(&order);
    let a = f.conj(&[POS, HID]);
    let r = conj_meet(&mut f.s, f.names, all, a);
    assert!(f.same(r, all));
}

#[test]
fn conj_meet_interleaves_in_the_order_of_names() {
    let mut s = Store::new();
    let names = put_names(&mut s, &[4, 3, 2, 1]);
    let a = put_names(&mut s, &[1, 3]);
    let b = put_names(&mut s, &[2, 4]);
    let r = conj_meet(&mut s, names, a, b);
    assert_eq!(get_names(&mut s, r), vec![1, 2, 3, 4]);
}

#[test]
fn conj_meet_does_not_see_the_flags_of_an_earlier_meet() {
    let mut f = fx(sorts());
    let nil = f.nil();
    let a = f.conj(&[NAT]);
    let b = f.conj(&[ZK]);
    let c = f.conj(&[NOK]);
    conj_meet(&mut f.s, f.names, a, b);
    let r = conj_meet(&mut f.s, f.names, c, nil);
    assert!(f.same(r, c));
}

#[test]
fn conj_meet_leaves_table_b_and_the_stack_as_they_were() {
    let mut f = fx(sorts());
    let nat = f.sym(NAT);
    let zk = f.sym(ZK);
    f.s.set_flag(Tbl::B, nat, true);
    let a = f.conj(&[NAT]);
    let b = f.conj(&[ZK]);
    conj_meet(&mut f.s, f.names, a, b);
    assert_eq!(f.s.get_flag(Tbl::B, nat), Some(true));
    assert_eq!(f.s.get_flag(Tbl::B, zk), None);
    assert!(f.s.pop().is_none());
}

#[test]
fn conj_meet_spends_two_ticks_for_each_member_and_three_for_each_name_and_five() {
    for n in [1usize, 2, 9, 100] {
        let mut s = Store::new();
        let order: Vec<Name> = (0..n as u32).rev().collect();
        let names = put_names(&mut s, &order);
        for (la, lb) in [(0, 0), (n, 0), (0, n), (n, n), (n / 2, n)] {
            let a: Vec<Name> = (0..la as u32).collect();
            let b: Vec<Name> = (0..lb as u32).collect();
            let (ia, ib) = (put_names(&mut s, &a), put_names(&mut s, &b));
            let (_, ticks) = spent(&mut s, |s| conj_meet(s, names, ia, ib));
            let bound = (2 * la + 2 * lb + 3 * n + 5) as u64;
            assert!(ticks <= bound, "{} names, {} and {}: {} ticks", n, la, lb, ticks);
        }
    }
}

#[test]
fn conj_meet_of_two_sets_of_200000_names_each() {
    let mut s = Store::new();
    let order: Vec<Name> = (0..LONG as u32).rev().collect();
    let names = put_names(&mut s, &order);
    let a: Vec<Name> = (0..LONG as u32).filter(|i| i % 2 == 0).collect();
    let b: Vec<Name> = (0..LONG as u32).filter(|i| i % 2 == 1).collect();
    let (ia, ib) = (put_names(&mut s, &a), put_names(&mut s, &b));
    let r = conj_meet(&mut s, names, ia, ib);
    let got = get_names(&mut s, r);
    assert_eq!(got.len(), LONG);
    assert_eq!(&got[..3], &[0, 1, 2]);
}

// step_conj

#[test]
fn step_conj_of_the_empty_conjunction_and_no_argument_is_no_conjunction() {
    let mut f = fx(sorts());
    let nil = f.nil();
    let r = f.step(&[], Q, 0).expect("accepted");
    assert!(f.same(r, nil));
}

#[test]
fn step_conj_of_the_empty_conjunction_is_the_empty_conjunction_for_each_argument() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[], Q, 3), Some(vec![vec![], vec![], vec![]]));
    let mut g = fx(Sorts::new(vec![]));
    assert_eq!(g.step_read(&[], Q, 2), Some(vec![vec![], vec![]]));
}

#[test]
fn step_conj_of_one_sort_is_its_step() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[NAT], S, 1), Some(vec![vec![NAT]]));
}

#[test]
fn step_conj_of_a_constant_every_sort_has_is_no_conjunction() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[NAT, ZK, ONE], Z, 0), Some(vec![]));
}

#[test]
fn step_conj_is_nothing_when_one_sort_rejects_wherever_it_stands() {
    let mut f = fx(sorts());
    // `POS` has no `z`. It is the first member of one list and the last of
    // the other.
    assert_eq!(f.step_read(&[NAT, POS], Z, 0), None);
    assert_eq!(f.step_read(&[POS, ANY, ZK], Z, 0), None);
    assert_eq!(f.step_read(&[NAT, ANY, ZK, POS, ONE], Z, 0), None);
}

#[test]
fn step_conj_is_nothing_for_an_undeclared_name() {
    let mut f = fx(sorts());
    for n in 0..3 {
        assert_eq!(f.step_read(&[UND], Q, n), None);
        assert_eq!(f.step_read(&[ANY, UND], Q, n), None);
        assert_eq!(f.step_read(&[HID], K, n), None);
    }
}

#[test]
fn step_conj_is_nothing_for_a_sort_with_no_case_and_no_rest() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[NIL], Z, 0), None);
}

#[test]
fn step_conj_is_nothing_for_another_number_of_arguments() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[ZK], PAIR, 1), None);
    assert_eq!(f.step_read(&[ZK], PAIR, 3), None);
}

#[test]
fn step_conj_is_nothing_for_an_excluded_symbol_with_its_number_of_arguments_only() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[NOK], K, 0), None);
    assert_eq!(f.step_read(&[NOK], K, 1), Some(vec![vec![NOK]]));
}

#[test]
fn step_conj_of_a_rest_gives_its_sort_to_each_argument() {
    let mut f = fx(sorts());
    let want = f.conj(&[NOK]);
    let r = f.step(&[NOK], Q, 3).expect("accepted");
    let mut l = r;
    for _ in 0..3 {
        match f.s.read(l) {
            Node::App(h, t) => {
                assert!(f.same(h, want));
                l = t;
            }
            _ => panic!("fewer than three"),
        }
    }
    assert!(matches!(f.s.read(l), Node::Nil));
}

#[test]
fn step_conj_of_a_rest_with_any_term_gives_the_empty_conjunction_to_each_argument() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[ANY], Q, 2), Some(vec![vec![], vec![]]));
}

#[test]
fn step_conj_reads_a_case_before_the_rest() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[NOPAIR], S, 1), Some(vec![vec![NAT]]));
}

#[test]
fn step_conj_is_nothing_when_one_sort_excludes_a_symbol_another_has_a_case_for() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[NOPAIR, ZK], PAIR, 2), None);
}

#[test]
fn step_conj_reads_the_first_case_with_the_number_of_arguments() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[TWICE], S, 1), Some(vec![vec![NIL]]));
    assert_eq!(f.step_read(&[TWICE], S, 2), Some(vec![vec![], vec![]]));
}

#[test]
fn step_conj_any_term_adds_no_sort() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[NAT, POS], S, 1), Some(vec![vec![NAT]]));
    assert_eq!(f.step_read(&[POS, ANY], S, 1), Some(vec![vec![]]));
}

#[test]
fn step_conj_joins_the_sorts_of_a_case_and_of_a_rest() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[NAT, RK], S, 1), Some(vec![vec![NAT]]));
    let want = f.conj(&[NAT, NOK]);
    let r = f.step(&[NAT, NOK, POS], S, 1).expect("accepted");
    match f.s.read(r) {
        Node::App(h, _) => assert!(f.same(h, want)),
        _ => panic!("no argument"),
    }
}

#[test]
fn step_conj_has_a_sort_two_members_give_once() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[ZK, KK], PAIR, 2), Some(vec![vec![ZK], vec![ZK]]));
}

#[test]
fn step_conj_gives_one_node_whatever_the_order_of_the_declarations() {
    for flip in [false, true] {
        let mut defs = vec![
            (1, def(vec![case(Z, &[3])], None)),
            (2, def(vec![case(Z, &[4])], None)),
        ];
        if flip {
            defs.reverse();
        }
        let mut f = fx(Sorts::new(defs));
        let want = f.conj(&[3, 4]);
        let r = f.step(&[1, 2], Z, 1).expect("accepted");
        match f.s.read(r) {
            Node::App(h, _) => assert!(f.same(h, want)),
            _ => panic!("no argument"),
        }
    }
}

#[test]
fn step_conj_keeps_the_arguments_apart() {
    let mut f = fx(Sorts::new(vec![
        (1, def(vec![case(Z, &[3, 4])], None)),
        (2, def(vec![(Z, vec![Some(5), None])], None)),
        (6, def(vec![(Z, vec![None, Some(7)])], None)),
    ]));
    assert_eq!(f.step_read(&[1], Z, 2), Some(vec![vec![3], vec![4]]));
    assert_eq!(f.step_read(&[2, 6], Z, 2), Some(vec![vec![5], vec![7]]));
    assert_eq!(f.step_read(&[1, 2, 6], Z, 2), Some(vec![vec![3, 5], vec![4, 7]]));
}

#[test]
fn step_conj_reads_only_the_first_declaration_of_a_name() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[NAT], K, 1), None);
}

#[test]
fn step_conj_gives_an_undeclared_name_a_case_says_of_an_argument() {
    let mut f = fx(sorts());
    assert_eq!(f.step_read(&[HOLE], S, 1), Some(vec![vec![UND]]));
}

#[test]
fn step_conj_of_no_declaration_and_a_sort_is_nothing() {
    let mut s = Store::new();
    let nil = s.alloc(Node::Nil);
    let c = put_names(&mut s, &[1]);
    let head = s.alloc(Node::Sym(Z));
    assert!(step_conj(&mut s, nil, c, c, head, nil).is_none());
}

#[test]
fn step_conj_is_the_step_conj_of_the_reference() {
    let mut f = fx(sorts());
    let order = f.order.clone();
    let mut rng = Rng(5);
    let (mut some, mut none) = (0, 0);
    for round in 0..600 {
        let c: Vec<Name> = order.iter().copied().filter(|_| rng.next(4) == 0).collect();
        let set: Conj = c.iter().copied().collect();
        for head in [Z, K, Q, S, PAIR] {
            for n in 0..4 {
                let want = f.ss.step_conj(&set, (head, n));
                let got = f.step(&c, head, n);
                match (&want, got) {
                    (None, None) => none += 1,
                    (Some(kids), Some(r)) => {
                        some += 1;
                        let mut l = r;
                        for kid in kids {
                            let k: Vec<Name> = kid.iter().copied().collect();
                            let node = f.conj(&k);
                            match f.s.read(l) {
                                Node::App(h, t) => {
                                    assert!(f.same(h, node), "round {}: {:?} at {}/{}", round, c, head, n);
                                    l = t;
                                }
                                _ => panic!("round {}: fewer conjunctions than arguments", round),
                            }
                        }
                        assert!(matches!(f.s.read(l), Node::Nil));
                    }
                    _ => panic!("round {}: {:?} at {}/{}: reference {:?}", round, c, head, n, want),
                }
            }
        }
    }
    assert!(some > 500 && none > 500, "{} accepted, {} rejected", some, none);
}

fn random_ground(rng: &mut Rng, depth: usize) -> P {
    let c = |f| pf(f, vec![]);
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
fn a_term_is_in_every_sort_exactly_when_the_step_accepts_and_each_argument_is_in_its_sorts() {
    let mut f = fx(sorts());
    let order = f.order.clone();
    let mut rng = Rng(3);
    let (mut yes, mut no) = (0, 0);
    for round in 0..1500 {
        let c: Vec<Name> = order.iter().copied().filter(|_| rng.next(6) == 0).collect();
        let t = random_ground(&mut rng, 3);
        let (head, args) = match &t {
            P::F(h, a) => (*h, a.clone()),
            P::V(_) => unreachable!(),
        };
        let whole = c.iter().all(|n| f.ss.member(*n, &t));
        let ci = f.conj(&c);
        let hi = f.sym(head);
        let ai = put_pats(&mut f.s, &args);
        let parts = match step_conj(&mut f.s, f.decls, f.names, ci, hi, ai) {
            None => false,
            Some(kids) => {
                let kids = get_conjs(&mut f.s, kids);
                assert_eq!(kids.len(), args.len());
                let mut all = true;
                for (kid, a) in kids.iter().zip(&args) {
                    for m in kid {
                        let mi = f.sym(*m);
                        let ti = put_pat(&mut f.s, a);
                        f.s.clear(Tbl::B);
                        all &= member(&mut f.s, f.decls, mi, ti);
                    }
                }
                all
            }
        };
        assert_eq!(parts, whole, "round {}: {:?} in {:?}", round, t, c);
        if whole {
            yes += 1
        } else {
            no += 1
        }
    }
    assert!(yes > 200 && no > 200, "{} in, {} out", yes, no);
}

#[test]
fn step_conj_does_not_need_table_a_cleared() {
    let mut f = fx(sorts());
    names(&mut f.s, f.decls);
    assert_eq!(f.step_read(&[ZK], PAIR, 2), Some(vec![vec![ZK], vec![ZK]]));
    assert_eq!(f.step_read(&[POS, ANY], S, 1), Some(vec![vec![]]));
}

#[test]
fn step_conj_leaves_table_b_as_it_was() {
    let mut f = fx(sorts());
    let nat = f.sym(NAT);
    let zk = f.sym(ZK);
    f.s.set_flag(Tbl::B, nat, true);
    f.step(&[ZK, NAT], Z, 0);
    f.step(&[ZK], PAIR, 2);
    assert_eq!(f.s.get_flag(Tbl::B, nat), Some(true));
    assert_eq!(f.s.get_flag(Tbl::B, zk), None);
}

#[test]
fn step_conj_leaves_the_stack_empty() {
    let mut f = fx(sorts());
    assert!(f.step(&[ZK, KK], PAIR, 2).is_some());
    assert!(f.s.pop().is_none());
    assert!(f.step(&[NAT, ANY, POS], Z, 0).is_none());
    assert!(f.s.pop().is_none());
}

#[test]
fn step_conj_spends_ticks_in_proportion_to_the_arguments() {
    let run = |n: usize| {
        let mut f = fx(sorts());
        let c = f.conj(&[NOK, RK]);
        let head = f.sym(Q);
        let args = f.args(n);
        let (r, ticks) = spent(&mut f.s, |s| step_conj(s, f.decls, f.names, c, head, args));
        assert!(r.is_some());
        ticks
    };
    let base = run(0);
    for n in [1u64, 2, 10, 100] {
        let ticks = run(n as usize);
        // For each argument: each of the two sorts measures and fills it
        // (at most 6 each), 5 for each sort to flag what it gives, 3 for
        // each of the 14 names, and 9.
        assert!(ticks <= base + n * (2 * 6 + 2 * 5 + 3 * 14 + 9), "{} arguments: {} ticks", n, ticks);
    }
}

#[test]
fn step_conj_spends_ticks_in_proportion_to_the_conjunction() {
    let all = [ANY, NOK, RK, NOPAIR];
    let run = |k: usize| {
        let mut f = fx(sorts());
        let c = f.conj(&all[..k]);
        let head = f.sym(Q);
        let args = f.args(2);
        let (r, ticks) = spent(&mut f.s, |s| step_conj(s, f.decls, f.names, c, head, args));
        assert!(r.is_some());
        ticks
    };
    let base = run(0);
    let one = (1..=4).map(|k| run(k) - run(k - 1)).max().unwrap();
    for k in 1..=4u64 {
        assert!(run(k as usize) <= base + k * one);
    }
    // The 13 declarations are searched once for each sort, at no more than
    // 20 ticks each.
    assert!(one <= 13 * 20, "{} ticks for one sort", one);
}

#[test]
fn step_conj_of_400000_arguments_through_two_rests() {
    let mut f = fx(sorts());
    let want = f.conj(&[NOK, NAT]);
    let r = f.step(&[NOK, RK], Q, LONG).expect("accepted");
    let mut l = r;
    let mut n = 0;
    while let Node::App(h, t) = f.s.read(l) {
        if n == 0 || n == LONG - 1 {
            assert!(f.same(h, want));
        }
        n += 1;
        l = t;
    }
    assert_eq!(n, LONG);
    assert!(f.s.pop().is_none());
}

#[test]
fn step_conj_of_400000_arguments_is_nothing_when_the_case_has_two() {
    let mut f = fx(sorts());
    let c = f.conj(&[ZK]);
    let head = f.sym(PAIR);
    let args = f.args(LONG);
    let (r, ticks) = spent(&mut f.s, |s| step_conj(s, f.decls, f.names, c, head, args));
    assert!(r.is_none());
    assert!(ticks < 200, "{} ticks", ticks);
}
