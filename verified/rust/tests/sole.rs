//! The one root of the members of a conjunction of sorts that are not in a
//! list of ground terms (`sorts::sole_root`), against `Sorts.sole` of the
//! specification (`lean/RwLog/Sorts/Roots.lean`) as the reference on trees
//! has it.
//!
//! Every table of sorts here is well formed: each conjunction of its names
//! has no member, one, or infinitely many.

mod common;

use common::sorts::*;
use rwlog_core::sorts::{count, included, included_but, live, sole_root, step_conj, Count};
use rwlog_core::store::{Node, Store, TermId};

// Symbols.
const Z: u32 = 0;
const O: u32 = 1;
const F: u32 = 2;
const G: u32 = 3;
const SU: u32 = 5;

// Names.
const A: Name = 100;
const B: Name = 101;
const C: Name = 102;
const D: Name = 103;
const ZS: Name = 106;
const N: Name = 107;
const E: Name = 108;
const OD: Name = 109;
/// Never declared.
const Q: Name = 110;
const ANY: Name = 112;
const L1: Name = 113;
const PS: Name = 115;
const P2: Name = 116;
const P3: Name = 117;
const OS: Name = 118;
const NZ: Name = 119;
const NA: Name = 125;
const NB: Name = 126;
const ZZ: Name = 129;
const ZO: Name = 130;
const AN: Name = 141;
const A2: Name = 144;
const NS: Name = 146;
const RN: Name = 149;
const R1: Name = 170;
const RC: Name = 171;
const RF: Name = 172;
const T3: Name = 173;

type Case = (u32, Vec<Option<Name>>);
type Defs = Vec<(Name, Def)>;

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

fn nat(n: Name) -> Def {
    cases(vec![(Z, vec![]), (SU, vec![Some(n)])])
}

/// One root whose arguments are in the sorts given.
fn one(f: u32, kids: Vec<Option<Name>>) -> Def {
    cases(vec![(f, kids)])
}

fn with(mut base: Defs, extra: Defs) -> Defs {
    base.extend(extra);
    base
}

/// The naturals, those from one, two and three up, two constants and a sort
/// with no member.
fn nats() -> Defs {
    vec![
        (N, nat(N)),
        (PS, one(SU, vec![Some(N)])),
        (P2, one(SU, vec![Some(PS)])),
        (P3, one(SU, vec![Some(P2)])),
        (ZS, zero()),
        (OS, one(O, vec![])),
        (D, dead()),
    ]
}

/// The even and the odd naturals.
fn eo() -> Defs {
    vec![(E, cases(vec![(Z, vec![]), (SU, vec![Some(OD)])])), (OD, one(SU, vec![Some(E)]))]
}

fn hn() -> Defs {
    with(nats(), eo())
}

/// Every term, every term but `z`, two constants and the naturals.
fn anys() -> Defs {
    vec![
        (ANY, rest(vec![], vec![], None)),
        (NZ, rest(vec![], vec![(Z, 0)], None)),
        (ZS, zero()),
        (OS, one(O, vec![])),
        (N, nat(N)),
    ]
}

/// Sorts of pairs `f(_, _)`.
fn fd() -> Defs {
    with(
        nats(),
        vec![
            (A, one(F, vec![Some(N), Some(ZS)])),
            (NA, one(F, vec![Some(PS), None])),
            (B, one(F, vec![Some(OS), Some(N)])),
            (NB, one(F, vec![None, Some(PS)])),
            (ZZ, one(F, vec![Some(ZS), Some(ZS)])),
            (ZO, one(F, vec![Some(ZS), Some(OS)])),
        ],
    )
}

/// Sorts with two cases.
fn fe() -> Defs {
    with(
        nats(),
        vec![
            (A, cases(vec![(Z, vec![]), (F, vec![Some(N)])])),
            (B, cases(vec![(F, vec![]), (F, vec![Some(N)])])),
            (C, cases(vec![(F, vec![Some(ZS)]), (F, vec![Some(N), Some(ZS)])])),
            (A2, cases(vec![(F, vec![Some(N)]), (G, vec![Some(N)])])),
        ],
    )
}

fn f_of_zero() -> Defs {
    vec![(A, one(F, vec![Some(ZS)])), (ZS, zero()), (OS, one(O, vec![]))]
}

fn z() -> P {
    pf(Z, vec![])
}

fn o() -> P {
    pf(O, vec![])
}

fn s(t: P) -> P {
    pf(SU, vec![t])
}

fn f1(a: P) -> P {
    pf(F, vec![a])
}

fn f2(a: P, b: P) -> P {
    pf(F, vec![a, b])
}

struct Fx {
    s: Store,
    ss: Sorts,
    decls: TermId,
    order: Vec<Name>,
    names: TermId,
}

fn fx(defs: Defs) -> Fx {
    let ss = Sorts::new(defs);
    let mut s = Store::new();
    let decls = put_sorts(&mut s, &ss);
    let order = ss.all_names();
    let names = put_names(&mut s, &order);
    Fx { s, ss, decls, order, names }
}

/// A root with the sorts of each of its arguments, in the order of the
/// names of the table.
type Root = Option<(u32, Vec<Vec<Name>>)>;

impl Fx {
    fn conj(&mut self, c: &[Name]) -> TermId {
        let set: Conj = c.iter().copied().collect();
        let list = canon(&self.order, &set);
        assert_eq!(list.len(), set.len(), "a conjunction of names of the declarations");
        put_names(&mut self.s, &list)
    }

    /// `sole_root`, as it is in the store.
    fn raw(&mut self, c: &[Name], gone: &[P]) -> Option<(TermId, TermId)> {
        let c = self.conj(c);
        let g = put_pats(&mut self.s, gone);
        let got = sole_root(&mut self.s, self.decls, self.names, c, g);
        assert!(self.s.pop().is_none(), "the stack is not empty");
        got
    }

    fn read(&mut self, got: Option<(TermId, TermId)>) -> Root {
        got.map(|(f, kids)| {
            let f = match self.s.read(f) {
                Node::Sym(f) => f,
                _ => panic!("the root is not a symbol"),
            };
            (f, get_conjs(&mut self.s, kids))
        })
    }

    fn sole(&mut self, c: &[Name], gone: &[P]) -> Root {
        let got = self.raw(c, gone);
        self.read(got)
    }

    /// The reference's answer, in the same form.
    fn want(&self, c: &[Name], gone: &[P]) -> Root {
        let set: Conj = c.iter().copied().collect();
        self.ss.sole(&set, gone).map(|((f, _), kids)| (f, kids.iter().map(|k| canon(&self.order, k)).collect()))
    }
}

fn root(f: u32, kids: &[&[Name]]) -> Root {
    Some((f, kids.iter().map(|k| k.to_vec()).collect()))
}

/// The answer written by hand is the answer of the store and of the
/// reference. The sorts of an argument are written in the order of the
/// names of the table.
fn sole_is(defs: Defs, c: &[Name], gone: &[P], want: Root) {
    let mut f = fx(defs);
    assert_eq!(f.want(c, gone), want, "the reference on {:?} but {:?}", c, gone);
    assert_eq!(f.sole(c, gone), want, "the store on {:?} but {:?}", c, gone);
}

// Every sort has a rest.

#[test]
fn the_empty_conjunction_has_every_root() {
    sole_is(nats(), &[], &[], None);
    sole_is(nats(), &[], &[z()], None);
}

#[test]
fn sorts_that_all_have_a_rest_have_many_roots() {
    sole_is(anys(), &[ANY], &[], None);
    sole_is(anys(), &[ANY, NZ], &[z()], None);
}

#[test]
fn one_case_beside_a_rest_is_not_one_root() {
    let defs = with(nats(), vec![(R1, rest(vec![(F, vec![Some(N)])], vec![], None))]);
    sole_is(defs, &[R1], &[], None);
}

// A sort with a rest beside one without.

#[test]
fn a_rest_accepts_the_root_another_sort_names() {
    sole_is(anys(), &[ANY, ZS], &[], root(Z, &[]));
    sole_is(anys(), &[ANY, ZS], &[z()], None);
}

#[test]
fn a_rest_of_any_term_adds_nothing_to_an_argument() {
    sole_is(anys(), &[ANY, N], &[], None);
    sole_is(anys(), &[ANY, N], &[z()], root(SU, &[&[N]]));
}

#[test]
fn a_root_a_rest_excludes_is_refused() {
    sole_is(anys(), &[NZ, N], &[], root(SU, &[&[N]]));
    sole_is(anys(), &[NZ, ZS], &[], None);
}

#[test]
fn the_sort_of_a_rest_is_a_sort_of_the_argument() {
    let defs = with(nats(), vec![(RN, rest(vec![], vec![], Some(PS)))]);
    sole_is(defs.clone(), &[RN, N], &[], None);
    sole_is(defs, &[RN, N], &[z()], root(SU, &[&[N, PS]]));
}

#[test]
fn a_case_is_read_before_the_rest_of_its_sort() {
    let defs = with(nats(), vec![(RC, rest(vec![(SU, vec![Some(PS)])], vec![], None))]);
    sole_is(defs, &[RC, N], &[z()], root(SU, &[&[N, PS]]));
}

#[test]
fn a_case_of_a_sort_with_a_rest_is_refused_by_the_other_sort() {
    let defs = with(nats(), vec![(RF, rest(vec![(F, vec![None])], vec![], None))]);
    sole_is(defs, &[RF, ZS], &[], root(Z, &[]));
}

#[test]
fn a_rest_that_excludes_a_root_leaves_the_other() {
    let defs = || vec![(N, nat(N)), (NS, rest(vec![], vec![(SU, 1)], None)), (OS, one(O, vec![]))];
    sole_is(defs(), &[N, NS], &[], root(Z, &[]));
    sole_is(defs(), &[N, NS], &[z()], None);
}

// No declaration, or no member.

#[test]
fn a_sort_with_no_declaration_has_no_root() {
    let defs = || vec![(A, one(F, vec![Some(Q)])), (ZS, zero()), (D, dead())];
    sole_is(defs(), &[Q], &[], None);
    sole_is(defs(), &[Q], &[z()], None);
    sole_is(defs(), &[ZS, Q], &[], None);
    // The argument of `f` has no member.
    sole_is(defs(), &[A], &[], None);
}

#[test]
fn a_sort_with_no_case_has_no_root() {
    sole_is(nats(), &[D], &[], None);
    sole_is(nats(), &[D], &[z()], None);
}

#[test]
fn sorts_that_refuse_each_others_roots_have_no_root() {
    sole_is(nats(), &[ZS, PS], &[], None);
    sole_is(nats(), &[ZS, PS], &[z()], None);
    sole_is(nats(), &[ZS, OS], &[], None);
}

#[test]
fn a_root_whose_argument_has_no_member_is_not_a_root() {
    sole_is(hn(), &[E, OD], &[], None);
}

// One case.

#[test]
fn one_case_is_the_root() {
    sole_is(nats(), &[PS], &[], root(SU, &[&[N]]));
    sole_is(nats(), &[P3], &[], root(SU, &[&[P2]]));
}

#[test]
fn removing_some_of_many_members_keeps_the_root() {
    sole_is(nats(), &[PS], &[s(z()), s(s(z()))], root(SU, &[&[N]]));
}

#[test]
fn removed_terms_with_other_roots_change_nothing() {
    sole_is(nats(), &[PS], &[o()], root(SU, &[&[N]]));
    sole_is(nats(), &[PS], &[z()], root(SU, &[&[N]]));
    sole_is(nats(), &[PS], &[f2(z(), z())], root(SU, &[&[N]]));
}

// A constant.

#[test]
fn a_constant_is_a_root_with_no_arguments() {
    sole_is(nats(), &[ZS], &[], root(Z, &[]));
}

#[test]
fn the_one_member_removed_leaves_no_root() {
    sole_is(nats(), &[ZS], &[z()], None);
    sole_is(nats(), &[ZS], &[z(), z()], None);
}

#[test]
fn removing_another_term_keeps_the_constant() {
    sole_is(nats(), &[ZS], &[o()], root(Z, &[]));
    sole_is(nats(), &[ZS], &[s(z())], root(Z, &[]));
    sole_is(nats(), &[ZS], &[pf(Z, vec![z()])], root(Z, &[]));
    // A symbol with the number of a name.
    sole_is(nats(), &[ZS], &[pf(ZS, vec![])], root(Z, &[]));
}

// Two roots.

#[test]
fn two_roots_are_not_one() {
    sole_is(nats(), &[N], &[], None);
}

#[test]
fn removing_the_one_member_of_a_root_leaves_the_other_root() {
    sole_is(nats(), &[N], &[z()], root(SU, &[&[N]]));
    sole_is(nats(), &[N], &[z(), z()], root(SU, &[&[N]]));
}

#[test]
fn a_root_with_many_members_cannot_be_removed() {
    sole_is(nats(), &[N], &[s(z())], None);
    sole_is(nats(), &[N], &[z(), s(z())], root(SU, &[&[N]]));
    sole_is(nats(), &[N], &[s(z()), z()], root(SU, &[&[N]]));
}

#[test]
fn a_removed_term_outside_the_sort_changes_nothing() {
    sole_is(nats(), &[N], &[o()], None);
    sole_is(nats(), &[N], &[z(), o()], root(SU, &[&[N]]));
    sole_is(nats(), &[N], &[z(), pf(N, vec![])], root(SU, &[&[N]]));
}

#[test]
fn a_removed_term_with_the_symbol_at_another_arity_is_another_root() {
    sole_is(nats(), &[N], &[pf(SU, vec![])], None);
    sole_is(nats(), &[N], &[pf(SU, vec![z(), z()])], None);
    sole_is(nats(), &[N], &[z(), pf(SU, vec![z(), z()])], root(SU, &[&[N]]));
}

#[test]
fn a_case_whose_argument_has_no_member_is_not_counted() {
    let defs = || vec![(A, cases(vec![(Z, vec![]), (F, vec![Some(D)])])), (D, dead()), (OS, one(O, vec![]))];
    sole_is(defs(), &[A], &[], root(Z, &[]));
    sole_is(defs(), &[A], &[z()], None);
    sole_is(defs(), &[A], &[f1(z())], root(Z, &[]));
}

#[test]
fn an_argument_with_no_member_under_two_sorts_is_not_counted() {
    let defs = || {
        with(
            hn(),
            vec![
                (A, cases(vec![(Z, vec![]), (F, vec![Some(E)])])),
                (B, cases(vec![(Z, vec![]), (F, vec![Some(OD)])])),
            ],
        )
    };
    sole_is(defs(), &[A, B], &[], root(Z, &[]));
    sole_is(defs(), &[A, B], &[z()], None);
}

#[test]
fn a_constant_beside_a_root_with_many_members() {
    sole_is(fe(), &[A], &[], None);
    sole_is(fe(), &[A], &[z()], root(F, &[&[N]]));
    sole_is(fe(), &[A], &[f1(z())], None);
}

// Three roots.

#[test]
fn three_roots_need_two_removed() {
    let defs = || with(nats(), vec![(T3, cases(vec![(Z, vec![]), (O, vec![]), (SU, vec![Some(N)])]))]);
    sole_is(defs(), &[T3], &[], None);
    sole_is(defs(), &[T3], &[z()], None);
    sole_is(defs(), &[T3], &[z(), o()], root(SU, &[&[N]]));
    sole_is(defs(), &[T3], &[z(), s(z())], None);
    sole_is(defs(), &[T3], &[o(), s(z()), z()], root(SU, &[&[N]]));
}

// One symbol with two numbers of arguments.

#[test]
fn a_symbol_with_no_argument_and_with_one_is_two_roots() {
    sole_is(fe(), &[B], &[], None);
    sole_is(fe(), &[B], &[pf(F, vec![])], root(F, &[&[N]]));
    sole_is(fe(), &[B], &[f1(z())], None);
}

#[test]
fn a_symbol_with_one_argument_and_with_two_is_two_roots() {
    sole_is(fe(), &[C], &[], None);
    sole_is(fe(), &[C], &[f1(z())], root(F, &[&[N], &[ZS]]));
    sole_is(fe(), &[C], &[f2(z(), z())], None);
    sole_is(fe(), &[C], &[f1(z()), f2(z(), z())], root(F, &[&[N], &[ZS]]));
}

// A root with arguments and one member.

#[test]
fn a_root_whose_argument_has_one_member_has_one_member() {
    sole_is(f_of_zero(), &[A], &[], root(F, &[&[ZS]]));
    sole_is(f_of_zero(), &[A], &[f1(z())], None);
}

#[test]
fn only_the_one_member_removes_its_root() {
    for gone in [f1(o()), z(), f2(z(), z()), pf(F, vec![])] {
        sole_is(f_of_zero(), &[A], &[gone], root(F, &[&[ZS]]));
    }
}

#[test]
fn two_arguments_with_one_member_each() {
    sole_is(fd(), &[ZZ], &[], root(F, &[&[ZS], &[ZS]]));
    sole_is(fd(), &[ZZ], &[f2(z(), z())], None);
    sole_is(fd(), &[ZZ], &[f2(z(), o())], root(F, &[&[ZS], &[ZS]]));
    sole_is(fd(), &[ZZ], &[f2(o(), z())], root(F, &[&[ZS], &[ZS]]));
}

#[test]
fn the_arguments_are_read_in_order() {
    sole_is(fd(), &[ZO], &[], root(F, &[&[ZS], &[OS]]));
    sole_is(fd(), &[ZO], &[f2(z(), o())], None);
    sole_is(fd(), &[ZO], &[f2(o(), z())], root(F, &[&[ZS], &[OS]]));
}

#[test]
fn one_argument_with_many_members_keeps_the_root() {
    sole_is(fd(), &[A], &[f2(z(), z())], root(F, &[&[N], &[ZS]]));
}

#[test]
fn two_sorts_together_give_an_argument_one_member() {
    sole_is(fd(), &[A, ZZ], &[], root(F, &[&[N, ZS], &[ZS]]));
    sole_is(fd(), &[A, ZZ], &[f2(z(), z())], None);
    sole_is(fd(), &[A, ZZ], &[f2(s(z()), z())], root(F, &[&[N, ZS], &[ZS]]));
}

#[test]
fn two_sorts_together_give_an_argument_no_member() {
    sole_is(fd(), &[A, B], &[], None);
    sole_is(fd(), &[A, NB], &[], None);
}

#[test]
fn any_term_adds_nothing_to_the_sorts_of_an_argument() {
    sole_is(fd(), &[A, NA], &[], root(F, &[&[N, PS], &[ZS]]));
}

// Arguments that may be any term.

#[test]
fn an_argument_that_may_be_any_term_has_no_sort_and_many_members() {
    sole_is(fd(), &[NA], &[], root(F, &[&[PS], &[]]));
    sole_is(fd(), &[NA], &[f2(s(z()), z())], root(F, &[&[PS], &[]]));
    let defs = vec![(AN, one(F, vec![None])), (ZS, zero())];
    sole_is(defs, &[AN], &[f1(z())], root(F, &[&[]]));
}

// Nested.

#[test]
fn the_one_member_is_a_term_with_arguments() {
    let defs = || vec![(A, one(F, vec![Some(B)])), (B, one(G, vec![Some(ZS)])), (ZS, zero()), (OS, one(O, vec![]))];
    let g1 = |a: P| pf(G, vec![a]);
    sole_is(defs(), &[A], &[f1(g1(z()))], None);
    for gone in [f1(g1(o())), f1(z()), g1(z()), f2(g1(z()), z())] {
        sole_is(defs(), &[A], &[gone], root(F, &[&[B]]));
    }
}

#[test]
fn a_second_sort_gives_the_root_one_member() {
    let defs = || with(nats(), vec![(L1, one(SU, vec![Some(ZS)]))]);
    sole_is(defs(), &[L1], &[s(z())], None);
    sole_is(defs(), &[N, L1], &[], root(SU, &[&[N, ZS]]));
    sole_is(defs(), &[N, L1], &[s(z())], None);
    sole_is(defs(), &[N, L1], &[s(s(z()))], root(SU, &[&[N, ZS]]));
}

// Two sorts.

#[test]
fn a_second_sort_refuses_a_root() {
    sole_is(hn(), &[N, PS], &[], root(SU, &[&[N]]));
    sole_is(hn(), &[N, P2], &[], root(SU, &[&[N, PS]]));
    sole_is(hn(), &[N, OD], &[], root(SU, &[&[N, E]]));
    sole_is(nats(), &[N, ZS], &[], root(Z, &[]));
    sole_is(nats(), &[N, ZS], &[z()], None);
}

#[test]
fn two_sorts_with_the_same_two_roots() {
    sole_is(hn(), &[N, E], &[], None);
    sole_is(hn(), &[N, E], &[z()], root(SU, &[&[N, OD]]));
}

#[test]
fn two_sorts_that_share_one_root() {
    sole_is(fe(), &[A, A2], &[], root(F, &[&[N]]));
}

// Declarations as they are read.

#[test]
fn the_first_case_of_a_root_is_the_one_read() {
    let defs = || with(nats(), vec![(A, cases(vec![(F, vec![Some(ZS)]), (F, vec![Some(N)])]))]);
    sole_is(defs(), &[A], &[], root(F, &[&[ZS]]));
    sole_is(defs(), &[A], &[f1(z())], None);
}

#[test]
fn the_first_declaration_of_a_name_is_the_one_read() {
    let defs = vec![(A, zero()), (A, nat(A)), (OS, one(O, vec![]))];
    sole_is(defs, &[A], &[], root(Z, &[]));
}

// Calls one after another, and tables.

#[test]
fn the_same_call_three_times_gives_the_same_answer() {
    let mut f = fx(nats());
    for _ in 0..3 {
        assert_eq!(f.sole(&[N], &[z()]), root(SU, &[&[N]]));
        assert_eq!(f.sole(&[N], &[]), None);
        assert_eq!(f.sole(&[ZS], &[z()]), None);
    }
}

#[test]
fn what_other_operations_leave_in_the_tables_does_not_matter() {
    let mut f = fx(hn());
    let c = f.conj(&[N, E]);
    let n = f.s.alloc(Node::Sym(PS));
    let g = put_pats(&mut f.s, &[z()]);
    live(&mut f.s, f.decls, f.names, c);
    assert_eq!(f.sole(&[N, E], &[z()]), root(SU, &[&[N, OD]]));
    assert!(!matches!(count(&mut f.s, f.decls, f.names, c), Count::None));
    assert_eq!(f.sole(&[N, E], &[z()]), root(SU, &[&[N, OD]]));
    included(&mut f.s, f.decls, f.names, c, n);
    assert_eq!(f.sole(&[N, E], &[z()]), root(SU, &[&[N, OD]]));
    included_but(&mut f.s, f.decls, f.names, c, n, g);
    assert_eq!(f.sole(&[N, E], &[z()]), root(SU, &[&[N, OD]]));
}

#[test]
fn a_very_deep_removed_term_needs_no_recursion() {
    let mut f = fx(nats());
    let su = f.s.alloc(Node::Sym(SU));
    let zero = f.s.alloc(Node::Sym(Z));
    let mut big = zero;
    for _ in 0..10_000 {
        big = f.s.alloc(Node::App(su, big));
    }
    let nil = f.s.alloc(Node::Nil);
    let only_big = f.s.alloc(Node::App(big, nil));
    let both = f.s.alloc(Node::App(zero, only_big));
    let ps = f.conj(&[PS]);
    let n = f.conj(&[N]);
    let got = sole_root(&mut f.s, f.decls, f.names, ps, only_big);
    assert_eq!(f.read(got), root(SU, &[&[N]]));
    let got = sole_root(&mut f.s, f.decls, f.names, n, both);
    assert_eq!(f.read(got), root(SU, &[&[N]]));
    let got = sole_root(&mut f.s, f.decls, f.names, n, only_big);
    assert_eq!(f.read(got), None);
}

#[test]
fn the_sorts_of_an_argument_are_the_node_of_that_conjunction() {
    let mut f = fx(fd());
    let (_, kids) = f.raw(&[A, ZZ], &[]).expect("one root");
    let first = match f.s.read(kids) {
        Node::App(k, _) => k,
        _ => panic!("no argument"),
    };
    let want = f.conj(&[N, ZS]);
    assert!(f.s.same(first, want));
}

#[test]
fn the_arguments_are_what_a_step_of_the_conjunction_gives() {
    let mut f = fx(fd());
    let c = f.conj(&[A, NA]);
    let (root, kids) = f.raw(&[A, NA], &[]).expect("one root");
    let again = step_conj(&mut f.s, f.decls, f.names, c, root, kids).expect("a step");
    assert!(f.s.same(kids, again));
}

// Properties on small tables.

fn subsets<T: Clone>(xs: &[T], max: usize) -> Vec<Vec<T>> {
    (0..1usize << xs.len())
        .filter(|m| m.count_ones() as usize <= max)
        .map(|m| xs.iter().enumerate().filter(|(i, _)| m >> i & 1 == 1).map(|(_, x)| x.clone()).collect())
        .collect()
}

/// The tables the properties are checked on, each with the terms removed
/// terms are drawn from.
fn tables() -> Vec<(Defs, Vec<P>)> {
    let nums = vec![z(), s(z()), s(s(z())), o()];
    let pairs = vec![f2(z(), z()), f2(z(), o()), f2(o(), z()), f2(s(z()), z()), f2(z(), s(z())), z()];
    let ones = vec![z(), f1(z()), f1(s(z())), pf(F, vec![]), f2(z(), z()), f2(s(z()), z())];
    vec![(hn(), nums.clone()), (anys(), nums), (fd(), pairs), (fe(), ones)]
}

#[test]
fn sole_root_agrees_with_the_reference_on_small_tables() {
    let (mut some, mut none) = (0, 0);
    for (defs, pool) in tables() {
        let mut f = fx(defs);
        for c in subsets(&f.order.clone(), 2) {
            for gone in subsets(&pool, 3) {
                let got = f.sole(&c, &gone);
                assert_eq!(got, f.want(&c, &gone), "{:?} but {:?}", c, gone);
                if got.is_some() {
                    some += 1
                } else {
                    none += 1
                }
            }
        }
    }
    assert!(some > 500 && none > 500, "{} with a root, {} without", some, none);
}

#[test]
fn the_order_and_repeats_of_the_removed_terms_do_not_matter() {
    for (defs, pool) in tables() {
        let mut f = fx(defs);
        for c in subsets(&f.order.clone(), 2) {
            for gone in subsets(&pool, 2) {
                let want = f.sole(&c, &gone);
                let mut back: Vec<P> = gone.iter().rev().cloned().collect();
                assert_eq!(f.sole(&c, &back), want, "{:?} but {:?} reversed", c, gone);
                back.extend(gone.iter().cloned());
                assert_eq!(f.sole(&c, &back), want, "{:?} but {:?} repeated", c, gone);
            }
        }
    }
}

#[test]
fn every_member_left_has_the_root() {
    // The members are looked for among the small terms of the pool's symbols.
    let mut small = vec![z(), o(), pf(F, vec![])];
    for i in 0..3 {
        small.push(s(small[i].clone()));
        small.push(f1(small[i].clone()));
        for j in 0..3 {
            small.push(f2(small[i].clone(), small[j].clone()));
        }
    }
    let mut checked = 0;
    for (defs, pool) in tables() {
        let mut f = fx(defs);
        for c in subsets(&f.order.clone(), 2) {
            for gone in subsets(&pool, 2) {
                let Some((root, kids)) = f.sole(&c, &gone) else { continue };
                for t in &small {
                    if gone.contains(t) || !c.iter().all(|n| f.ss.member(*n, t)) {
                        continue;
                    }
                    let P::F(h, args) = t else { unreachable!() };
                    assert_eq!((*h, args.len()), (root, kids.len()), "{:?} is left in {:?} but {:?}", t, c, gone);
                    checked += 1;
                }
            }
        }
    }
    assert!(checked > 500, "{} members checked", checked);
}

#[test]
fn removing_a_term_outside_the_conjunction_changes_nothing() {
    for (defs, pool) in tables() {
        let mut f = fx(defs);
        for c in subsets(&f.order.clone(), 2) {
            for gone in subsets(&pool, 2) {
                let want = f.sole(&c, &gone);
                for t in &pool {
                    if c.iter().all(|n| f.ss.member(*n, t)) {
                        continue;
                    }
                    let mut more = gone.clone();
                    more.push(t.clone());
                    assert_eq!(f.sole(&c, &more), want, "{:?} but {:?} and {:?}", c, gone, t);
                }
            }
        }
    }
}
