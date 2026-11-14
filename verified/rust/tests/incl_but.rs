//! Whether every member of a conjunction of sorts, but for the ground terms
//! of a list, is in a sort, on the store, against the specification
//! (`inclBut` of `lean/RwLog/Sorts/InclBut.lean`, which for well-formed
//! sorts says: every member of the conjunction that is not a term of the
//! list is in the sort).
//!
//! Every table of sorts here is well formed: each conjunction of its names
//! has no member, one, or infinitely many.

mod common;

use common::sorts::*;
use common::spent;
use rwlog_core::sorts::{count, included, included_but, live, out};
use rwlog_core::store::{Node, Store, TermId};

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
const PS: Name = 115;
const P2: Name = 116;
const P3: Name = 117;
const OS: Name = 118;
const NZ: Name = 119;
const B2: Name = 120;
const GA: Name = 121;
const GB: Name = 122;
const FA: Name = 123;
const FN: Name = 124;
const NA: Name = 125;
const NB: Name = 126;
const NN: Name = 127;
const PP: Name = 128;
const ZZ: Name = 129;
const ZO: Name = 130;
const PZ: Name = 131;
const GZ: Name = 132;
const A4: Name = 133;
const AG: Name = 134;
const N4: Name = 135;
const N42: Name = 136;
const A3: Name = 137;
const N3: Name = 138;
const A1: Name = 139;
const B1: Name = 140;
const AN: Name = 141;
const NC: Name = 142;
const NC2: Name = 143;
const A2: Name = 144;
const M2: Name = 145;
const NS: Name = 146;
const NF1: Name = 147;
const R: Name = 148;
const RN: Name = 149;
const RP: Name = 150;
const RZ: Name = 151;
const M1: Name = 152;
const M3: Name = 153;
const ANY2: Name = 154;
const E2: Name = 155;
const O3: Name = 156;
const E4: Name = 157;
const X2: Name = 158;
const Y3: Name = 159;
const X3: Name = 160;
const LP: Name = 161;
const NL: Name = 162;
const L3: Name = 163;
const L3P: Name = 164;
const TR: Name = 165;
const TN: Name = 166;
const T2: Name = 167;
const NZO: Name = 168;
const R2: Name = 169;

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

/// Every term.
fn any() -> Def {
    rest(vec![], vec![], None)
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

/// Every term, every term but `z`, two constants and the naturals.
fn anys() -> Defs {
    vec![
        (ANY, any()),
        (NZ, rest(vec![], vec![(Z, 0)], None)),
        (ZS, zero()),
        (OS, one(O, vec![])),
        (N, nat(N)),
    ]
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

fn nil() -> P {
    pf(NI, vec![])
}

fn cons(a: P, b: P) -> P {
    pf(CO, vec![a, b])
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

    fn but(&mut self, c: &[Name], n: Name, gone: &[P]) -> bool {
        let c = self.conj(c);
        let n = self.name(n);
        let g = put_pats(&mut self.s, gone);
        included_but(&mut self.s, self.decls, self.names, c, n, g)
    }

    fn ticks(&mut self, c: &[Name], n: Name, gone: &[P]) -> (bool, u64) {
        let c = self.conj(c);
        let n = self.name(n);
        let g = put_pats(&mut self.s, gone);
        let (decls, names) = (self.decls, self.names);
        spent(&mut self.s, |s| included_but(s, decls, names, c, n, g))
    }
}

/// The answer the meaning gives, written by hand, is the answer of the
/// reference model and of the store.
fn but_is(defs: Defs, c: &[Name], n: Name, gone: &[P], want: bool) {
    let mut f = fx(defs);
    let set: Conj = c.iter().copied().collect();
    assert_eq!(
        f.ss.included_but(&set, n, gone),
        want,
        "the reference model on c={c:?} n={n} gone={gone:?}"
    );
    assert_eq!(f.but(c, n, gone), want, "the store on c={c:?} n={n} gone={gone:?}");
}

// Nothing removed.

#[test]
fn nothing_removed_a_sort_is_in_itself() {
    but_is(vec![(N, nat(N))], &[N], N, &[], true);
}

#[test]
fn nothing_removed_naturals_are_not_all_positive() {
    but_is(nats(), &[N], PS, &[], false);
}

#[test]
fn nothing_removed_a_dead_conjunction_is_in_an_undeclared_sort() {
    but_is(vec![(D, dead())], &[D], Q, &[], true);
}

#[test]
fn nothing_removed_every_term_is_in_any_and_not_in_one_constant() {
    but_is(anys(), &[], ANY, &[], true);
    but_is(anys(), &[], ZS, &[], false);
}

// The root is refused by the sort.

#[test]
fn removing_zero_puts_the_naturals_in_the_positives() {
    but_is(nats(), &[N], PS, &[z()], true);
}

#[test]
fn removing_a_term_already_in_the_sort_does_not_help() {
    but_is(nats(), &[N], PS, &[s(z())], false);
}

#[test]
fn removing_more_than_needed_is_harmless() {
    but_is(nats(), &[N], PS, &[s(z()), z()], true);
}

#[test]
fn removing_the_counterexample_twice() {
    but_is(nats(), &[N], PS, &[z(), z()], true);
}

#[test]
fn removing_a_term_outside_the_conjunction_does_not_help() {
    but_is(nats(), &[N], PS, &[o()], false);
    but_is(nats(), &[N], PS, &[o(), z()], true);
}

#[test]
fn the_one_member_removed_puts_a_constant_in_another_constant() {
    but_is(nats(), &[ZS], OS, &[z()], true);
    but_is(nats(), &[ZS], OS, &[o()], false);
}

#[test]
fn a_one_member_sort_but_its_member_is_in_an_undeclared_sort() {
    but_is(nats(), &[ZS], Q, &[z()], true);
}

#[test]
fn finitely_many_removed_do_not_put_the_naturals_in_an_undeclared_or_dead_sort() {
    but_is(nats(), &[N], Q, &[z(), s(z()), s(s(z()))], false);
    but_is(nats(), &[N], D, &[z()], false);
    but_is(nats(), &[ZS], D, &[z()], true);
}

fn f_of_zero() -> Defs {
    with(nats(), vec![(A, one(F, vec![Some(ZS)]))])
}

#[test]
fn a_refused_root_whose_one_argument_has_one_member() {
    but_is(f_of_zero(), &[A], D, &[pf(F, vec![z()])], true);
    but_is(f_of_zero(), &[A], D, &[pf(F, vec![o()])], false);
    but_is(f_of_zero(), &[A], D, &[z()], false);
}

#[test]
fn a_removed_term_with_the_symbol_at_another_arity_is_another_root() {
    but_is(f_of_zero(), &[A], D, &[pf(F, vec![z(), z()])], false);
    but_is(f_of_zero(), &[A], D, &[pf(F, vec![])], false);
}

#[test]
fn a_refused_root_whose_argument_has_many_members_cannot_be_removed() {
    let defs = with(nats(), vec![(A, one(F, vec![Some(N)]))]);
    but_is(defs, &[A], D, &[pf(F, vec![z()])], false);
}

#[test]
fn a_refused_root_whose_argument_is_any_term_cannot_be_removed() {
    let defs = with(nats(), vec![(A, one(F, vec![None]))]);
    but_is(defs, &[A], D, &[pf(F, vec![z()])], false);
}

#[test]
fn a_refused_root_with_two_one_member_arguments_in_order() {
    let defs = || with(nats(), vec![(A, one(F, vec![Some(ZS), Some(OS)]))]);
    but_is(defs(), &[A], D, &[pf(F, vec![z(), o()])], true);
    but_is(defs(), &[A], D, &[pf(F, vec![o(), z()])], false);
}

#[test]
fn a_refused_root_with_three_one_member_arguments() {
    let defs = || with(nats(), vec![(A, one(H, vec![Some(ZS), Some(OS), Some(ZS)]))]);
    but_is(defs(), &[A], D, &[pf(H, vec![z(), o(), z()])], true);
    but_is(defs(), &[A], D, &[pf(H, vec![z(), z(), o()])], false);
}

#[test]
fn a_refused_root_with_one_argument_of_many_members_among_one_member_ones() {
    let defs = with(nats(), vec![(A, one(F, vec![Some(ZS), Some(N)]))]);
    but_is(defs, &[A], D, &[pf(F, vec![z(), z()])], false);
}

#[test]
fn the_one_member_is_a_deep_term() {
    let defs = || with(nats(), vec![(A, one(F, vec![Some(B)])), (B, one(G, vec![Some(ZS)]))]);
    but_is(defs(), &[A], D, &[pf(F, vec![pf(G, vec![z()])])], true);
    but_is(defs(), &[A], D, &[pf(F, vec![pf(G, vec![o()])])], false);
    but_is(defs(), &[A], D, &[pf(G, vec![z()])], false);
}

// One argument position.

fn fc() -> Defs {
    with(
        nats(),
        vec![
            (A, one(F, vec![Some(N)])),
            (B, one(F, vec![Some(PS)])),
            (B2, one(F, vec![Some(P2)])),
            (GA, one(G, vec![Some(A)])),
            (GB, one(G, vec![Some(B)])),
        ],
    )
}

#[test]
fn the_one_counterexample_under_an_argument_is_removed() {
    but_is(fc(), &[A], B, &[pf(F, vec![z()])], true);
}

#[test]
fn removing_the_argument_alone_is_not_removing_the_term() {
    but_is(fc(), &[A], B, &[z()], false);
}

#[test]
fn removing_a_sibling_value_that_is_in_the_sort_does_not_help() {
    but_is(fc(), &[A], B, &[pf(F, vec![s(z())])], false);
}

#[test]
fn a_removed_term_with_another_root_is_not_projected() {
    but_is(fc(), &[A], B, &[pf(G, vec![z()])], false);
}

#[test]
fn a_removed_term_with_another_arity_is_not_projected() {
    but_is(fc(), &[A], B, &[pf(F, vec![z(), z()])], false);
    but_is(fc(), &[A], B, &[pf(F, vec![])], false);
}

#[test]
fn a_counterexample_at_depth_three() {
    let t = || pf(G, vec![pf(F, vec![z()])]);
    but_is(fc(), &[GA], GB, &[t()], true);
    but_is(fc(), &[GA], GB, &[pf(F, vec![z()])], false);
    but_is(fc(), &[GA], GB, &[t(), pf(F, vec![z()]), z()], true);
}

#[test]
fn two_counterexamples_one_under_the_other_need_both_removed() {
    but_is(nats(), &[N], P2, &[z()], false);
    but_is(nats(), &[N], P2, &[s(z())], false);
    but_is(nats(), &[N], P2, &[z(), s(z())], true);
    but_is(nats(), &[N], P2, &[s(z()), z()], true);
}

#[test]
fn three_counterexamples_in_a_chain() {
    but_is(nats(), &[N], P3, &[z(), s(z()), s(s(z()))], true);
    but_is(nats(), &[N], P3, &[z(), s(s(z()))], false);
    but_is(nats(), &[N], P3, &[z(), s(z())], false);
}

#[test]
fn two_removed_terms_feed_one_argument_position() {
    but_is(fc(), &[A], B2, &[pf(F, vec![z()]), pf(F, vec![s(z())])], true);
    but_is(fc(), &[A], B2, &[pf(F, vec![z()])], false);
}

#[test]
fn an_argument_the_sort_leaves_free_makes_no_obligation() {
    let defs = with(fc(), vec![(FA, one(F, vec![None]))]);
    but_is(defs, &[A], FA, &[pf(F, vec![z()])], true);
}

#[test]
fn an_argument_of_every_term_but_one() {
    let defs = || {
        with(
            fc(),
            vec![
                (FA, one(F, vec![None])),
                (FN, one(F, vec![Some(NZ)])),
                (NZ, rest(vec![], vec![(Z, 0)], None)),
            ],
        )
    };
    but_is(defs(), &[FA], FN, &[pf(F, vec![z()])], true);
    but_is(defs(), &[FA], FN, &[pf(F, vec![o()])], false);
    but_is(defs(), &[FA], A, &[pf(F, vec![o()])], false);
}

// Several argument positions.

fn fd() -> Defs {
    with(
        nats(),
        vec![
            (A, one(F, vec![Some(N), Some(ZS)])),
            (NA, one(F, vec![Some(PS), None])),
            (B, one(F, vec![Some(OS), Some(N)])),
            (NB, one(F, vec![None, Some(PS)])),
            (NN, one(F, vec![Some(N), Some(N)])),
            (PP, one(F, vec![Some(PS), Some(PS)])),
            (ZZ, one(F, vec![Some(ZS), Some(ZS)])),
            (ZO, one(F, vec![Some(ZS), Some(OS)])),
            (PZ, one(F, vec![Some(PS), Some(ZS)])),
        ],
    )
}

#[test]
fn a_sibling_with_one_member_lets_one_term_be_removed() {
    but_is(fd(), &[A], NA, &[pf(F, vec![z(), z()])], true);
}

#[test]
fn a_removed_term_whose_sibling_is_not_the_one_member_is_not_projected() {
    but_is(fd(), &[A], NA, &[pf(F, vec![z(), o()])], false);
}

#[test]
fn the_failing_position_is_the_last_and_the_sibling_the_first() {
    but_is(fd(), &[B], NB, &[pf(F, vec![o(), z()])], true);
    but_is(fd(), &[B], NB, &[pf(F, vec![z(), o()])], false);
}

#[test]
fn a_sibling_with_many_members_cannot_be_fixed_by_removing_terms() {
    but_is(fd(), &[NN], NA, &[pf(F, vec![z(), z()])], false);
    but_is(fd(), &[NN], NA, &[pf(F, vec![z(), z()]), pf(F, vec![z(), s(z())])], false);
}

#[test]
fn both_positions_fail_with_many_members_each() {
    but_is(fd(), &[NN], PP, &[pf(F, vec![z(), z()])], false);
}

#[test]
fn one_removed_term_serves_both_positions() {
    but_is(fd(), &[ZZ], PP, &[pf(F, vec![z(), z()])], true);
    but_is(fd(), &[ZZ], PP, &[], false);
}

#[test]
fn two_removed_terms_that_each_agree_at_one_position_do_not_remove_their_cross() {
    but_is(fd(), &[ZO], PZ, &[pf(F, vec![s(z()), o()]), pf(F, vec![z(), z()])], false);
}

#[test]
fn siblings_with_many_members_do_no_harm_when_every_position_is_included() {
    but_is(fd(), &[NN], NN, &[pf(F, vec![z(), z()])], true);
}

#[test]
fn the_one_member_of_a_sibling_is_a_compound_term_compared_by_identity() {
    let defs = || {
        with(
            nats(),
            vec![
                (GZ, one(G, vec![Some(ZS)])),
                (A4, one(F, vec![Some(ZS), Some(OS)])),
                (AG, one(F, vec![Some(N), Some(GZ)])),
                (NA, one(F, vec![Some(PS), None])),
                (C, one(G, vec![Some(N), Some(A4)])),
                (M, one(G, vec![Some(PS), None])),
            ],
        )
    };
    but_is(defs(), &[AG], NA, &[pf(F, vec![z(), pf(G, vec![z()])])], true);
    but_is(defs(), &[AG], NA, &[pf(F, vec![z(), pf(G, vec![o()])])], false);
    but_is(defs(), &[AG], NA, &[pf(F, vec![z(), z()])], false);
    but_is(defs(), &[C], M, &[pf(G, vec![z(), pf(F, vec![z(), o()])])], true);
    but_is(defs(), &[C], M, &[pf(G, vec![z(), pf(F, vec![o(), z()])])], false);
}

fn fw() -> Defs {
    with(
        nats(),
        vec![
            (A, one(H, vec![Some(ZS), Some(N), Some(OS)])),
            (NA, one(H, vec![None, Some(PS), None])),
            (A4, one(H, vec![Some(ZS), Some(OS), Some(N), Some(ZS)])),
            (N4, one(H, vec![Some(ZS), Some(OS), Some(PS), Some(ZS)])),
            (N42, one(H, vec![Some(ZS), Some(OS), Some(P2), Some(ZS)])),
            (A3, one(H, vec![Some(N), Some(N), Some(ZS)])),
            (N3, one(H, vec![Some(PS), None, None])),
        ],
    )
}

#[test]
fn three_arguments_with_the_failing_one_in_the_middle() {
    but_is(fw(), &[A], NA, &[pf(H, vec![z(), z(), o()])], true);
    but_is(fw(), &[A], NA, &[pf(H, vec![z(), z(), z()])], false);
    but_is(fw(), &[A], NA, &[pf(H, vec![o(), z(), z()])], false);
}

#[test]
fn four_arguments_where_the_sort_names_a_sort_at_every_position() {
    but_is(fw(), &[A4], N4, &[pf(H, vec![z(), o(), z(), z()])], true);
    but_is(fw(), &[A4], N4, &[pf(H, vec![z(), o(), z(), o()])], false);
}

#[test]
fn four_arguments_with_two_removed_terms_at_one_position() {
    let t0 = || pf(H, vec![z(), o(), z(), z()]);
    but_is(fw(), &[A4], N42, &[t0(), pf(H, vec![z(), o(), s(z()), z()])], true);
    but_is(fw(), &[A4], N42, &[t0(), pf(H, vec![z(), o(), s(z()), o()])], false);
    but_is(fw(), &[A4], N42, &[t0()], false);
}

#[test]
fn three_arguments_with_two_siblings_of_many_members() {
    but_is(fw(), &[A3], N3, &[pf(H, vec![z(), z(), z()])], false);
}

#[test]
fn a_counterexample_at_depth_three_under_several_positions() {
    let defs = || {
        with(
            nats(),
            vec![
                (A, one(G, vec![Some(A1), Some(ZS)])),
                (A1, one(F, vec![Some(ZS), Some(N)])),
                (B, one(G, vec![Some(B1), None])),
                (B1, one(F, vec![None, Some(PS)])),
                (AN, one(G, vec![Some(A1), Some(N)])),
            ],
        )
    };
    but_is(defs(), &[A], B, &[pf(G, vec![pf(F, vec![z(), z()]), z()])], true);
    but_is(defs(), &[A], B, &[pf(G, vec![pf(F, vec![z(), z()]), o()])], false);
    but_is(defs(), &[A], B, &[pf(G, vec![pf(F, vec![o(), z()]), z()])], false);
    but_is(defs(), &[AN], B, &[pf(G, vec![pf(F, vec![z(), z()]), z()])], false);
}

// Several keys; one symbol at several arities.

fn fe() -> Defs {
    with(
        nats(),
        vec![
            (A, cases(vec![(Z, vec![]), (F, vec![Some(N)])])),
            (NA, one(F, vec![Some(PS)])),
            (B, cases(vec![(F, vec![]), (F, vec![Some(N)])])),
            (NB, one(F, vec![Some(N)])),
            (C, cases(vec![(F, vec![Some(ZS)]), (F, vec![Some(N), Some(ZS)])])),
            (NC, one(F, vec![Some(N), None])),
            (NC2, one(F, vec![Some(PS), None])),
            (A2, cases(vec![(F, vec![Some(N)]), (G, vec![Some(N)])])),
            (M2, cases(vec![(F, vec![Some(PS)]), (G, vec![Some(PS)])])),
        ],
    )
}

#[test]
fn a_refused_root_and_a_failing_argument_at_another_root_need_both_removed() {
    but_is(fe(), &[A], NA, &[z(), pf(F, vec![z()])], true);
    but_is(fe(), &[A], NA, &[z()], false);
    but_is(fe(), &[A], NA, &[pf(F, vec![z()])], false);
}

#[test]
fn two_roots_each_with_a_failing_argument() {
    but_is(fe(), &[A2], M2, &[pf(F, vec![z()]), pf(G, vec![z()])], true);
    but_is(fe(), &[A2], M2, &[pf(F, vec![z()])], false);
    but_is(fe(), &[A2], M2, &[pf(G, vec![z()])], false);
    but_is(fe(), &[A2], M2, &[pf(F, vec![z()]), pf(G, vec![s(z())])], false);
}

#[test]
fn the_same_symbol_with_no_argument_and_with_one() {
    but_is(fe(), &[B], NB, &[pf(F, vec![])], true);
    but_is(fe(), &[B], NB, &[pf(F, vec![z()])], false);
}

#[test]
fn the_same_symbol_with_one_argument_and_with_two() {
    but_is(fe(), &[C], NC, &[pf(F, vec![z()])], true);
    but_is(fe(), &[C], NC, &[pf(F, vec![z(), z()])], false);
    but_is(fe(), &[C], NC2, &[pf(F, vec![z()]), pf(F, vec![z(), z()])], true);
    but_is(fe(), &[C], NC2, &[pf(F, vec![z()])], false);
    but_is(fe(), &[C], NC2, &[pf(F, vec![z(), z()])], false);
}

// A conjunction with no member, at the top or at an argument.

#[test]
fn a_dead_conjunction_is_in_every_sort_whatever_is_removed() {
    but_is(vec![(D, dead())], &[D], Q, &[z()], true);
    but_is(with(eo(), vec![(D, dead())]), &[E, OD], D, &[z()], true);
}

#[test]
fn an_undeclared_name_in_the_conjunction_makes_it_empty() {
    let defs = || vec![(A, one(F, vec![Some(Q)])), (ZS, zero()), (D, dead())];
    but_is(defs(), &[Q], ZS, &[z()], true);
    but_is(defs(), &[A], ZS, &[pf(F, vec![z()])], true);
    but_is(defs(), &[ZS, Q], D, &[o()], true);
}

#[test]
fn a_root_with_a_dead_argument_is_no_member_and_asks_nothing() {
    let defs = || {
        vec![
            (A, cases(vec![(Z, vec![]), (F, vec![Some(D)])])),
            (D, dead()),
            (OS, one(O, vec![])),
        ]
    };
    but_is(defs(), &[A], OS, &[z()], true);
    but_is(defs(), &[A], OS, &[], false);
    but_is(defs(), &[A], OS, &[pf(F, vec![z()])], false);
}

#[test]
fn an_argument_conjunction_with_no_member_under_two_sorts() {
    let defs = || {
        with(
            eo(),
            vec![
                (A, cases(vec![(Z, vec![]), (F, vec![Some(E)])])),
                (B, cases(vec![(Z, vec![]), (F, vec![Some(OD)])])),
                (N, nat(N)),
                (PS, one(SU, vec![Some(N)])),
            ],
        )
    };
    but_is(defs(), &[A, B], PS, &[z()], true);
    but_is(defs(), &[A, B], PS, &[pf(F, vec![z()])], false);
}

#[test]
fn a_root_one_sort_of_the_conjunction_refuses_is_not_asked_about() {
    let defs =
        || vec![(N, nat(N)), (NS, rest(vec![], vec![(SU, 1)], None)), (OS, one(O, vec![]))];
    but_is(defs(), &[N, NS], OS, &[z()], true);
    but_is(defs(), &[N, NS], OS, &[s(z())], false);
}

#[test]
fn a_conjunction_of_zero_and_positive_is_empty() {
    but_is(nats(), &[ZS, PS], P2, &[z()], true);
}

// Rests, excluded roots, roots no declaration names.

#[test]
fn fresh_roots_cannot_all_be_removed() {
    but_is(anys(), &[ANY], ZS, &[o()], false);
    but_is(anys(), &[ANY], ZS, &[o(), pf(CA, vec![]), pf(CB, vec![])], false);
}

#[test]
fn every_term_is_in_every_term_whatever_is_removed() {
    but_is(anys(), &[ANY], ANY, &[z()], true);
}

#[test]
fn every_term_but_the_one_excluded_root() {
    but_is(anys(), &[ANY], NZ, &[z()], true);
    but_is(anys(), &[ANY], NZ, &[o()], false);
    but_is(anys(), &[ANY], NZ, &[], false);
    but_is(anys(), &[ANY], NZ, &[pf(Z, vec![z()])], false);
    but_is(anys(), &[], NZ, &[z()], true);
    but_is(anys(), &[], ZS, &[z()], false);
}

#[test]
fn a_removed_term_with_a_root_no_declaration_names_is_accepted_by_the_rest_of_the_sort() {
    but_is(anys(), &[ANY], NZ, &[z(), pf(CA, vec![z()])], true);
}

#[test]
fn an_excluded_root_with_free_arguments_cannot_be_removed() {
    let defs = || {
        vec![
            (ANY, any()),
            (NF1, rest(vec![], vec![(F, 1)], None)),
            (ZS, zero()),
            (A, rest(vec![(F, vec![Some(ZS)])], vec![], None)),
            (N, nat(N)),
        ]
    };
    but_is(defs(), &[ANY], NF1, &[pf(F, vec![z()])], false);
    but_is(defs(), &[A], NF1, &[pf(F, vec![z()])], true);
    but_is(defs(), &[A], NF1, &[pf(F, vec![o()])], false);
    but_is(defs(), &[N], NF1, &[z()], true);
}

#[test]
fn a_rest_of_the_sort_that_asks_a_sort_fails_at_fresh_roots() {
    let defs = vec![(ANY, any()), (R, rest(vec![], vec![], Some(ZS))), (ZS, zero())];
    but_is(defs, &[ANY], R, &[pf(F, vec![o()])], false);
}

#[test]
fn rests_are_compared_by_the_sorts_they_ask() {
    let defs = || {
        vec![
            (RN, rest(vec![], vec![], Some(N))),
            (RP, rest(vec![], vec![], Some(PS))),
            (N, nat(N)),
            (PS, one(SU, vec![Some(N)])),
            (NF1, rest(vec![], vec![(F, 1)], None)),
        ]
    };
    but_is(defs(), &[RN], RP, &[pf(F, vec![z()])], false);
    but_is(defs(), &[RP], RN, &[pf(F, vec![z()])], true);
    but_is(defs(), &[RN], NF1, &[pf(F, vec![z()])], false);
}

#[test]
fn a_case_beside_the_rest_has_the_one_counterexample() {
    let defs = || {
        vec![
            (C, rest(vec![(F, vec![Some(ZS)])], vec![], Some(N))),
            (M, rest(vec![(F, vec![Some(PS)])], vec![], Some(N))),
            (N, nat(N)),
            (PS, one(SU, vec![Some(N)])),
            (ZS, zero()),
        ]
    };
    but_is(defs(), &[C], M, &[pf(F, vec![z()])], true);
    but_is(defs(), &[C], M, &[pf(F, vec![s(z())])], false);
    but_is(defs(), &[C], M, &[pf(G, vec![z()])], false);
    but_is(defs(), &[C], M, &[pf(F, vec![z()]), pf(G, vec![z()]), pf(CA, vec![])], true);
}

#[test]
fn a_case_of_the_sort_met_through_the_rest_of_the_conjunction() {
    let defs = || {
        vec![
            (RN, rest(vec![], vec![], Some(N))),
            (M, rest(vec![(F, vec![Some(PS)])], vec![], Some(N))),
            (M2, rest(vec![(F, vec![Some(PS), None])], vec![], Some(N))),
            (N, nat(N)),
            (PS, one(SU, vec![Some(N)])),
        ]
    };
    but_is(defs(), &[RN], M, &[pf(F, vec![z()])], true);
    but_is(defs(), &[RN], M, &[pf(G, vec![z()])], false);
    but_is(defs(), &[RN], M2, &[pf(F, vec![z(), z()])], false);
}

#[test]
fn a_conjunction_has_fresh_roots_only_when_every_sort_has_a_rest() {
    but_is(anys(), &[ANY, ZS], OS, &[z()], true);
}

#[test]
fn a_case_of_the_sort_overrides_its_own_exclusion() {
    let defs = vec![(ANY, any()), (M, rest(vec![(Z, vec![])], vec![(Z, 0)], None))];
    but_is(defs, &[ANY], M, &[o()], true);
}

#[test]
fn an_excluded_root_that_the_conjunction_excludes_too() {
    let defs = || {
        vec![
            (NZ, rest(vec![], vec![(Z, 0)], None)),
            (NZO, rest(vec![], vec![(Z, 0), (O, 0)], None)),
        ]
    };
    but_is(defs(), &[NZ], NZO, &[o()], true);
    but_is(defs(), &[NZ], NZO, &[z()], false);
}

#[test]
fn an_excluded_root_whose_arguments_have_one_member_by_the_rest_of_the_conjunction() {
    let defs = || {
        vec![
            (RZ, rest(vec![], vec![], Some(ZS))),
            (ZS, zero()),
            (M1, rest(vec![], vec![(F, 1)], Some(ZS))),
            (M2, rest(vec![], vec![(F, 2)], Some(ZS))),
        ]
    };
    but_is(defs(), &[RZ], M1, &[pf(F, vec![z()])], true);
    but_is(defs(), &[RZ], M2, &[pf(F, vec![z(), z()])], true);
    but_is(defs(), &[RZ], M2, &[pf(F, vec![z()])], false);
}

#[test]
fn a_rest_whose_argument_sort_is_dead_has_only_constants() {
    let defs = || {
        vec![
            (C, rest(vec![(Z, vec![])], vec![], Some(D))),
            (D, dead()),
            (NZ, rest(vec![], vec![(Z, 0)], None)),
            (ZS, zero()),
            (R, rest(vec![], vec![], Some(ZS))),
            (NF1, rest(vec![], vec![(F, 1)], None)),
        ]
    };
    but_is(defs(), &[C], NZ, &[z()], true);
    but_is(defs(), &[C], ZS, &[z()], false);
    but_is(defs(), &[C], R, &[z()], true);
    but_is(defs(), &[C], NF1, &[pf(F, vec![z()])], true);
}

#[test]
fn a_case_and_a_rest_of_two_sorts_join_at_an_argument() {
    let defs = || {
        vec![
            (A, one(F, vec![Some(N)])),
            (R2, rest(vec![], vec![(SU, 1)], Some(ZS))),
            (B, one(F, vec![Some(PS)])),
            (N, nat(N)),
            (PS, one(SU, vec![Some(N)])),
            (ZS, zero()),
            (D, dead()),
        ]
    };
    but_is(defs(), &[A, R2], B, &[pf(F, vec![z()])], true);
    but_is(defs(), &[A, R2], D, &[pf(F, vec![z()])], true);
    but_is(defs(), &[A], D, &[pf(F, vec![z()])], false);
}

#[test]
fn every_term_against_a_case_of_the_sort_under_its_rest() {
    let defs = || {
        vec![
            (NZ, rest(vec![], vec![(Z, 0)], None)),
            (M, rest(vec![(F, vec![Some(NZ)])], vec![], None)),
            (M2, rest(vec![(F, vec![Some(NZ), None])], vec![], None)),
            (ANY, any()),
            (ANY2, any()),
            (M3, rest(vec![], vec![], Some(ANY2))),
        ]
    };
    but_is(defs(), &[], M, &[pf(F, vec![z()])], true);
    but_is(defs(), &[ANY], M, &[pf(F, vec![z()])], true);
    but_is(defs(), &[], M2, &[pf(F, vec![z(), z()])], false);
    but_is(defs(), &[ANY], M3, &[z()], true);
}

// Conjunctions of two and three sorts.

fn hn() -> Defs {
    with(nats(), eo())
}

#[test]
fn a_second_sort_in_the_conjunction_removes_a_counterexample() {
    but_is(hn(), &[N, E], PS, &[z()], true);
    but_is(hn(), &[N, E], P2, &[z()], true);
    but_is(hn(), &[N], P2, &[z()], false);
    but_is(hn(), &[N, E], OD, &[z()], false);
    but_is(hn(), &[E, N, PS], P2, &[s(z())], true);
    but_is(hn(), &[N, PS], D, &[s(z())], false);
}

#[test]
fn three_sorts_make_a_sibling_have_one_member() {
    let defs = || {
        with(
            eo(),
            vec![
                (N, nat(N)),
                (PS, one(SU, vec![Some(N)])),
                (ZS, zero()),
                (NS, rest(vec![], vec![(SU, 1)], None)),
                (A, one(F, vec![Some(N), None])),
                (B, one(F, vec![Some(E), Some(ZS)])),
                (C, one(F, vec![None, Some(N)])),
                (A2, one(F, vec![None, Some(NS)])),
                (M, one(F, vec![Some(PS), None])),
            ],
        )
    };
    but_is(defs(), &[A, B, C], M, &[pf(F, vec![z(), z()])], true);
    but_is(defs(), &[A, C], M, &[pf(F, vec![z(), z()])], false);
    but_is(defs(), &[C, A2], M, &[pf(F, vec![z(), z()])], false);
    but_is(defs(), &[A, C, A2], M, &[pf(F, vec![z(), z()])], true);
}

// Recursion.

#[test]
fn finitely_many_removed_of_infinitely_many_counterexamples() {
    but_is(hn(), &[N], E, &[s(z()), s(s(s(z())))], false);
    but_is(eo(), &[E], OD, &[z()], false);
    but_is(nats(), &[N], N, &[s(z())], true);
    but_is(vec![(N, nat(N)), (M, nat(M))], &[N], M, &[z()], true);
}

#[test]
fn mutual_recursion_with_two_counterexamples() {
    let defs = || {
        with(
            eo(),
            vec![
                (E2, one(SU, vec![Some(OD)])),
                (O3, one(SU, vec![Some(E2)])),
                (E4, one(SU, vec![Some(O3)])),
            ],
        )
    };
    but_is(defs(), &[E], E4, &[z(), s(s(z()))], true);
    but_is(defs(), &[E], E4, &[z()], false);
    but_is(defs(), &[E], E4, &[s(s(z()))], false);
    but_is(defs(), &[E], E4, &[z(), s(z()), s(s(z()))], true);
    but_is(defs(), &[E], E4, &[z(), s(s(s(s(z()))))], false);
}

#[test]
fn mutual_recursion_through_two_roots() {
    let defs = || {
        vec![
            (X, cases(vec![(Z, vec![]), (F, vec![Some(Y)])])),
            (Y, one(G, vec![Some(X)])),
            (X2, one(F, vec![Some(Y)])),
            (Y3, one(G, vec![Some(X2)])),
            (X3, one(F, vec![Some(Y3)])),
        ]
    };
    let fg = || pf(F, vec![pf(G, vec![z()])]);
    but_is(defs(), &[X], X2, &[z()], true);
    but_is(defs(), &[X], X3, &[z(), fg()], true);
    but_is(defs(), &[X], X3, &[z()], false);
    but_is(defs(), &[X], X3, &[fg()], false);
    but_is(defs(), &[X], X3, &[z(), pf(G, vec![z()]), fg()], true);
}

#[test]
fn lists_and_trees() {
    let defs = || {
        vec![
            (N, nat(N)),
            (PS, one(SU, vec![Some(N)])),
            (L1, cases(vec![(NI, vec![]), (CO, vec![Some(N), Some(L1)])])),
            (L2, one(CO, vec![Some(N), Some(L1)])),
            (LP, cases(vec![(NI, vec![]), (CO, vec![Some(PS), Some(LP)])])),
            (NL, one(NI, vec![])),
            (L3, one(CO, vec![Some(N), Some(NL)])),
            (L3P, one(CO, vec![Some(PS), Some(NL)])),
            (TR, cases(vec![(CA, vec![]), (F, vec![Some(TR), Some(TR)])])),
            (TN, one(F, vec![Some(TR), Some(TR)])),
            (T2, cases(vec![(CA, vec![]), (F, vec![Some(TN), Some(TR)])])),
        ]
    };
    but_is(defs(), &[L1], L2, &[nil()], true);
    but_is(defs(), &[L1], L2, &[cons(z(), nil())], false);
    but_is(defs(), &[L1], LP, &[cons(z(), nil())], false);
    but_is(defs(), &[L3], L3P, &[cons(z(), nil())], true);
    but_is(defs(), &[L3], L3P, &[cons(z(), cons(z(), nil()))], false);
    but_is(defs(), &[TR], TN, &[pf(CA, vec![])], true);
    but_is(defs(), &[TR], T2, &[pf(F, vec![pf(CA, vec![]), pf(CA, vec![])])], false);
}

// Declarations read as the store reads them.

#[test]
fn the_first_declaration_of_a_name_declared_twice_is_read() {
    let mut f = fx(vec![(A, zero()), (A, nat(A)), (D, dead())]);
    assert!(f.but(&[A], D, &[z()]));
}

#[test]
fn the_first_of_duplicate_cases_is_read() {
    let defs = || {
        with(
            nats(),
            vec![
                (A, cases(vec![(F, vec![Some(ZS)]), (F, vec![Some(N)])])),
                (C, one(F, vec![Some(N)])),
                (M, cases(vec![(F, vec![Some(PS)]), (F, vec![Some(N)])])),
            ],
        )
    };
    assert!(fx(defs()).but(&[A], D, &[pf(F, vec![z()])]));
    assert!(!fx(defs()).but(&[C], M, &[pf(F, vec![s(z())])]));
    assert!(fx(defs()).but(&[C], M, &[pf(F, vec![z()])]));
}

#[test]
fn a_symbol_numbered_like_a_sort_name_is_only_a_symbol() {
    but_is(nats(), &[N], PS, &[pf(N, vec![])], false);
    but_is(nats(), &[N], PS, &[z(), pf(N, vec![])], true);
    but_is(anys(), &[ANY], NZ, &[z(), pf(ANY, vec![]), pf(NZ, vec![z()])], true);
    but_is(anys(), &[ANY], NZ, &[pf(NZ, vec![])], false);
}

/// `s` applied `k` times to `z`, built without recursion.
fn deep(st: &mut Store, k: usize) -> TermId {
    let su = st.alloc(Node::Sym(SU));
    let mut t = st.alloc(Node::Sym(Z));
    for _ in 0..k {
        t = st.alloc(Node::App(su, t));
    }
    t
}

#[test]
fn a_very_deep_removed_term_needs_no_recursion() {
    let mut f = fx(nats());
    let c = f.conj(&[N]);
    let n = f.name(PS);
    let big = deep(&mut f.s, 10_000);
    let zero = deep(&mut f.s, 0);
    let nil = f.s.alloc(Node::Nil);
    let only_big = f.s.alloc(Node::App(big, nil));
    let both = f.s.alloc(Node::App(zero, only_big));
    assert!(included_but(&mut f.s, f.decls, f.names, c, n, both));
    assert!(!included_but(&mut f.s, f.decls, f.names, c, n, only_big));
}

// The store afterwards.

#[test]
fn included_but_leaves_the_stack_empty() {
    let mut f = fx(nats());
    assert!(f.but(&[N], P2, &[z(), s(z())]));
    assert!(f.s.pop().is_none());
    assert!(!f.but(&[N], P2, &[z()]));
    assert!(f.s.pop().is_none());
}

#[test]
fn included_but_gives_the_same_answer_when_called_again() {
    let mut f = fx(fd());
    for _ in 0..3 {
        assert!(f.but(&[A], NA, &[pf(F, vec![z(), z()])]));
        assert!(!f.but(&[NN], NA, &[pf(F, vec![z(), z()])]));
        assert!(f.but(&[ZZ], PP, &[pf(F, vec![z(), z()])]));
    }
}

#[test]
fn included_but_is_not_disturbed_by_what_other_questions_leave_in_the_tables() {
    let mut f = fx(hn());
    let c = f.conj(&[N]);
    let e = f.conj(&[E]);
    let p2 = f.name(P2);
    let (decls, names) = (f.decls, f.names);
    assert!(live(&mut f.s, decls, names, c));
    assert!(f.but(&[N], P2, &[z(), s(z())]));
    assert!(!included(&mut f.s, decls, names, c, p2));
    assert!(!f.but(&[N], P2, &[s(z())]));
    let _ = count(&mut f.s, decls, names, e);
    assert!(f.but(&[N, E], P2, &[z()]));
    assert!(out(&mut f.s, decls, names, c, p2));
    assert!(f.but(&[N], P3, &[z(), s(z()), s(s(z()))]));
}

// Properties, over every conjunction and sort of a table and lists of
// small terms.

fn subsets<T: Clone>(xs: &[T], max: usize) -> Vec<Vec<T>> {
    (0..1usize << xs.len())
        .filter(|m| m.count_ones() as usize <= max)
        .map(|m| xs.iter().enumerate().filter(|(i, _)| m >> i & 1 == 1).map(|(_, x)| x.clone()).collect())
        .collect()
}

/// `z`, `o`, and `s` applied up to four times to either.
fn small_terms() -> Vec<P> {
    let mut out = vec![z(), o()];
    for i in 0..8 {
        out.push(s(out[i].clone()));
    }
    out
}

/// The tables the properties are checked on, each with the terms removed
/// terms are drawn from.
fn tables() -> Vec<(Defs, Vec<P>)> {
    let nums = vec![z(), s(z()), s(s(z())), o()];
    let pairs = vec![
        pf(F, vec![z(), z()]),
        pf(F, vec![z(), o()]),
        pf(F, vec![o(), z()]),
        pf(F, vec![s(z()), z()]),
        pf(F, vec![z(), s(z())]),
        z(),
    ];
    vec![(hn(), nums.clone()), (anys(), nums), (fd(), pairs)]
}

#[test]
fn included_but_agrees_with_the_reference_model_on_every_question_of_small_tables() {
    for (defs, pool) in tables() {
        let mut f = fx(defs);
        let mut sorts = f.order.clone();
        sorts.push(Q);
        for c in subsets(&f.order.clone(), 2) {
            let set: Conj = c.iter().copied().collect();
            for &n in &sorts {
                for gone in subsets(&pool, 2) {
                    let want = f.ss.included_but(&set, n, &gone);
                    assert_eq!(f.but(&c, n, &gone), want, "c={c:?} n={n} gone={gone:?}");
                }
            }
        }
    }
}

#[test]
fn nothing_removed_is_inclusion() {
    for (defs, _) in tables() {
        let mut f = fx(defs);
        let mut sorts = f.order.clone();
        sorts.push(Q);
        for c in subsets(&f.order.clone(), 2) {
            for &n in &sorts {
                let ci = f.conj(&c);
                let ni = f.name(n);
                let inc = included(&mut f.s, f.decls, f.names, ci, ni);
                assert_eq!(f.but(&c, n, &[]), inc, "c={c:?} n={n}");
            }
        }
    }
}

#[test]
fn when_the_answer_is_yes_every_small_member_left_is_in_the_sort() {
    let mut f = fx(hn());
    let terms = small_terms();
    let pool = vec![z(), s(z()), s(s(z())), o()];
    let mut sorts = f.order.clone();
    sorts.push(Q);
    for c in subsets(&f.order.clone(), 2) {
        for &n in &sorts {
            for gone in subsets(&pool, 3) {
                if f.but(&c, n, &gone) {
                    for t in &terms {
                        let inside = c.iter().all(|&m| f.ss.member(m, t));
                        assert!(
                            !inside || gone.contains(t) || f.ss.member(n, t),
                            "c={c:?} n={n} gone={gone:?} leaves {t:?} outside"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn removing_a_needed_term_from_the_list_turns_yes_into_no() {
    let mut f = fx(hn());
    let pool = vec![z(), s(z()), s(s(z())), o()];
    for c in subsets(&f.order.clone(), 2) {
        for &n in &f.order.clone() {
            for gone in subsets(&pool, 3) {
                if !f.but(&c, n, &gone) {
                    continue;
                }
                for g in &gone {
                    let needed = c.iter().all(|&m| f.ss.member(m, g)) && !f.ss.member(n, g);
                    if needed {
                        let fewer: Vec<P> = gone.iter().filter(|t| *t != g).cloned().collect();
                        assert!(!f.but(&c, n, &fewer), "c={c:?} n={n} gone={gone:?} without {g:?}");
                    }
                }
            }
        }
    }
}

#[test]
fn the_order_and_the_repeats_of_the_list_do_not_matter() {
    for (defs, pool) in tables() {
        let mut f = fx(defs);
        for c in subsets(&f.order.clone(), 1) {
            for &n in &f.order.clone() {
                for gone in subsets(&pool, 2) {
                    let want = f.but(&c, n, &gone);
                    let mut back = gone.clone();
                    back.reverse();
                    assert_eq!(f.but(&c, n, &back), want, "reversed, c={c:?} n={n} gone={gone:?}");
                    let mut twice = gone.clone();
                    twice.extend(gone.clone());
                    assert_eq!(f.but(&c, n, &twice), want, "doubled, c={c:?} n={n} gone={gone:?}");
                }
            }
        }
    }
}

#[test]
fn adding_terms_to_the_list_keeps_a_yes() {
    for (defs, pool) in tables() {
        let mut f = fx(defs);
        for c in subsets(&f.order.clone(), 1) {
            for &n in &f.order.clone() {
                for gone in subsets(&pool, 2) {
                    if f.but(&c, n, &gone) {
                        for extra in &pool {
                            let mut more = gone.clone();
                            more.push(extra.clone());
                            assert!(f.but(&c, n, &more), "c={c:?} n={n} gone={gone:?} and {extra:?}");
                        }
                    }
                }
            }
        }
    }
}

// The ticks spent.

#[test]
fn repeated_terms_in_the_list_do_not_multiply_the_ticks() {
    let mut f = fx(nats());
    let (yes, one_copy) = f.ticks(&[N], P3, &[z(), s(z()), s(s(z()))]);
    assert!(yes);
    let mut many = Vec::new();
    for _ in 0..8 {
        many.extend([z(), s(z()), s(s(z()))]);
    }
    let (yes, eight_copies) = f.ticks(&[N], P3, &many);
    assert!(yes);
    assert!(
        eight_copies <= 8 * 8 * one_copy,
        "{eight_copies} ticks for eight copies against {one_copy} for one"
    );
}

#[test]
fn the_ticks_grow_with_the_depth_of_a_removed_term_and_no_faster_than_its_square() {
    let mut f = fx(nats());
    let c = f.conj(&[N]);
    let n = f.name(PS);
    let nil = f.s.alloc(Node::Nil);
    let zero = deep(&mut f.s, 0);
    let mut spent_at = Vec::new();
    for k in [100usize, 200, 400] {
        let big = deep(&mut f.s, k);
        let l = f.s.alloc(Node::App(big, nil));
        let g = f.s.alloc(Node::App(zero, l));
        let (decls, names) = (f.decls, f.names);
        let (yes, t) = spent(&mut f.s, |s| included_but(s, decls, names, c, n, g));
        assert!(yes);
        spent_at.push(t);
    }
    assert!(spent_at[1] <= 4 * spent_at[0] + 1000, "{spent_at:?}");
    assert!(spent_at[2] <= 4 * spent_at[1] + 1000, "{spent_at:?}");
}
