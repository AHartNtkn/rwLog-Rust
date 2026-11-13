//! Tests of the translated core, run as ordinary Rust. The Lean proofs in
//! `verified/lean` are about the same source.

use rwlog_core::matching::{instantiate, match_into, term_eq, Subst};
use rwlog_core::store::{Node, Store, TermId};

struct Fx {
    s: Store,
}

impl Fx {
    fn new() -> Fx {
        Fx { s: Store::new() }
    }
    fn var(&mut self, v: u32) -> TermId {
        self.s.alloc(Node::Var(v))
    }
    fn sym(&mut self, f: u32) -> TermId {
        self.s.alloc(Node::Sym(f))
    }
    fn app(&mut self, a: TermId, b: TermId) -> TermId {
        self.s.alloc(Node::App(a, b))
    }
    /// Ticks spent by `f`.
    fn spent<R>(&mut self, f: impl FnOnce(&mut Store) -> R) -> (R, u64) {
        let before = self.s.ticks();
        let r = f(&mut self.s);
        (r, self.s.ticks() - before)
    }
}

const A: u32 = 0;
const B: u32 = 1;

#[test]
fn alloc_costs_one_tick_each() {
    let mut fx = Fx::new();
    fx.var(0);
    fx.sym(A);
    assert_eq!(fx.s.ticks(), 2);
}

#[test]
fn same_identifier_is_same_and_costs_one_tick() {
    let mut fx = Fx::new();
    let x = fx.sym(A);
    let y = fx.sym(A);
    let before = fx.s.ticks();
    assert!(fx.s.same(x, x));
    assert!(!fx.s.same(x, y));
    assert_eq!(fx.s.ticks() - before, 2);
}

#[test]
fn term_eq_equal_terms_at_different_nodes() {
    let mut fx = Fx::new();
    let (a1, b1) = (fx.sym(A), fx.var(3));
    let t1 = fx.app(a1, b1);
    let (a2, b2) = (fx.sym(A), fx.var(3));
    let t2 = fx.app(a2, b2);
    let (r, ticks) = fx.spent(|s| term_eq(s, t1, t2));
    assert!(r);
    assert_eq!(ticks, 8, "two reads at each of the three positions, one word comparison at each leaf");
}

#[test]
fn term_eq_different_symbols() {
    let mut fx = Fx::new();
    let (a, b) = (fx.sym(A), fx.sym(B));
    let (r, ticks) = fx.spent(|s| term_eq(s, a, b));
    assert!(!r);
    assert_eq!(ticks, 3, "two reads and one word comparison");
}

#[test]
fn term_eq_variable_is_not_a_symbol_with_the_same_number() {
    let mut fx = Fx::new();
    let (a, b) = (fx.sym(0), fx.var(0));
    assert!(!term_eq(&mut fx.s, a, b));
}

#[test]
fn term_eq_stops_at_the_first_difference() {
    let mut fx = Fx::new();
    let (a1, c) = (fx.sym(A), fx.sym(A));
    let t1 = fx.app(a1, c);
    let (b1, d) = (fx.sym(B), fx.sym(A));
    let t2 = fx.app(b1, d);
    let (r, ticks) = fx.spent(|s| term_eq(s, t1, t2));
    assert!(!r);
    assert_eq!(ticks, 5, "the right arguments are never read");
}

#[test]
fn match_unbound_variable_binds_it_without_reading_the_target() {
    let mut fx = Fx::new();
    let p = fx.var(7);
    let t = fx.sym(A);
    let (r, ticks) = fx.spent(|s| match_into(s, p, t, Subst::new()));
    let th = r.expect("a variable matches anything");
    let u = th.lookup(&mut fx.s, 7).expect("bound");
    assert!(fx.s.same(u, t));
    assert!(th.lookup(&mut fx.s, 8).is_none());
    assert_eq!(ticks, 1);
}

#[test]
fn match_repeated_variable_needs_equal_subterms() {
    let mut fx = Fx::new();
    // pattern ($0 $0)
    let (x, y) = (fx.var(0), fx.var(0));
    let p = fx.app(x, y);
    // (a a) at two different nodes
    let (a1, a2) = (fx.sym(A), fx.sym(A));
    let good = fx.app(a1, a2);
    // (a b)
    let (a3, b) = (fx.sym(A), fx.sym(B));
    let bad = fx.app(a3, b);
    assert!(match_into(&mut fx.s, p, good, Subst::new()).is_some());
    assert!(match_into(&mut fx.s, p, bad, Subst::new()).is_none());
}

#[test]
fn match_target_variables_are_rigid() {
    let mut fx = Fx::new();
    let p = fx.sym(A);
    let t = fx.var(0);
    assert!(match_into(&mut fx.s, p, t, Subst::new()).is_none());
}

#[test]
fn match_same_variable_number_on_both_sides_is_unrelated() {
    let mut fx = Fx::new();
    // pattern ($0 a) against ((b $0) a): $0 of the pattern is bound to (b $0) of the target.
    let (x, a1) = (fx.var(0), fx.sym(A));
    let p = fx.app(x, a1);
    let (b, x2) = (fx.sym(B), fx.var(0));
    let inner = fx.app(b, x2);
    let a2 = fx.sym(A);
    let t = fx.app(inner, a2);
    let th = match_into(&mut fx.s, p, t, Subst::new()).expect("matches");
    let u = th.lookup(&mut fx.s, 0).expect("bound");
    assert!(fx.s.same(u, inner));
}

#[test]
fn match_symbol_against_application_fails() {
    let mut fx = Fx::new();
    let p = fx.sym(A);
    let (a, b) = (fx.sym(A), fx.sym(B));
    let t = fx.app(a, b);
    assert!(match_into(&mut fx.s, p, t, Subst::new()).is_none());
}

#[test]
fn match_application_against_symbol_fails() {
    let mut fx = Fx::new();
    let (a, b) = (fx.sym(A), fx.sym(B));
    let p = fx.app(a, b);
    let t = fx.sym(A);
    assert!(match_into(&mut fx.s, p, t, Subst::new()).is_none());
}

#[test]
fn match_spends_at_most_twice_the_sizes() {
    let mut fx = Fx::new();
    // pattern (($0 $1) $0), size 5; target ((a b) a), size 5.
    let (x, y) = (fx.var(0), fx.var(1));
    let xy = fx.app(x, y);
    let x2 = fx.var(0);
    let p = fx.app(xy, x2);
    let (a, b) = (fx.sym(A), fx.sym(B));
    let ab = fx.app(a, b);
    let a2 = fx.sym(A);
    let t = fx.app(ab, a2);
    let (r, ticks) = fx.spent(|s| match_into(s, p, t, Subst::new()));
    assert!(r.is_some());
    assert!(ticks <= 2 * (5 + 5), "spent {ticks}");
}

#[test]
fn lookup_returns_the_newest_binding() {
    let mut fx = Fx::new();
    let (a, b) = (fx.sym(A), fx.sym(B));
    let th = Subst::new().bind(0, a).bind(0, b);
    let u = th.lookup(&mut fx.s, 0).expect("bound");
    assert!(fx.s.same(u, b));
}

#[test]
fn instantiate_replaces_bound_variables_and_keeps_unbound_ones() {
    let mut fx = Fx::new();
    // ($0 $1) with $0 := a
    let (x, y) = (fx.var(0), fx.var(1));
    let p = fx.app(x, y);
    let a = fx.sym(A);
    let th = Subst::new().bind(0, a);
    let r = instantiate(&mut fx.s, &th, p);
    // expected (a $1)
    let (a2, y2) = (fx.sym(A), fx.var(1));
    let want = fx.app(a2, y2);
    assert!(term_eq(&mut fx.s, r, want));
}

#[test]
fn instantiate_then_match_recovers_the_instance() {
    let mut fx = Fx::new();
    let (x, b) = (fx.var(0), fx.sym(B));
    let p = fx.app(x, b);
    let (a, a2) = (fx.sym(A), fx.sym(A));
    let aa = fx.app(a, a2);
    let th = Subst::new().bind(0, aa);
    let inst = instantiate(&mut fx.s, &th, p);
    let th2 = match_into(&mut fx.s, p, inst, Subst::new()).expect("an instance matches");
    let u = th2.lookup(&mut fx.s, 0).expect("bound");
    assert!(term_eq(&mut fx.s, u, aa));
}
