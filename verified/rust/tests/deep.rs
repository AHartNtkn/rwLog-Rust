//! No function recurses on a term: each works on terms far deeper than the
//! call stack could follow.

use rwlog_core::cover::{covers_plain, left_bound, mmatch, right_bound};
use rwlog_core::span::{act, compose, Act, Span};
use rwlog_core::store::{Node, Store, Tbl, TermId};
use rwlog_core::term::{append, occurs, rebuild, Leaf};

const DEPTH: usize = 400_000;

/// `f (f (... (f leaf)))`, with `DEPTH` applications, nested on the right.
fn right_spine(s: &mut Store, leaf: TermId) -> TermId {
    let f = s.alloc(Node::Sym(7));
    let mut t = leaf;
    for _ in 0..DEPTH {
        t = s.alloc(Node::App(f, t));
    }
    t
}

/// `(((leaf f) f) ... f)`, with `DEPTH` applications, nested on the left.
fn left_spine(s: &mut Store, leaf: TermId) -> TermId {
    let f = s.alloc(Node::Sym(7));
    let mut t = leaf;
    for _ in 0..DEPTH {
        t = s.alloc(Node::App(t, f));
    }
    t
}

/// The list of `DEPTH` copies of `m`.
fn long_list(s: &mut Store, m: TermId) -> TermId {
    let mut l = s.alloc(Node::Nil);
    for _ in 0..DEPTH {
        l = s.alloc(Node::App(m, l));
    }
    l
}

fn var1(s: &mut Store) -> TermId {
    let v0 = s.root();
    s.alloc(Node::VR(v0))
}

#[test]
fn rebuild_of_a_term_deep_on_the_right() {
    let mut s = Store::new();
    let x = s.root();
    let t = right_spine(&mut s, x);
    let c = s.alloc(Node::Sym(1));
    let want = right_spine(&mut s, c);
    s.clear(Tbl::A);
    let r = rebuild(&mut s, Leaf::Sub(x, c), t);
    assert!(s.same(r, want));
}

#[test]
fn rebuild_of_a_term_deep_on_the_left() {
    let mut s = Store::new();
    let x = s.root();
    let t = left_spine(&mut s, x);
    let c = s.alloc(Node::Sym(1));
    let want = left_spine(&mut s, c);
    s.clear(Tbl::A);
    let r = rebuild(&mut s, Leaf::Sub(x, c), t);
    assert!(s.same(r, want));
}

#[test]
fn occurs_in_a_deep_term_finds_the_variable_at_the_bottom() {
    let mut s = Store::new();
    let x = s.root();
    let y = var1(&mut s);
    let t = right_spine(&mut s, x);
    let u = left_spine(&mut s, x);
    s.clear(Tbl::B);
    assert!(occurs(&mut s, x, t));
    s.clear(Tbl::B);
    assert!(occurs(&mut s, x, u));
    s.clear(Tbl::B);
    assert!(!occurs(&mut s, y, t));
    s.clear(Tbl::B);
    assert!(!occurs(&mut s, y, u));
}

#[test]
fn append_of_a_long_list() {
    let mut s = Store::new();
    let m = s.alloc(Node::Sym(3));
    let a = long_list(&mut s, m);
    let n = s.alloc(Node::Sym(4));
    let nil = s.alloc(Node::Nil);
    let b = s.alloc(Node::App(n, nil));
    let r = append(&mut s, a, b);
    // The result is `DEPTH` copies of `m` in front of `b`.
    let mut want = b;
    for _ in 0..DEPTH {
        want = s.alloc(Node::App(m, want));
    }
    assert!(s.same(r, want));
}

#[test]
fn mmatch_of_a_deep_pattern() {
    let mut s = Store::new();
    let x = s.root();
    let c = s.alloc(Node::Sym(1));
    let d = s.alloc(Node::Sym(2));
    for spine in [right_spine, left_spine] {
        let p = spine(&mut s, x);
        let t = spine(&mut s, c);
        s.clear(Tbl::A);
        assert!(mmatch(&mut s, p, t));
        // The pattern with a symbol at the bottom does not match the same
        // spine over another symbol.
        let q = spine(&mut s, d);
        s.clear(Tbl::A);
        assert!(!mmatch(&mut s, q, t));
    }
}

#[test]
fn covers_plain_of_deep_spans() {
    let mut s = Store::new();
    let x = s.root();
    let c = s.alloc(Node::Sym(1));
    let p = right_spine(&mut s, x);
    let t = right_spine(&mut s, c);
    let nil = s.alloc(Node::Nil);
    let a = Span { l: p, r: p, c: nil };
    let b = Span { l: t, r: t, c: nil };
    assert!(covers_plain(&mut s, a, b));
    assert!(!covers_plain(&mut s, b, a));
}

#[test]
fn bounds_of_a_span_with_a_deep_side_and_many_deep_constraints() {
    let mut s = Store::new();
    let x = s.root();
    let y = var1(&mut s);
    let l = right_spine(&mut s, x);
    let r = left_spine(&mut s, y);
    // Constraints: many on `x`, each a deep term, and one on `y` at the end.
    let on_x = left_spine(&mut s, x);
    let nil = s.alloc(Node::Nil);
    let last = s.alloc(Node::App(y, nil));
    let mut c = last;
    for _ in 0..DEPTH {
        c = s.alloc(Node::App(on_x, c));
    }
    let sp = Span { l, r, c };
    let lb = left_bound(&mut s, sp).expect("the left side is not a variable");
    let rb = right_bound(&mut s, sp).expect("the right side is not a variable");
    // The left bound keeps the constraints on `x`, the right bound the one on `y`.
    let mut want = nil;
    for _ in 0..DEPTH {
        want = s.alloc(Node::App(on_x, want));
    }
    assert!(s.same(lb.l, l) && s.same(lb.r, l) && s.same(lb.c, want));
    assert!(s.same(rb.l, r) && s.same(rb.r, r) && s.same(rb.c, last));
}

#[test]
fn act_checks_the_occurrence_of_a_variable_in_a_deep_term() {
    let mut s = Store::new();
    let x = s.root();
    let y = var1(&mut s);
    let t = right_spine(&mut s, x);
    assert!(matches!(act(&mut s, x, t), Act::Fail));
    assert!(matches!(act(&mut s, y, t), Act::Elim(_, _)));
}

#[test]
fn compose_through_a_deep_interface() {
    let mut s = Store::new();
    let x = s.root();
    let c = s.alloc(Node::Sym(1));
    let px = right_spine(&mut s, x);
    let pc = right_spine(&mut s, c);
    let nil = s.alloc(Node::Nil);
    // `x -> f^n x` then `f^n c -> c`: the interface binds `x` to `c`.
    let a = Span { l: x, r: px, c: nil };
    let b = Span { l: pc, r: c, c: nil };
    let z = compose(&mut s, a, b).expect("the spans compose");
    assert!(s.same(z.l, c) && s.same(z.r, c) && s.same(z.c, nil));
}
