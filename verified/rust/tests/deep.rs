//! No function recurses on a term: each works on terms far deeper than the
//! call stack could follow.

use rwlog_core::span::{act, Act};
use rwlog_core::store::{Node, Store, Tbl, TermId};
use rwlog_core::term::{append, ground, occurs, rebuild, Leaf};

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
fn act_checks_the_occurrence_of_a_variable_in_a_deep_term() {
    let mut s = Store::new();
    let x = s.root();
    let y = var1(&mut s);
    let t = right_spine(&mut s, x);
    assert!(matches!(act(&mut s, x, t), Act::Fail));
    assert!(matches!(act(&mut s, y, t), Act::Elim(_, _)));
}

#[test]
fn ground_of_deep_terms() {
    let mut s = Store::new();
    let x = s.root();
    let c = s.alloc(Node::Sym(1));
    for spine in [right_spine, left_spine] {
        let closed = spine(&mut s, c);
        assert!(ground(&mut s, closed));
        // A variable at the bottom is found.
        let open = spine(&mut s, x);
        assert!(!ground(&mut s, open));
    }
}
