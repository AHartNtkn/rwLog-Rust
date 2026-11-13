//! The base machine, run as ordinary Rust.

mod common;
use common::*;
use rwlog_core::store::{Frame, Node, Store, Tbl, TermId};

#[test]
fn new_store_has_spent_nothing() {
    let s = Store::new();
    assert_eq!(s.ticks(), 0);
}

#[test]
fn root_is_the_variable_zero() {
    let mut s = Store::new();
    let r = s.root();
    assert!(matches!(s.read(r), Node::V0));
    let z = s.alloc(Node::V0);
    assert!(s.same(z, r));
}

#[test]
fn each_primitive_costs_one_tick() {
    let mut s = Store::new();
    let ((), t) = spent(&mut s, |s| {
        let a = s.alloc(Node::Sym(7));
        s.read(a);
        s.same(a, a);
        s.word_eq(1, 2);
        s.clear(Tbl::A);
        s.set(Tbl::A, a, a);
        s.get(Tbl::A, a);
        s.set_flag(Tbl::B, a, true);
        s.get_flag(Tbl::B, a);
    });
    assert_eq!(t, 9);
}

#[test]
fn alloc_of_a_node_already_there_returns_its_identifier() {
    let mut s = Store::new();
    let f = s.alloc(Node::Sym(3));
    let x = s.alloc(Node::V0);
    let t1 = s.alloc(Node::App(f, x));
    let f2 = s.alloc(Node::Sym(3));
    let t2 = s.alloc(Node::App(f2, x));
    assert!(s.same(f, f2));
    assert!(s.same(t1, t2));
}

#[test]
fn different_nodes_get_different_identifiers() {
    let mut s = Store::new();
    let x = s.root();
    let ids = [
        s.alloc(Node::Sym(0)),
        s.alloc(Node::Sym(1)),
        s.alloc(Node::Sym(16)),
        s.alloc(Node::Sym(17)),
        s.alloc(Node::Sym(256)),
        s.alloc(Node::Sym(u32::MAX)),
        s.alloc(Node::Nil),
        s.alloc(Node::VR(x)),
    ];
    let mut all = vec![x];
    all.extend(ids);
    let a = s.alloc(Node::App(ids[0], ids[1]));
    let b = s.alloc(Node::App(ids[1], ids[0]));
    let c = s.alloc(Node::App(ids[0], ids[0]));
    all.extend([a, b, c]);
    for i in 0..all.len() {
        for j in 0..all.len() {
            assert_eq!(s.same(all[i], all[j]), i == j, "nodes {i} and {j}");
        }
    }
}

#[test]
fn application_keys_do_not_run_together() {
    // (1, 16 + 1) and (16 + 1, 1) and (1 * 16 + 1, ...) must not collide
    // when the digits of the two parts are written one after the other.
    let mut s = Store::new();
    let mut ids = Vec::new();
    for f in 0..40u32 {
        ids.push(s.alloc(Node::Sym(f)));
    }
    let mut apps = Vec::new();
    for &a in &ids {
        for &b in &ids {
            apps.push(s.alloc(Node::App(a, b)));
        }
    }
    for i in 0..apps.len() {
        for j in 0..apps.len() {
            assert_eq!(s.same(apps[i], apps[j]), i == j);
        }
    }
    for (k, &p) in apps.iter().enumerate() {
        match s.read(p) {
            Node::App(a, b) => {
                assert!(s.same(a, ids[k / 40]));
                assert!(s.same(b, ids[k % 40]));
            }
            _ => panic!("not an application"),
        }
    }
}

#[test]
fn left_of_variable_zero_is_variable_zero() {
    let mut s = Store::new();
    let z = s.root();
    let l = s.alloc(Node::VL(z));
    assert!(s.same(l, z));
}

#[test]
fn variables_read_back_as_their_numbers() {
    let mut s = Store::new();
    for n in 0..200u128 {
        let p = put_var(&mut s, n);
        assert_eq!(get(&mut s, p), v(n));
    }
}

#[test]
fn equal_numbers_are_the_same_variable_node() {
    let mut s = Store::new();
    for n in 0..64u128 {
        for m in 0..64u128 {
            let p = put_var(&mut s, n);
            let q = put_var(&mut s, m);
            assert_eq!(s.same(p, q), n == m);
        }
    }
}

#[test]
fn renaming_does_not_overflow_after_many_levels() {
    let mut s = Store::new();
    let mut p = s.root();
    for _ in 0..1000 {
        p = s.alloc(Node::VR(p));
    }
    let mut depth = 0;
    loop {
        match s.read(p) {
            Node::VR(q) => {
                depth += 1;
                p = q;
            }
            Node::V0 => break,
            _ => panic!("not a variable"),
        }
    }
    assert_eq!(depth, 1000);
}

#[test]
#[should_panic]
fn alloc_of_an_application_of_a_node_not_in_the_store_panics() {
    let mut big = Store::new();
    let mut p = big.root();
    for f in 0..10 {
        p = big.alloc(Node::Sym(f));
    }
    let mut s = Store::new();
    let x = s.root();
    s.alloc(Node::App(x, p));
}

#[test]
#[should_panic]
fn alloc_of_a_variable_over_a_symbol_panics() {
    let mut s = Store::new();
    let f = s.alloc(Node::Sym(0));
    s.alloc(Node::VR(f));
}

#[test]
fn a_fresh_node_has_empty_cells() {
    let mut s = Store::new();
    let a = s.alloc(Node::Sym(1));
    assert!(s.get(Tbl::A, a).is_none());
    assert!(s.get(Tbl::B, a).is_none());
    assert!(s.get_flag(Tbl::A, a).is_none());
}

#[test]
fn set_then_get_returns_the_value() {
    let mut s = Store::new();
    let a = s.alloc(Node::Sym(1));
    let b = s.alloc(Node::Sym(2));
    s.set(Tbl::A, a, b);
    let r = s.get(Tbl::A, a).expect("a value");
    assert!(s.same(r, b));
    assert!(s.get(Tbl::A, b).is_none());
}

#[test]
fn set_overwrites() {
    let mut s = Store::new();
    let a = s.alloc(Node::Sym(1));
    let b = s.alloc(Node::Sym(2));
    s.set(Tbl::A, a, b);
    s.set(Tbl::A, a, a);
    let r = s.get(Tbl::A, a).expect("a value");
    assert!(s.same(r, a));
}

#[test]
fn the_two_tables_are_separate() {
    let mut s = Store::new();
    let a = s.alloc(Node::Sym(1));
    s.set(Tbl::A, a, a);
    assert!(s.get(Tbl::B, a).is_none());
    s.set_flag(Tbl::B, a, false);
    assert_eq!(s.get_flag(Tbl::B, a), Some(false));
    assert!(s.get(Tbl::A, a).is_some());
}

#[test]
fn clear_empties_one_table_only() {
    let mut s = Store::new();
    let a = s.alloc(Node::Sym(1));
    s.set(Tbl::A, a, a);
    s.set_flag(Tbl::B, a, true);
    s.clear(Tbl::A);
    assert!(s.get(Tbl::A, a).is_none());
    assert_eq!(s.get_flag(Tbl::B, a), Some(true));
    s.clear(Tbl::B);
    assert!(s.get_flag(Tbl::B, a).is_none());
}

#[test]
fn flags_keep_both_values() {
    let mut s = Store::new();
    let a = s.alloc(Node::Sym(1));
    let b = s.alloc(Node::Sym(2));
    s.set_flag(Tbl::A, a, true);
    s.set_flag(Tbl::A, b, false);
    assert_eq!(s.get_flag(Tbl::A, a), Some(true));
    assert_eq!(s.get_flag(Tbl::A, b), Some(false));
}

#[test]
fn cells_survive_later_allocations() {
    let mut s = Store::new();
    let a = s.alloc(Node::Sym(1));
    s.set(Tbl::A, a, a);
    for f in 2..100 {
        s.alloc(Node::Sym(f));
    }
    assert!(s.get(Tbl::A, a).is_some());
}

/// Is the frame the one with these two nodes, and of this kind?
fn is_frame(s: &mut Store, f: Option<Frame>, a: TermId, b: TermId, build: bool) -> bool {
    match f {
        Some(Frame::Visit(x, y)) => !build && s.same(x, a) && s.same(y, b),
        Some(Frame::Build(x, y)) => build && s.same(x, a) && s.same(y, b),
        None => false,
    }
}

#[test]
fn pop_of_an_empty_stack_is_nothing() {
    let mut s = Store::new();
    assert!(s.pop().is_none());
}

#[test]
fn frames_come_off_the_stack_last_in_first_out() {
    let mut s = Store::new();
    let a = s.alloc(Node::Sym(1));
    let b = s.alloc(Node::Sym(2));
    s.push(Frame::Visit(a, b));
    s.push(Frame::Build(b, a));
    let f = s.pop();
    assert!(is_frame(&mut s, f, b, a, true));
    let f = s.pop();
    assert!(is_frame(&mut s, f, a, b, false));
    assert!(s.pop().is_none());
}

#[test]
fn a_frame_pushed_after_a_pop_replaces_the_popped_one() {
    let mut s = Store::new();
    let a = s.alloc(Node::Sym(1));
    let b = s.alloc(Node::Sym(2));
    s.push(Frame::Visit(a, a));
    s.push(Frame::Visit(b, b));
    s.pop();
    s.push(Frame::Build(a, b));
    let f = s.pop();
    assert!(is_frame(&mut s, f, a, b, true));
    let f = s.pop();
    assert!(is_frame(&mut s, f, a, a, false));
    assert!(s.pop().is_none());
}

#[test]
fn drop_stack_empties_the_stack() {
    let mut s = Store::new();
    let a = s.root();
    for _ in 0..5 {
        s.push(Frame::Visit(a, a));
    }
    s.drop_stack();
    assert!(s.pop().is_none());
}

#[test]
fn the_stack_holds_many_frames() {
    let mut s = Store::new();
    let a = s.root();
    let b = s.alloc(Node::Sym(3));
    for i in 0..10_000 {
        s.push(if i % 2 == 0 {
            Frame::Visit(a, b)
        } else {
            Frame::Build(b, a)
        });
    }
    for i in (0..10_000).rev() {
        let f = s.pop();
        let ok = if i % 2 == 0 {
            is_frame(&mut s, f, a, b, false)
        } else {
            is_frame(&mut s, f, b, a, true)
        };
        assert!(ok, "frame {i}");
    }
    assert!(s.pop().is_none());
}

#[test]
fn each_stack_primitive_costs_one_tick() {
    let mut s = Store::new();
    let a = s.root();
    let ((), t) = spent(&mut s, |s| {
        s.push(Frame::Visit(a, a));
        s.pop();
        s.pop();
        s.drop_stack();
    });
    assert_eq!(t, 4);
}

#[test]
fn the_stack_does_not_touch_the_tables() {
    let mut s = Store::new();
    let a = s.alloc(Node::Sym(1));
    s.clear(Tbl::A);
    s.set(Tbl::A, a, a);
    s.push(Frame::Visit(a, a));
    s.drop_stack();
    let r = s.get(Tbl::A, a).expect("a value");
    assert!(s.same(r, a));
}
