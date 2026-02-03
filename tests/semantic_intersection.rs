mod common;

use common::*;

use rwlog::symbol::SymbolStore;
use rwlog::term::TermStore;

#[test]
fn intersection_propagates_input_binding_into_output() {
    let symbols = SymbolStore::new();
    let expected = [(
        shape_app("f", vec![shape_atom("a")]),
        shape_app("g", vec![shape_atom("a")]),
    )];

    assert_rel_pairs_with_dual(&symbols, &expected, &|terms, symbols| {
        let f = sym(symbols, "f");
        let g = sym(symbols, "g");
        let a = t_atom(symbols, terms, "a");
        let v0 = t_var(terms, 0);
        let v1 = t_var(terms, 1);

        let left = rel_rule(t_app1(terms, f, v0), t_app1(terms, g, v0), terms);
        let right = rel_rule(t_app1(terms, f, a), t_app1(terms, g, v1), terms);
        rel_and(left, right)
    });
}

#[test]
fn intersection_preserves_fresh_output_distinct_from_input() {
    let symbols = SymbolStore::new();
    let expected = [(
        shape_app("f", vec![shape_var(0)]),
        shape_app("g", vec![shape_var(1)]),
    )];

    assert_rel_pairs_with_dual(&symbols, &expected, &|terms, symbols| {
        let f = sym(symbols, "f");
        let g = sym(symbols, "g");
        let v0 = t_var(terms, 0);
        let v1 = t_var(terms, 1);
        let v2 = t_var(terms, 2);

        let left = rel_rule(t_app1(terms, f, v0), t_app1(terms, g, v1), terms);
        let right = rel_rule(t_app1(terms, f, v0), t_app1(terms, g, v2), terms);
        rel_and(left, right)
    });
}

#[test]
fn intersection_after_composition_respects_shared_prefix() {
    let symbols = SymbolStore::new();
    let expected = [(
        shape_app("f", vec![shape_var(0)]),
        shape_app("h", vec![shape_var(0)]),
    )];

    assert_rel_pairs_with_dual(&symbols, &expected, &|terms, symbols| {
        let f = sym(symbols, "f");
        let g = sym(symbols, "g");
        let h = sym(symbols, "h");
        let v0 = t_var(terms, 0);
        let v1 = t_var(terms, 1);

        let a = rel_rule(t_app1(terms, f, v0), t_app1(terms, g, v0), terms);
        let b = rel_rule(t_app1(terms, g, v0), t_app1(terms, h, v0), terms);
        let c = rel_rule(t_app1(terms, g, v0), t_app1(terms, h, v1), terms);

        let left = rel_seq(vec![a.clone(), b]);
        let right = rel_seq(vec![a, c]);
        rel_and(left, right)
    });
}

#[test]
fn intersection_before_composition_matches_post_intersection() {
    let symbols = SymbolStore::new();

    let actual_pre = {
        let mut terms = TermStore::new();
        let f = sym(&symbols, "f");
        let g = sym(&symbols, "g");
        let h = sym(&symbols, "h");
        let a = t_atom(&symbols, &terms, "a");
        let v0 = t_var(&terms, 0);
        let v1 = t_var(&terms, 1);

        let r1 = rel_rule(t_app1(&terms, f, v0), t_app1(&terms, g, v0), &mut terms);
        let r2 = rel_rule(t_app1(&terms, f, a), t_app1(&terms, g, v1), &mut terms);
        let d = rel_rule(t_app1(&terms, g, v0), t_app1(&terms, h, v0), &mut terms);

        let rel = rel_seq(vec![rel_and(r1, r2), d]);
        collect_pair_shapes(rel, terms, &symbols, None)
    };

    let actual_post = {
        let mut terms = TermStore::new();
        let f = sym(&symbols, "f");
        let g = sym(&symbols, "g");
        let h = sym(&symbols, "h");
        let a = t_atom(&symbols, &terms, "a");
        let v0 = t_var(&terms, 0);
        let v1 = t_var(&terms, 1);

        let r1 = rel_rule(t_app1(&terms, f, v0), t_app1(&terms, g, v0), &mut terms);
        let r2 = rel_rule(t_app1(&terms, f, a), t_app1(&terms, g, v1), &mut terms);
        let d = rel_rule(t_app1(&terms, g, v0), t_app1(&terms, h, v0), &mut terms);

        let left = rel_seq(vec![r1, d.clone()]);
        let right = rel_seq(vec![r2, d]);
        let rel = rel_and(left, right);
        collect_pair_shapes(rel, terms, &symbols, None)
    };

    assert_pairs(actual_pre, &actual_post);
}

#[test]
fn intersection_with_mixed_interior_or() {
    let symbols = SymbolStore::new();
    let expected = [(
        shape_app("f", vec![shape_atom("a")]),
        shape_app("h", vec![shape_atom("a")]),
    )];

    assert_rel_pairs_with_dual(&symbols, &expected, &|terms, symbols| {
        let f = sym(symbols, "f");
        let g = sym(symbols, "g");
        let h = sym(symbols, "h");
        let k = sym(symbols, "k");
        let a = t_atom(symbols, terms, "a");
        let v0 = t_var(terms, 0);

        let fg = rel_rule(t_app1(terms, f, v0), t_app1(terms, g, v0), terms);
        let gh = rel_rule(t_app1(terms, g, v0), t_app1(terms, h, v0), terms);
        let gk = rel_rule(t_app1(terms, g, v0), t_app1(terms, k, v0), terms);
        let left = rel_seq(vec![fg, rel_or(gh, gk)]);

        let fa = rel_rule(t_app1(terms, f, a), t_app1(terms, g, a), terms);
        let ga = rel_rule(t_app1(terms, g, a), t_app1(terms, h, a), terms);
        let right = rel_seq(vec![fa, ga]);

        rel_and(left, right)
    });
}

#[test]
fn intersection_with_mixed_interior_and() {
    let symbols = SymbolStore::new();
    let expected = [(
        shape_app("f", vec![shape_var(0)]),
        shape_app("h", vec![shape_var(0)]),
    )];

    assert_rel_pairs_with_dual(&symbols, &expected, &|terms, symbols| {
        let f = sym(symbols, "f");
        let g = sym(symbols, "g");
        let h = sym(symbols, "h");
        let v0 = t_var(terms, 0);
        let v1 = t_var(terms, 1);

        let fg = rel_rule(t_app1(terms, f, v0), t_app1(terms, g, v0), terms);
        let gh = rel_rule(t_app1(terms, g, v0), t_app1(terms, h, v0), terms);
        let gh_fresh = rel_rule(t_app1(terms, g, v0), t_app1(terms, h, v1), terms);
        let left = rel_seq(vec![fg.clone(), rel_and(gh, gh_fresh)]);

        let right = rel_seq(vec![
            fg,
            rel_rule(t_app1(terms, g, v0), t_app1(terms, h, v0), terms),
        ]);

        rel_and(left, right)
    });
}
