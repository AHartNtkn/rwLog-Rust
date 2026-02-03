mod common;

use common::*;

use rwlog::rel::Rel;
use rwlog::symbol::SymbolStore;
use rwlog::term::TermStore;
use std::sync::Arc;

#[test]
fn zero_relation_has_no_answers() {
    let symbols = SymbolStore::new();
    let build = |_terms: &mut TermStore, _symbols: &SymbolStore| Rel::Zero;
    assert_rel_pairs_with_dual(&symbols, &[], &build);
}

#[test]
fn call_unbound_is_empty() {
    let symbols = SymbolStore::new();
    let build = |_terms: &mut TermStore, _symbols: &SymbolStore| Rel::Call(42);
    assert_rel_pairs_with_dual(&symbols, &[], &build);
}

#[test]
fn identity_atom_preserves_input() {
    let symbols = SymbolStore::new();
    let expected = vec![(shape_atom("a"), shape_atom("a"))];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let a = t_atom(symbols, terms, "a");
        let identity = rel_rule(t_var(terms, 0), t_var(terms, 0), terms);
        rel_seq(vec![rel_at(a, terms), identity])
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn identity_unconstrained_emits_general_span() {
    let symbols = SymbolStore::new();
    let expected = vec![(shape_var(0), shape_var(0))];
    let build = |terms: &mut TermStore, _symbols: &SymbolStore| {
        let v0 = t_var(terms, 0);
        rel_rule(v0, v0, terms)
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn swap_unconstrained_emits_general_span() {
    let symbols = SymbolStore::new();
    let expected = vec![(
        shape_app("pair", vec![shape_var(0), shape_var(1)]),
        shape_app("pair", vec![shape_var(1), shape_var(0)]),
    )];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let pair = sym(symbols, "pair");
        let v0 = t_var(terms, 0);
        let v1 = t_var(terms, 1);
        let pair_v0_v1 = t_app2(terms, pair, v0, v1);
        let pair_v1_v0 = t_app2(terms, pair, v1, v0);
        rel_rule(pair_v0_v1, pair_v1_v0, terms)
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn repeated_variable_requires_equality() {
    let symbols = SymbolStore::new();
    let expected = vec![(
        shape_app("pair", vec![shape_atom("a"), shape_atom("a")]),
        shape_atom("a"),
    )];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let pair = sym(symbols, "pair");
        let a = t_atom(symbols, terms, "a");
        let v0 = t_var(terms, 0);
        let pair_v0_v0 = t_app2(terms, pair, v0, v0);
        let pair_aa = t_app2(terms, pair, a, a);
        let rule = rel_rule(pair_v0_v0, v0, terms);
        rel_seq(vec![rel_at(pair_aa, terms), rule])
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn repeated_variable_unconstrained_emits_general_span() {
    let symbols = SymbolStore::new();
    let expected = vec![(
        shape_app("pair", vec![shape_var(0), shape_var(0)]),
        shape_var(0),
    )];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let pair = sym(symbols, "pair");
        let v0 = t_var(terms, 0);
        let pair_v0_v0 = t_app2(terms, pair, v0, v0);
        rel_rule(pair_v0_v0, v0, terms)
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn repeated_variable_rejects_mismatch() {
    let symbols = SymbolStore::new();
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let pair = sym(symbols, "pair");
        let a = t_atom(symbols, terms, "a");
        let b = t_atom(symbols, terms, "b");
        let v0 = t_var(terms, 0);
        let pair_v0_v0 = t_app2(terms, pair, v0, v0);
        let pair_ab = t_app2(terms, pair, a, b);
        let rule = rel_rule(pair_v0_v0, v0, terms);
        rel_seq(vec![rel_at(pair_ab, terms), rule])
    };
    assert_rel_pairs_with_dual(&symbols, &[], &build);
}

#[test]
fn fresh_rhs_variable_is_existential() {
    let symbols = SymbolStore::new();
    let expected = vec![(
        shape_atom("a"),
        shape_app("pair", vec![shape_atom("a"), shape_var(0)]),
    )];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let pair = sym(symbols, "pair");
        let a = t_atom(symbols, terms, "a");
        let v0 = t_var(terms, 0);
        let v1 = t_var(terms, 1);
        let pair_v0_v1 = t_app2(terms, pair, v0, v1);
        let rule = rel_rule(v0, pair_v0_v1, terms);
        rel_seq(vec![rel_at(a, terms), rule])
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn fresh_rhs_variable_unconstrained_is_existential() {
    let symbols = SymbolStore::new();
    let expected = vec![(
        shape_var(0),
        shape_app("pair", vec![shape_var(0), shape_var(1)]),
    )];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let pair = sym(symbols, "pair");
        let v0 = t_var(terms, 0);
        let v1 = t_var(terms, 1);
        let pair_v0_v1 = t_app2(terms, pair, v0, v1);
        rel_rule(v0, pair_v0_v1, terms)
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn dropped_lhs_var_is_existential_in_backward() {
    let symbols = SymbolStore::new();
    let expected = vec![(
        shape_app("pair", vec![shape_atom("a"), shape_var(0)]),
        shape_atom("a"),
    )];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let pair = sym(symbols, "pair");
        let a = t_atom(symbols, terms, "a");
        let v0 = t_var(terms, 0);
        let v1 = t_var(terms, 1);
        let pair_v0_v1 = t_app2(terms, pair, v0, v1);
        let rule = rel_rule(pair_v0_v1, v0, terms);
        rel_seq(vec![rule, rel_at(a, terms)])
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn alpha_equivalent_rules_have_same_semantics() {
    let symbols = SymbolStore::new();
    let expected = vec![(shape_atom("a"), shape_app("f", vec![shape_atom("a")]))];

    let build_var0 = |terms: &mut TermStore, symbols: &SymbolStore| {
        let f = sym(symbols, "f");
        let a = t_atom(symbols, terms, "a");
        let v0 = t_var(terms, 0);
        let f_v0 = t_app1(terms, f, v0);
        let rule = rel_rule(v0, f_v0, terms);
        rel_seq(vec![rel_at(a, terms), rule])
    };
    let build_var1 = |terms: &mut TermStore, symbols: &SymbolStore| {
        let f = sym(symbols, "f");
        let a = t_atom(symbols, terms, "a");
        let v1 = t_var(terms, 1);
        let f_v1 = t_app1(terms, f, v1);
        let rule = rel_rule(v1, f_v1, terms);
        rel_seq(vec![rel_at(a, terms), rule])
    };

    assert_rel_pairs_with_dual(&symbols, &expected, &build_var0);
    assert_rel_pairs_with_dual(&symbols, &expected, &build_var1);
}

#[test]
fn seq_composition_produces_expected_pair() {
    let symbols = SymbolStore::new();
    let expected = vec![(shape_atom("a"), shape_atom("c"))];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let a = t_atom(symbols, terms, "a");
        let b = t_atom(symbols, terms, "b");
        let c = t_atom(symbols, terms, "c");
        let r1 = rel_rule(a, b, terms);
        let r2 = rel_rule(b, c, terms);
        rel_seq(vec![r1, r2])
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn seq_composition_non_ground_produces_general_span() {
    let symbols = SymbolStore::new();
    let expected = vec![(
        shape_app("f", vec![shape_var(0)]),
        shape_app("h", vec![shape_var(0)]),
    )];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let f = sym(symbols, "f");
        let g = sym(symbols, "g");
        let h = sym(symbols, "h");
        let v0 = t_var(terms, 0);
        let v1 = t_var(terms, 1);
        let f_v0 = t_app1(terms, f, v0);
        let g_v0 = t_app1(terms, g, v0);
        let g_v1 = t_app1(terms, g, v1);
        let h_v1 = t_app1(terms, h, v1);
        let r1 = rel_rule(f_v0, g_v0, terms);
        let r2 = rel_rule(g_v1, h_v1, terms);
        rel_seq(vec![r1, r2])
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn seq_mismatch_is_empty() {
    let symbols = SymbolStore::new();
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let a = t_atom(symbols, terms, "a");
        let b = t_atom(symbols, terms, "b");
        let c = t_atom(symbols, terms, "c");
        let d = t_atom(symbols, terms, "d");
        let r1 = rel_rule(a, b, terms);
        let r2 = rel_rule(c, d, terms);
        rel_seq(vec![r1, r2])
    };
    assert_rel_pairs_with_dual(&symbols, &[], &build);
}

#[test]
fn or_union_yields_both_answers() {
    let symbols = SymbolStore::new();
    let expected = vec![
        (shape_atom("a"), shape_atom("b")),
        (shape_atom("a"), shape_atom("c")),
    ];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let a = t_atom(symbols, terms, "a");
        let b = t_atom(symbols, terms, "b");
        let c = t_atom(symbols, terms, "c");
        let r1 = rel_rule(a, b, terms);
        let r2 = rel_rule(a, c, terms);
        rel_or(r1, r2)
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn or_union_deduplicates_answers() {
    let symbols = SymbolStore::new();
    let expected = vec![(shape_atom("a"), shape_atom("b"))];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let a = t_atom(symbols, terms, "a");
        let b = t_atom(symbols, terms, "b");
        let r1 = rel_rule(a, b, terms);
        let r2 = rel_rule(a, b, terms);
        rel_or(r1, r2)
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn or_union_deduplicates_alpha_equivalent_non_ground() {
    let symbols = SymbolStore::new();
    let expected = vec![(
        shape_app("pair", vec![shape_var(0), shape_var(1)]),
        shape_app("pair", vec![shape_var(1), shape_var(0)]),
    )];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let pair = sym(symbols, "pair");
        let v0 = t_var(terms, 0);
        let v1 = t_var(terms, 1);
        let v2 = t_var(terms, 2);
        let v3 = t_var(terms, 3);
        let rule_a = rel_rule(
            t_app2(terms, pair, v0, v1),
            t_app2(terms, pair, v1, v0),
            terms,
        );
        let rule_b = rel_rule(
            t_app2(terms, pair, v2, v3),
            t_app2(terms, pair, v3, v2),
            terms,
        );
        rel_or(rule_a, rule_b)
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn and_intersection_keeps_common_answers() {
    let symbols = SymbolStore::new();
    let expected = vec![(shape_atom("a"), shape_atom("c"))];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let a = t_atom(symbols, terms, "a");
        let b = t_atom(symbols, terms, "b");
        let c = t_atom(symbols, terms, "c");
        let d = t_atom(symbols, terms, "d");
        let left = rel_or(rel_rule(a, b, terms), rel_rule(a, c, terms));
        let right = rel_or(rel_rule(a, c, terms), rel_rule(a, d, terms));
        rel_and(left, right)
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn and_intersection_specializes_structure() {
    let symbols = SymbolStore::new();
    let expected = vec![(
        shape_app("f", vec![shape_var(0)]),
        shape_app("f", vec![shape_var(0)]),
    )];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let f = sym(symbols, "f");
        let v0 = t_var(terms, 0);
        let v1 = t_var(terms, 1);
        let identity = rel_rule(v0, v0, terms);
        let f_v1 = t_app1(terms, f, v1);
        let f_rule = rel_rule(f_v1, f_v1, terms);
        rel_and(identity, f_rule)
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}

#[test]
fn and_with_zero_is_empty() {
    let symbols = SymbolStore::new();
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let a = t_atom(symbols, terms, "a");
        let b = t_atom(symbols, terms, "b");
        let r1 = rel_rule(a, b, terms);
        rel_and(r1, Rel::Zero)
    };
    assert_rel_pairs_with_dual(&symbols, &[], &build);
}

#[test]
fn seq_with_zero_is_empty() {
    let symbols = SymbolStore::new();
    let build = |_terms: &mut TermStore, _symbols: &SymbolStore| {
        let left = Rel::Zero;
        let right = Rel::Zero;
        rel_seq(vec![left, right])
    };
    assert_rel_pairs_with_dual(&symbols, &[], &build);
}

#[test]
fn recursive_double_computes_expected_value() {
    let symbols = SymbolStore::new();
    let expected = vec![(shape_peano(2), shape_peano(4))];
    let build = |terms: &mut TermStore, symbols: &SymbolStore| {
        let z = t_atom(symbols, terms, "z");
        let s = sym(symbols, "s");

        let v0 = t_var(terms, 0);
        let peel = rel_rule(t_app1(terms, s, v0), v0, terms);
        let post = rel_rule(v0, t_app1(terms, s, t_app1(terms, s, v0)), terms);
        let base = rel_rule(z, z, terms);

        let body = rel_or(base, rel_seq(vec![peel, Rel::Call(0), post]));
        let rel = Rel::Fix(0, Arc::new(body));

        let input = t_peano(symbols, terms, 2);
        rel_seq(vec![rel_at(input, terms), rel])
    };
    assert_rel_pairs_with_dual(&symbols, &expected, &build);
}
