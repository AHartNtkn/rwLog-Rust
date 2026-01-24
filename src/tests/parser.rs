use super::*;

// ========================================================================
// TERM PARSING TESTS
// ========================================================================

#[test]
fn parse_atom() {
    let parser = Parser::new();
    let result = parser.parse_term("z");
    assert!(result.is_ok(), "Should parse atom");
    let parsed = result.unwrap();
    assert!(parsed.var_order.is_empty(), "Atom has no variables");
}

#[test]
fn parse_numeric_atom() {
    let parser = Parser::new();
    let result = parser.parse_term("0");
    assert!(result.is_ok(), "Should parse numeric atom");
    let parsed = result.unwrap();
    assert!(parsed.var_order.is_empty(), "Numeric atom has no variables");
}

#[test]
fn parse_variable() {
    let parser = Parser::new();
    let result = parser.parse_term("$x");
    assert!(result.is_ok(), "Should parse variable");
    let parsed = result.unwrap();
    assert_eq!(parsed.var_order.len(), 1, "Should have one variable");
}

#[test]
fn parse_compound_term_nullary() {
    let parser = Parser::new();
    let result = parser.parse_term("(f)");
    assert!(result.is_ok(), "Should parse nullary compound");
}

#[test]
fn parse_compound_term_unary() {
    let parser = Parser::new();
    let result = parser.parse_term("(s z)");
    assert!(result.is_ok(), "Should parse unary compound");
}

#[test]
fn parse_compound_with_numeric_atom() {
    let parser = Parser::new();
    let result = parser.parse_term("(c 0)");
    assert!(
        result.is_ok(),
        "Should parse compound with numeric atom argument"
    );
}

#[test]
fn parse_compound_term_binary() {
    let parser = Parser::new();
    let result = parser.parse_term("(cons z z)");
    assert!(result.is_ok(), "Should parse binary compound");
}

#[test]
fn parse_nested_compound() {
    let parser = Parser::new();
    let result = parser.parse_term("(cons (s z) (s (s z)))");
    assert!(result.is_ok(), "Should parse nested compound");
}

#[test]
fn parse_term_with_variable() {
    let parser = Parser::new();
    let result = parser.parse_term("(s $x)");
    assert!(result.is_ok());
    let parsed = result.unwrap();
    assert_eq!(parsed.var_order.len(), 1);
}

#[test]
fn parse_term_multiple_variables() {
    let parser = Parser::new();
    let result = parser.parse_term("(cons $x $y)");
    assert!(result.is_ok());
    let parsed = result.unwrap();
    assert_eq!(parsed.var_order.len(), 2);
}

#[test]
fn parse_term_repeated_variable() {
    let parser = Parser::new();
    let result = parser.parse_term("(cons $x $x)");
    assert!(result.is_ok());
    let parsed = result.unwrap();
    // Same variable used twice, but only counted once
    assert_eq!(parsed.var_order.len(), 1);
}

#[test]
fn parse_term_whitespace_handling() {
    let parser = Parser::new();
    let result = parser.parse_term("  (  cons   $x   $y  )  ");
    assert!(result.is_ok());
}

#[test]
fn parse_term_unclosed_paren_fails() {
    let parser = Parser::new();
    let result = parser.parse_term("(cons $x");
    assert!(result.is_err());
}

#[test]
fn parse_term_extra_chars_fails() {
    let parser = Parser::new();
    let result = parser.parse_term("z extra");
    assert!(result.is_err());
}

// ========================================================================
// RULE PARSING TESTS
// ========================================================================

#[test]
fn parse_simple_rule() {
    let mut parser = Parser::new();
    let result = parser.parse_rule("z -> z");
    assert!(result.is_ok(), "Should parse simple rule");
}

#[test]
fn parse_rule_with_compound() {
    let mut parser = Parser::new();
    let result = parser.parse_rule("(s $x) -> $x");
    assert!(result.is_ok());
}

#[test]
fn parse_rule_with_variables() {
    let mut parser = Parser::new();
    let result = parser.parse_rule("(cons $x $y) -> $y");
    assert!(result.is_ok());
}

#[test]
fn parse_rule_rhs_only_variable_creates_fresh_output() {
    let mut parser = Parser::new();
    let nf = parser
        .parse_rule("$x -> (f $x $y)")
        .expect("parse rule with rhs-only variable");
    assert_eq!(nf.drop_fresh.in_arity, 1);
    assert_eq!(nf.drop_fresh.out_arity, 2);
    assert_eq!(nf.drop_fresh.map.as_slice(), &[(0, 0)]);
}

#[test]
fn parse_rule_lhs_only_variable_is_dropped() {
    let mut parser = Parser::new();
    let nf = parser
        .parse_rule("(f $x $y) -> $x")
        .expect("parse rule with lhs-only variable");
    assert_eq!(nf.drop_fresh.in_arity, 2);
    assert_eq!(nf.drop_fresh.out_arity, 1);
    assert_eq!(nf.drop_fresh.map.as_slice(), &[(0, 0)]);
}

#[test]
fn parse_complex_rule() {
    let mut parser = Parser::new();
    let result = parser.parse_rule("(cons (s $x) $y) -> (cons $x $y)");
    assert!(result.is_ok());
}

#[test]
fn parse_rule_missing_arrow_fails() {
    let mut parser = Parser::new();
    let result = parser.parse_rule("z z");
    assert!(result.is_err());
}

#[test]
fn parse_rule_missing_rhs_fails() {
    let mut parser = Parser::new();
    let result = parser.parse_rule("z ->");
    assert!(result.is_err());
}

// ========================================================================
// RELATION BODY PARSING TESTS
// ========================================================================

#[test]
fn parse_single_rule_body() {
    let mut parser = Parser::new();
    let result = parser.parse_rel_body("z -> z");
    assert!(result.is_ok());
    assert!(matches!(result.unwrap(), Rel::Atom(_)));
}

#[test]
fn parse_term_literal_identity_body() {
    let mut parser = Parser::new();
    let result = parser.parse_rel_body("@z").unwrap();
    match result {
        Rel::Atom(nf) => {
            assert_eq!(nf.match_pats.len(), 1);
            assert_eq!(nf.build_pats.len(), 1);
            assert_eq!(nf.match_pats[0], nf.build_pats[0]);
        }
        _ => panic!("Expected term literal to parse as Atom identity"),
    }
}

#[test]
fn parse_or_body() {
    let mut parser = Parser::new();
    let result = parser.parse_rel_body("z -> z | (s z) -> (s z)");
    assert!(result.is_ok());
    assert!(matches!(result.unwrap(), Rel::Or(_, _)));
}

#[test]
fn parse_seq_body() {
    let mut parser = Parser::new();
    let result = parser.parse_rel_body("z -> (s z) ; (s $x) -> $x");
    assert!(result.is_ok());
    assert!(matches!(result.unwrap(), Rel::Seq(_)));
}

#[test]
fn parse_bracketed_seq() {
    let mut parser = Parser::new();
    let result = parser.parse_rel_body("[z -> (s z) ; (s $x) -> $x]");
    assert!(result.is_ok());
}

#[test]
fn parse_or_with_seq() {
    let mut parser = Parser::new();
    let result = parser.parse_rel_body("z -> z | [a -> b ; b -> c]");
    assert!(result.is_ok());
    match result.unwrap() {
        Rel::Or(left, right) => {
            assert!(matches!(left.as_ref(), Rel::Atom(_)));
            assert!(matches!(right.as_ref(), Rel::Seq(_)));
        }
        _ => panic!("Expected Or"),
    }
}

#[test]
fn parse_call_in_seq() {
    let mut parser = Parser::new();
    // First register a relation
    parser.relations.insert("foo".to_string(), 0);
    let result = parser.parse_rel_body("a -> b ; foo ; c -> d");
    assert!(result.is_ok());
    match result.unwrap() {
        Rel::Seq(factors) => {
            assert_eq!(factors.len(), 3);
            assert!(matches!(factors[1].as_ref(), Rel::Call(0)));
        }
        _ => panic!("Expected Seq"),
    }
}

#[test]
fn parse_nested_brackets() {
    let mut parser = Parser::new();
    let result = parser.parse_rel_body("[[a -> b]]");
    assert!(result.is_ok());
}

#[test]
fn parse_and_body() {
    let mut parser = Parser::new();
    let result = parser.parse_rel_body("a -> a & b -> b");
    assert!(result.is_ok());
    assert!(matches!(result.unwrap(), Rel::And(_, _)));
}

#[test]
fn parse_and_with_or() {
    let mut parser = Parser::new();
    // `|` binds looser than `&`
    // So `a & b | c & d` should parse as `(a & b) | (c & d)`
    // Use [...] for grouping rules
    let result = parser.parse_rel_body("[a -> a] & [b -> b] | [c -> c] & [d -> d]");
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    match result.unwrap() {
        Rel::Or(left, right) => {
            assert!(matches!(left.as_ref(), Rel::And(_, _)));
            assert!(matches!(right.as_ref(), Rel::And(_, _)));
        }
        _ => panic!("Expected Or at top level"),
    }
}

#[test]
fn parse_and_with_seq() {
    let mut parser = Parser::new();
    // `&` binds tighter than `;`
    // So `a ; b & c ; d` should parse as `a ; (b & c) ; d`
    let result = parser.parse_rel_body("[a -> a] ; [b -> b] & [c -> c] ; [d -> d]");
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    match result.unwrap() {
        Rel::Seq(factors) => {
            assert_eq!(factors.len(), 3);
            assert!(matches!(factors[0].as_ref(), Rel::Atom(_)));
            assert!(matches!(factors[1].as_ref(), Rel::And(_, _)));
            assert!(matches!(factors[2].as_ref(), Rel::Atom(_)));
        }
        _ => panic!("Expected Seq at top level"),
    }
}

#[test]
fn parse_chained_and() {
    let mut parser = Parser::new();
    let result = parser.parse_rel_body("[a -> a] & [b -> b] & [c -> c]");
    assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    // Should be left-associative: ((a & b) & c)
    match result.unwrap() {
        Rel::And(left, right) => {
            assert!(matches!(left.as_ref(), Rel::And(_, _)));
            assert!(matches!(right.as_ref(), Rel::Atom(_)));
        }
        _ => panic!("Expected And"),
    }
}

// ========================================================================
// RELATION DEFINITION PARSING TESTS
// ========================================================================

#[test]
fn parse_simple_rel_def() {
    let mut parser = Parser::new();
    let result = parser.parse_rel_def("rel id { $x -> $x }");
    assert!(result.is_ok());
    let (name, rel) = result.unwrap();
    assert_eq!(name, "id");
    assert!(matches!(rel, Rel::Fix(_, _)));
}

#[test]
fn parse_rel_def_with_or() {
    let mut parser = Parser::new();
    let result = parser.parse_rel_def("rel test { a -> b | c -> d }");
    assert!(result.is_ok());
    let (name, rel) = result.unwrap();
    assert_eq!(name, "test");
    match rel {
        Rel::Fix(_, body) => {
            assert!(matches!(body.as_ref(), Rel::Or(_, _)));
        }
        _ => panic!("Expected Fix"),
    }
}

#[test]
fn parse_recursive_rel_def() {
    let mut parser = Parser::new();
    let input = r#"
        rel add {
            (cons z $y) -> $y
            |
            [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
        }
    "#;
    let result = parser.parse_rel_def(input);
    assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
    let (name, _rel) = result.unwrap();
    assert_eq!(name, "add");
}

#[test]
fn parse_rel_def_missing_brace_fails() {
    let mut parser = Parser::new();
    let result = parser.parse_rel_def("rel test { $x -> $x");
    assert!(result.is_err());
}

#[test]
fn parse_rel_def_missing_name_fails() {
    let mut parser = Parser::new();
    let result = parser.parse_rel_def("rel { $x -> $x }");
    assert!(result.is_err());
}

// ========================================================================
// COMMENT HANDLING TESTS
// ========================================================================

#[test]
fn parse_with_comments() {
    let parser = Parser::new();
    let result = parser.parse_term("# this is a comment\nz");
    assert!(result.is_ok());
}

#[test]
fn parse_rule_with_comment() {
    let mut parser = Parser::new();
    let result = parser.parse_rule("z -> z # identity");
    assert!(result.is_ok());
}

#[test]
fn parse_rel_body_with_comments() {
    let mut parser = Parser::new();
    let input = r#"
        # Base case
        z -> z
        |
        # Recursive case
        (s $x) -> (s $x)
    "#;
    let result = parser.parse_rel_body(input);
    assert!(result.is_ok());
}

// ========================================================================
// EDGE CASE TESTS
// ========================================================================

#[test]
fn parse_empty_input_fails() {
    let parser = Parser::new();
    let result = parser.parse_term("");
    assert!(result.is_err());
}

#[test]
fn parse_whitespace_only_fails() {
    let parser = Parser::new();
    let result = parser.parse_term("   ");
    assert!(result.is_err());
}

#[test]
fn parse_identifier_with_underscores() {
    let parser = Parser::new();
    let result = parser.parse_term("my_atom");
    assert!(result.is_ok());
}

#[test]
fn parse_identifier_with_numbers() {
    let parser = Parser::new();
    let result = parser.parse_term("x1");
    assert!(result.is_ok());
}

#[test]
fn parse_variable_with_underscore() {
    let parser = Parser::new();
    let result = parser.parse_term("$my_var");
    assert!(result.is_ok());
}

#[test]
fn theory_parsing_allows_constraints_in_rules() {
    let mut parser = Parser::with_chr();
    let theory = r#"
theory eq {
  constraint eq/2
  (eq $x $x) <=> .
}
"#;
    parser.parse_theory_def(theory).expect("parse theory");
    let nf = parser
        .parse_rule("(pair $x $y) { (eq $x $y) } -> $x")
        .expect("parse rule with constraint");

    assert_eq!(nf.drop_fresh.constraint.store.alive_count, 1);
    let pred = nf
        .drop_fresh
        .constraint
        .program
        .pred_id("eq")
        .expect("eq predicate id");
    let inst = nf
        .drop_fresh
        .constraint
        .store
        .inst
        .iter()
        .find(|c| c.alive)
        .expect("alive constraint");
    assert_eq!(inst.pred, pred);
}

#[test]
fn constraint_with_unknown_predicate_fails() {
    let mut parser = Parser::with_chr();
    let theory = r#"
theory eq {
  constraint eq/2
  (eq $x $x) <=> .
}
"#;
    parser.parse_theory_def(theory).expect("parse theory");
    let err = match parser.parse_rule("$x { (neq $x $x) } -> $x") {
        Ok(_) => panic!("expected unknown predicate error"),
        Err(err) => err,
    };
    assert!(
        err.message.contains("unknown constraint"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn theory_fail_body_makes_constraint_unsat() {
    let mut parser = Parser::with_chr();
    let theory = r#"
theory bad {
  constraint bad/0
  bad <=> fail.
}
"#;
    parser.parse_theory_def(theory).expect("parse theory");
    let nf = parser
        .parse_rule("$x { bad } -> $x")
        .expect("parse rule with fail constraint");
    let mut terms = parser.take_terms();
    let result = nf.drop_fresh.constraint.normalize(&mut terms);
    assert!(result.is_none(), "expected failure from bad constraint");
}

#[test]
fn theory_parses_propagation_and_simpagation_rules() {
    let mut parser = Parser::with_chr();
    let theory = r#"
theory t {
  constraint p/1
  constraint q/1
  constraint r/1
  (p $x) ==> (q $x).
  (p $x) \ (q $x) <=> (r $x).
}
"#;
    parser
        .parse_theory_def(theory)
        .expect("parse propagation and simpagation");
}

#[test]
fn theory_parses_guard_and_applies_it() {
    let mut parser = Parser::with_chr();
    let theory = r#"
theory guards {
  constraint p/1
  constraint q/1
  (p $x) <=> (eq $x z) | (q $x).
}
"#;
    parser.parse_theory_def(theory).expect("parse theory");
    let nf = parser
        .parse_rule("z { (p z) } -> z")
        .expect("parse rule with guard");

    let mut terms = parser.take_terms();
    let (normalized, _) = nf
        .drop_fresh
        .constraint
        .normalize(&mut terms)
        .expect("normalize constraints");

    let q = normalized.program.pred_id("q").expect("q predicate id");
    let count = normalized
        .store
        .inst
        .iter()
        .filter(|c| c.alive && c.pred == q)
        .count();
    assert_eq!(count, 1, "Expected guard to add q(z)");
}

#[test]
fn constraint_arity_mismatch_fails() {
    let mut parser = Parser::with_chr();
    let theory = r#"
theory eq {
  constraint eq/2
  (eq $x $x) <=> .
}
"#;
    parser.parse_theory_def(theory).expect("parse theory");
    let err = match parser.parse_rule("$x { (eq $x) } -> $x") {
        Ok(_) => panic!("expected arity mismatch error"),
        Err(err) => err,
    };
    assert!(err.message.contains("arity"), "unexpected error: {}", err);
}

#[test]
fn format_nf_includes_constraints() {
    let mut parser = Parser::with_chr();
    let theory = r#"
theory eq {
  constraint eq/2
  (eq $x $x) <=> .
}
"#;
    parser.parse_theory_def(theory).expect("parse theory");
    let nf = parser
        .parse_rule("(pair $x $y) { (eq $x $y) } -> $x")
        .expect("parse rule with constraint");
    let mut terms = parser.take_terms();
    let rendered = crate::nf::format_nf(&nf, &mut terms, parser.symbols()).expect("format nf");
    assert!(
        rendered.contains("{ (eq $0 $1) }"),
        "expected constraints in output, got: {}",
        rendered
    );
}

// ========================================================================
// SIZE AND MEMORY TESTS
// ========================================================================

#[test]
fn parser_size_reasonable() {
    use std::mem::size_of;
    let size = size_of::<Parser>();
    // Parser contains SymbolStore, TermStore, and HashMap<String, RelId>
    assert!(
        size < 1000,
        "Parser should not be excessively large, got {}",
        size
    );
}

#[test]
fn parse_error_size_reasonable() {
    use std::mem::size_of;
    let size = size_of::<ParseError>();
    assert!(
        size < 100,
        "ParseError should not be excessively large, got {}",
        size
    );
}
