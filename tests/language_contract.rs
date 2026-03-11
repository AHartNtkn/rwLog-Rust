mod common;

use common::*;

use rwlog::chr::ChrState;
use rwlog::engine::Engine;
use rwlog::nf::direct_rule_terms;
use rwlog::parser::{ChrConstraintBuilder, Parser, RelDef};
use rwlog::rel::Rel;
use rwlog::repl::{split_statements, Repl, ReplError};
use rwlog::work::Env;

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

type TestConstraint = ChrState;

static TEMP_FILE_COUNTER: AtomicU64 = AtomicU64::new(0);

struct TempFile {
    path: PathBuf,
}

impl TempFile {
    fn new(prefix: &str, content: &str) -> Self {
        let id = TEMP_FILE_COUNTER.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let mut path = std::env::temp_dir();
        path.push(format!("rwlog_{prefix}_{pid}_{id}.txt"));
        fs::write(&path, content).expect("write temp file");
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn peano_term(n: usize) -> String {
    if n == 0 {
        "z".to_string()
    } else {
        format!("(s {})", peano_term(n - 1))
    }
}

fn parse_program_defs(
    parser: &mut Parser<ChrConstraintBuilder>,
    program: &str,
) -> Result<HashMap<String, Rel<TestConstraint>>, String> {
    let statements = split_statements(program)?;

    // Pre-scan: register all macro signatures for forward references.
    parser.scan_macro_signatures(&statements);

    let mut pending_rels = Vec::new();
    for statement in statements {
        let line = statement.trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with("theory ") {
            parser.parse_theory_def(line).map_err(|e| e.to_string())?;
            pending_rels.clear();
            continue;
        }
        if line.starts_with("rel ") {
            if let RelDef::Relation(name, rel) = parser.parse_rel_def(line).map_err(|e| e.to_string())? {
                pending_rels.push((name, rel));
            }
            continue;
        }
        return Err(format!(
            "Unsupported statement in contract test program: {line}"
        ));
    }

    // Resolve any pending macro calls now that all definitions are available.
    let mut defs = HashMap::new();
    for (name, rel) in pending_rels {
        let resolved = parser.resolve_pending(rel)?;
        defs.insert(name, resolved);
    }
    Ok(defs)
}

fn collect_query_pairs_with_cap(
    program: &str,
    query: &str,
    cap: usize,
) -> (Vec<(Shape, Shape)>, bool) {
    let mut parser = Parser::with_chr();
    let defs = parse_program_defs(&mut parser, program).expect("parse program");
    let rel = parser.parse_rel_body(query).expect("parse query");
    let env = Env::from_defs(&defs);
    let terms = parser.take_terms();
    let mut engine = Engine::new_with_env(rel, terms, env);

    let mut out = Vec::new();
    while out.len() < cap {
        match engine.next() {
            Some(nf) => {
                let (lhs, rhs) =
                    direct_rule_terms(&nf, engine.terms_mut()).expect("expected unary answer");
                out.push(pair_shape(lhs, rhs, engine.terms_mut(), parser.symbols()));
            }
            None => return (out, true),
        }
    }
    (out, false)
}

fn assert_query_exact(program: &str, query: &str, expected: &[(Shape, Shape)]) {
    let cap = expected.len() + 1;
    let (actual, exhausted) = collect_query_pairs_with_cap(program, query, cap);
    assert!(
        exhausted,
        "query produced more answers than expected: query={query}, partial={actual:?}"
    );
    assert_pairs(actual, expected);
}

fn assert_query_contains(
    program: &str,
    query: &str,
    cap: usize,
    expected_subset: &[(Shape, Shape)],
) {
    let (actual, _exhausted) = collect_query_pairs_with_cap(program, query, cap);
    let actual_set: HashSet<(Shape, Shape)> = actual.into_iter().collect();
    for expected in expected_subset {
        assert!(
            actual_set.contains(expected),
            "missing expected answer {:?} in query {}",
            expected,
            query
        );
    }
}

fn cons_shape(left: Shape, right: Shape) -> Shape {
    shape_app("cons", vec![left, right])
}

const BASIC_PROGRAM: &str = r#"
rel id {
    $x -> $x
}

rel swap {
    (pair $x $y) -> (pair $y $x)
}

rel same_pair {
    (pair $x $x) -> $x
}

rel extend {
    $x -> (pair $x $y)
}

rel first {
    (pair $x $y) -> $x
}
"#;

const ADD_PROGRAM: &str = r#"
rel add {
    (cons z $y) -> $y
    |
    [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
}
"#;

const EVEN_ODD_PROGRAM: &str = r#"
rel even {
    z -> yes
    |
    [(s $n) -> $n ; odd]
}

rel odd {
    z -> no
    |
    [(s $n) -> $n ; even]
}
"#;

const RANGE_PROGRAM: &str = r#"
theory ranges {
    constraint lt/2
    constraint leq/2
    constraint between/2

    (leq $x $x) <=> .
    (leq z $y) <=> .
    (leq (s $x) (s $y)) <=> (leq $x $y).
    (leq (s $x) z) <=> fail.

    (lt z (s $y)) <=> .
    (lt (s $x) (s $y)) <=> (lt $x $y).
    (lt $x z) <=> fail.

    (between $x (range (closed $lo) (closed $hi))) <=> (leq $lo $x), (leq $x $hi).
    (between $x (range (open $lo) (open $hi))) <=> (lt $lo $x), (lt $x $hi).
}

rel member {
    (pair $x $range) { (between $x $range) } -> $x
}
"#;

const EQ_NEQ_PROGRAM: &str = r#"
theory eq_neq {
    constraint eq/2
    constraint neq/2
    constraint nonzero/1

    (eq $x $x) <=> .
    (eq z (s $x)) <=> fail.
    (eq (s $x) z) <=> fail.
    (eq (s $x) (s $y)) <=> (eq $x $y).

    (neq $x $x) <=> fail.
    (neq z (s $x)) <=> .
    (neq (s $x) z) <=> .
    (neq (s $x) (s $y)) <=> (neq $x $y).

    (eq $x $y), (neq $x $y) <=> fail.
    (nonzero $x) <=> (eq $x z) | fail.
    (nonzero $x) <=> (neq $x z) | true.
}

rel same {
    (pair $x $y) { (eq $x $y) } -> $x
}

rel different {
    (pair $x $y) { (neq $x $y) } -> (pair $x $y)
}

rel nonzero_ok {
    $x { (nonzero $x) } -> $x
}
"#;

#[test]
fn term_literal_is_identity_relation() {
    assert_query_exact("", "@a", &[(shape_atom("a"), shape_atom("a"))]);
}

#[test]
fn inline_rule_query_executes() {
    assert_query_exact("", "@a ; a -> b", &[(shape_atom("a"), shape_atom("b"))]);
}

#[test]
fn named_identity_relation_is_bidirectional() {
    assert_query_exact(
        BASIC_PROGRAM,
        "@a ; id",
        &[(shape_atom("a"), shape_atom("a"))],
    );
    assert_query_exact(
        BASIC_PROGRAM,
        "id ; @a",
        &[(shape_atom("a"), shape_atom("a"))],
    );
}

#[test]
fn repeated_variable_pattern_accepts_equal_inputs() {
    assert_query_exact(
        BASIC_PROGRAM,
        "@(pair a a) ; same_pair",
        &[(
            shape_app("pair", vec![shape_atom("a"), shape_atom("a")]),
            shape_atom("a"),
        )],
    );
}

#[test]
fn repeated_variable_pattern_rejects_unequal_inputs() {
    assert_query_exact(BASIC_PROGRAM, "@(pair a b) ; same_pair", &[]);
}

#[test]
fn fresh_rhs_variable_is_existential() {
    assert_query_exact(
        BASIC_PROGRAM,
        "@a ; extend",
        &[(
            shape_atom("a"),
            shape_app("pair", vec![shape_atom("a"), shape_var(0)]),
        )],
    );
}

#[test]
fn dropped_lhs_variable_is_existential_backward() {
    assert_query_exact(
        BASIC_PROGRAM,
        "first ; @a",
        &[(
            shape_app("pair", vec![shape_atom("a"), shape_var(0)]),
            shape_atom("a"),
        )],
    );
}

#[test]
fn alpha_equivalent_relations_have_same_behavior() {
    let program = r#"
rel lift_a {
    $x -> (f $x)
}

rel lift_b {
    $y -> (f $y)
}
"#;
    let expected = [(shape_atom("a"), shape_app("f", vec![shape_atom("a")]))];
    assert_query_exact(program, "@a ; lift_a", &expected);
    assert_query_exact(program, "@a ; lift_b", &expected);
}

#[test]
fn undefined_call_has_no_answers() {
    assert_query_exact("", "missing_relation", &[]);
}

#[test]
fn disjunction_deduplicates_alpha_equivalent_answers() {
    let program = r#"
rel swap_a {
    (pair $x $y) -> (pair $y $x)
}

rel swap_b {
    (pair $u $v) -> (pair $v $u)
}
"#;
    assert_query_exact(
        program,
        "swap_a | swap_b",
        &[(
            shape_app("pair", vec![shape_var(0), shape_var(1)]),
            shape_app("pair", vec![shape_var(1), shape_var(0)]),
        )],
    );
}

#[test]
fn conjunction_returns_intersection_of_answers() {
    assert_query_exact(
        "",
        "@a ; [a -> b | a -> c] & [a -> c | a -> d]",
        &[(shape_atom("a"), shape_atom("c"))],
    );
}

#[test]
fn sequence_composition_works_via_surface_syntax() {
    let program = r#"
rel r1 { a -> b }
rel r2 { b -> c }
"#;
    assert_query_exact(
        program,
        "@a ; r1 ; r2",
        &[(shape_atom("a"), shape_atom("c"))],
    );
}

#[test]
fn precedence_seq_binds_tighter_than_or() {
    assert_query_exact(
        "",
        "@a ; a -> b | a -> c ; c -> d",
        &[
            (shape_atom("a"), shape_atom("b")),
            (shape_atom("a"), shape_atom("d")),
        ],
    );
}

#[test]
fn bracket_grouping_overrides_default_precedence() {
    assert_query_exact(
        "",
        "@a ; [a -> b | a -> c] ; c -> d",
        &[(shape_atom("a"), shape_atom("d"))],
    );
}

#[test]
fn precedence_and_binds_tighter_than_seq() {
    assert_query_exact(
        "",
        "@a ; a -> b & a -> b ; b -> c",
        &[(shape_atom("a"), shape_atom("c"))],
    );
}

#[test]
fn sequence_associativity_holds() {
    assert_query_exact(
        "",
        "@a ; [a -> b ; b -> c] ; c -> d",
        &[(shape_atom("a"), shape_atom("d"))],
    );
    assert_query_exact(
        "",
        "@a ; a -> b ; [b -> c ; c -> d]",
        &[(shape_atom("a"), shape_atom("d"))],
    );
}

#[test]
fn disjunction_commutativity_holds_on_finite_queries() {
    assert_query_exact(
        "",
        "@a ; [a -> b | a -> c]",
        &[
            (shape_atom("a"), shape_atom("b")),
            (shape_atom("a"), shape_atom("c")),
        ],
    );
    assert_query_exact(
        "",
        "@a ; [a -> c | a -> b]",
        &[
            (shape_atom("a"), shape_atom("b")),
            (shape_atom("a"), shape_atom("c")),
        ],
    );
}

#[test]
fn conjunction_commutativity_holds_on_finite_queries() {
    let expected = [(shape_atom("a"), shape_atom("c"))];
    assert_query_exact("", "@a ; [a -> b | a -> c] & [a -> c | a -> d]", &expected);
    assert_query_exact("", "@a ; [a -> c | a -> d] & [a -> b | a -> c]", &expected);
}

#[test]
fn add_forward_examples_compute_expected_sums() {
    assert_query_exact(
        ADD_PROGRAM,
        "@(cons z (s (s z))) ; add",
        &[(cons_shape(shape_peano(0), shape_peano(2)), shape_peano(2))],
    );
    assert_query_exact(
        ADD_PROGRAM,
        "@(cons (s (s z)) (s z)) ; add",
        &[(cons_shape(shape_peano(2), shape_peano(1)), shape_peano(3))],
    );
}

#[test]
fn add_backward_for_two_returns_all_partitions() {
    assert_query_exact(
        ADD_PROGRAM,
        "add ; @(s (s z))",
        &[
            (cons_shape(shape_peano(0), shape_peano(2)), shape_peano(2)),
            (cons_shape(shape_peano(1), shape_peano(1)), shape_peano(2)),
            (cons_shape(shape_peano(2), shape_peano(0)), shape_peano(2)),
        ],
    );
}

#[test]
fn add_backward_for_three_returns_all_partitions() {
    assert_query_exact(
        ADD_PROGRAM,
        "add ; @(s (s (s z)))",
        &[
            (cons_shape(shape_peano(0), shape_peano(3)), shape_peano(3)),
            (cons_shape(shape_peano(1), shape_peano(2)), shape_peano(3)),
            (cons_shape(shape_peano(2), shape_peano(1)), shape_peano(3)),
            (cons_shape(shape_peano(3), shape_peano(0)), shape_peano(3)),
        ],
    );
}

#[test]
fn nat_relation_is_identity_on_bounded_forward_and_backward_queries() {
    let program = r#"
rel nat {
    z -> z
    |
    [(s $x) -> $x ; nat ; $y -> (s $y)]
}
"#;
    assert_query_exact(
        program,
        "@(s (s (s z))) ; nat",
        &[(shape_peano(3), shape_peano(3))],
    );
    assert_query_exact(
        program,
        "nat ; @(s (s z))",
        &[(shape_peano(2), shape_peano(2))],
    );
}

#[test]
fn mutual_recursion_even_odd_computes_expected_results() {
    assert_query_exact(
        EVEN_ODD_PROGRAM,
        "@(s (s z)) ; even",
        &[(shape_peano(2), shape_atom("yes"))],
    );
    assert_query_exact(
        EVEN_ODD_PROGRAM,
        "@(s z) ; odd",
        &[(shape_peano(1), shape_atom("yes"))],
    );
}

#[test]
fn mutual_recursion_even_backward_generates_even_inputs() {
    assert_query_contains(
        EVEN_ODD_PROGRAM,
        "even ; @yes",
        4,
        &[
            (shape_peano(0), shape_atom("yes")),
            (shape_peano(2), shape_atom("yes")),
            (shape_peano(4), shape_atom("yes")),
        ],
    );
}

#[test]
fn recursive_double_relation_doubles_peano_numbers() {
    let program = r#"
rel double {
    z -> z
    |
    [(s $x) -> $x ; double ; $y -> (s (s $y))]
}
"#;
    assert_query_exact(
        program,
        "@(s (s z)) ; double",
        &[(shape_peano(2), shape_peano(4))],
    );
}

#[test]
fn equality_guard_accepts_equal_pair() {
    assert_query_exact(
        EQ_NEQ_PROGRAM,
        "@(pair (s z) (s z)) ; same",
        &[(
            shape_app("pair", vec![shape_peano(1), shape_peano(1)]),
            shape_peano(1),
        )],
    );
}

#[test]
fn equality_guard_rejects_unequal_pair() {
    assert_query_exact(EQ_NEQ_PROGRAM, "@(pair z (s z)) ; same", &[]);
}

#[test]
fn disequality_guard_accepts_unequal_pair() {
    assert_query_exact(
        EQ_NEQ_PROGRAM,
        "@(pair z (s z)) ; different",
        &[(
            shape_app("pair", vec![shape_peano(0), shape_peano(1)]),
            shape_app("pair", vec![shape_peano(0), shape_peano(1)]),
        )],
    );
}

#[test]
fn disequality_guard_rejects_equal_pair() {
    assert_query_exact(EQ_NEQ_PROGRAM, "@(pair (s z) (s z)) ; different", &[]);
}

#[test]
fn nonzero_guard_rejects_zero() {
    assert_query_exact(EQ_NEQ_PROGRAM, "@z ; nonzero_ok", &[]);
}

#[test]
fn nonzero_guard_accepts_successor() {
    assert_query_exact(
        EQ_NEQ_PROGRAM,
        "@(s z) ; nonzero_ok",
        &[(shape_peano(1), shape_peano(1))],
    );
}

#[test]
fn between_closed_closed_accepts_bounds() {
    assert_query_exact(
        RANGE_PROGRAM,
        "@(pair z (range (closed z) (closed (s z)))) ; member",
        &[(
            shape_app(
                "pair",
                vec![
                    shape_peano(0),
                    shape_app(
                        "range",
                        vec![
                            shape_app("closed", vec![shape_peano(0)]),
                            shape_app("closed", vec![shape_peano(1)]),
                        ],
                    ),
                ],
            ),
            shape_peano(0),
        )],
    );
}

#[test]
fn between_open_open_rejects_endpoints_but_accepts_interior() {
    assert_query_exact(
        RANGE_PROGRAM,
        "@(pair z (range (open z) (open (s (s z))))) ; member",
        &[],
    );
    assert_query_exact(
        RANGE_PROGRAM,
        "@(pair (s z) (range (open z) (open (s (s z))))) ; member",
        &[(
            shape_app(
                "pair",
                vec![
                    shape_peano(1),
                    shape_app(
                        "range",
                        vec![
                            shape_app("open", vec![shape_peano(0)]),
                            shape_app("open", vec![shape_peano(2)]),
                        ],
                    ),
                ],
            ),
            shape_peano(1),
        )],
    );
}

#[test]
fn undefined_constraint_predicate_is_parse_error() {
    let mut parser = Parser::with_chr();
    let err = match parser.parse_rel_def("rel bad { $x { (missing $x) } -> $x }") {
        Ok(_) => panic!("expected unknown predicate parse error"),
        Err(err) => err,
    };
    assert!(
        err.to_string()
            .contains("unknown constraint predicate 'missing'"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn constraint_arity_mismatch_is_parse_error() {
    let mut parser = Parser::with_chr();
    parser
        .parse_theory_def(
            r#"
theory t {
    constraint p/1
}
"#,
        )
        .expect("parse theory");
    let err = match parser.parse_rel_def("rel bad { $x { (p $x $x) } -> $x }") {
        Ok(_) => panic!("expected arity mismatch parse error"),
        Err(err) => err,
    };
    assert!(
        err.to_string().contains("expects 1 args, got 2"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn theory_guard_variable_must_be_head_bound() {
    let mut parser = Parser::with_chr();
    let err = parser
        .parse_theory_def(
            r#"
theory bad_guard {
    constraint p/1
    (p $x) <=> (eq $y z) | true.
}
"#,
        )
        .expect_err("expected guard variable parse error");
    assert!(
        err.to_string().contains("must be bound by a head"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn repl_help_lists_core_commands() {
    let mut repl = Repl::new();
    let help = repl
        .process_input("help")
        .expect("help command")
        .expect("help output");
    assert!(help.contains("load <file>"), "missing load docs");
    assert!(help.contains("next [N]"), "missing next docs");
    assert!(help.contains("rel name"), "missing relation docs");
}

#[test]
fn repl_next_requires_positive_integer_argument() {
    let mut repl = Repl::new();
    let err_zero = repl
        .process_input("next 0")
        .expect_err("next 0 should error");
    assert!(
        err_zero.to_string().contains("must be > 0"),
        "unexpected error: {err_zero}"
    );

    let err_bad = repl
        .process_input("next nope")
        .expect_err("next nope should error");
    assert!(
        err_bad.to_string().contains("Invalid count for 'next'"),
        "unexpected error: {err_bad}"
    );
}

#[test]
fn repl_next_without_active_query_reports_status() {
    let mut repl = Repl::new();
    let msg = repl
        .process_input("next")
        .expect("next command")
        .expect("next output");
    assert!(
        msg.contains("No active query"),
        "unexpected next output: {}",
        msg
    );
}

#[test]
fn repl_reset_clears_active_query() {
    let mut repl = Repl::new();
    repl.process_input("rel f { a -> b | a -> c }")
        .expect("define relation");
    repl.process_input("f").expect("start query");
    repl.process_input("reset").expect("reset query");

    let msg = repl
        .process_input("next")
        .expect("next command")
        .expect("next output");
    assert!(
        msg.contains("No active query"),
        "expected reset to clear query, got: {}",
        msg
    );
}

#[test]
fn repl_theory_definition_clears_existing_relations() {
    let mut repl = Repl::new();
    repl.process_input("rel f { a -> b }")
        .expect("define relation");
    let listed_before = repl
        .process_input("list")
        .expect("list command")
        .expect("list output");
    assert!(listed_before.contains("f"), "relation should be listed");

    repl.process_input("theory t { constraint p/0 }")
        .expect("define theory");
    let listed_after = repl
        .process_input("list")
        .expect("list command")
        .expect("list output");
    assert_eq!(listed_after, "No relations or macros defined.");
}

#[test]
fn repl_load_file_supports_theory_and_relations() {
    let file = TempFile::new(
        "load_ok",
        r#"
theory t {
    constraint p/0
}

rel f {
    a -> b
}
"#,
    );
    let mut repl = Repl::new();
    let msg = repl
        .process_input(&format!("load {}", file.path().display()))
        .expect("load file")
        .expect("load output");
    assert!(
        msg.contains("Loaded 1 theory block(s)"),
        "missing theory load count: {}",
        msg
    );
    assert!(
        msg.contains("Loaded 1 relation(s)"),
        "missing relation load count: {}",
        msg
    );

    let query = repl
        .process_input("f")
        .expect("run query")
        .expect("query output");
    assert!(
        query.contains("a -> b"),
        "loaded relation should execute, got: {}",
        query
    );
}

#[test]
fn repl_load_file_reports_parse_errors() {
    let file = TempFile::new(
        "load_err",
        r#"
rel bad {
    a -> b
"#,
    );
    let mut repl = Repl::new();
    let err = repl
        .process_input(&format!("load {}", file.path().display()))
        .expect_err("load should fail");
    let err_msg = err.to_string();
    assert!(
        err_msg.contains("Parse error") || err_msg.contains("Unterminated block definition"),
        "unexpected error: {}",
        err_msg
    );
}

#[test]
fn split_statements_handles_comments_and_multiline_blocks() {
    let statements = split_statements(
        r#"
# comment
rel a {
    x -> y
}

rel b {
    y -> z
}

# query
@x ; a ; b
"#,
    )
    .expect("split statements");

    assert_eq!(statements.len(), 3);
    assert!(statements[0].starts_with("rel a {"));
    assert!(statements[1].starts_with("rel b {"));
    assert!(statements[2].starts_with("@x ; a ; b"));
}

#[test]
fn repl_process_cell_supports_mixed_definition_and_query() {
    let mut repl = Repl::new();
    let output = repl
        .process_cell("rel f { a -> b }\n@a ; f")
        .expect("process cell")
        .expect("cell output");
    assert!(
        output.contains("1."),
        "expected answer output for query line, got: {}",
        output
    );
}

#[test]
fn repl_exit_and_quit_return_quit_signal() {
    let mut repl = Repl::new();
    let quit_err = repl.process_input("quit").expect_err("quit should error");
    assert_eq!(quit_err, ReplError::Quit);

    let exit_err = repl.process_input("exit").expect_err("exit should error");
    assert_eq!(exit_err, ReplError::Quit);
}

#[test]
fn large_peano_input_can_be_constructed_for_queries() {
    let n = peano_term(8);
    let query = format!("@{} ; id", n);
    assert_query_exact(BASIC_PROGRAM, &query, &[(shape_peano(8), shape_peano(8))]);
}

// =========================================================================
// Equality constraints in theories ($x = $y)
// =========================================================================

#[test]
fn equality_constraint_in_theory_produces_correct_binding() {
    // A theory where p(X, Y) uses $X = $Y to unify args.
    // When both args are the same ground term, the rule fires normally.
    let program = r#"
theory eq_theory {
  constraint p/2
  constraint q/1
  (p $x $y) <=> $x = $y, (q $x).
}

rel r { (pair $a $a) { (p $a $a) } -> $a }
"#;
    assert_query_exact(
        program,
        "@(pair z z) ; r",
        &[(
            shape_app("pair", vec![shape_atom("z"), shape_atom("z")]),
            shape_atom("z"),
        )],
    );
}

#[test]
fn equality_constraint_failure_kills_branch() {
    // When args differ, $x = $y fails and the whole body fails.
    let program = r#"
theory eq_theory {
  constraint p/2
  (p $x $y) <=> $x = $y.
}

rel r { (pair $a $b) { (p $a $b) } -> $a }
"#;
    // p(a, b) where a != b → body fails → no results.
    assert_query_exact(program, "@(pair a b) ; r", &[]);
}

#[test]
fn equality_constraint_grounds_nf_pattern_via_substitution() {
    // $b appears only in the RHS — it's fresh/existential.
    // The guard posts (p $a $b), which fires $a = $b, binding $b to $a's value.
    // Without the constraint, $b would remain free in the output.
    // With the constraint, querying @z ; r should produce z -> (pair z z):
    // $a matches z from input, $b gets bound to z via the equality.
    let program = r#"
theory eq_theory {
  constraint p/2
  (p $x $y) <=> $x = $y.
}

rel r { $a { (p $a $b) } -> (pair $a $b) }
"#;
    assert_query_exact(
        program,
        "@z ; r",
        &[(
            shape_atom("z"),
            shape_app("pair", vec![shape_atom("z"), shape_atom("z")]),
        )],
    );
}

// =========================================================================
// Parameterized relation macros
// =========================================================================

#[test]
fn macro_non_recursive_definition_and_expansion() {
    // Define a macro that composes a relation with itself
    let program = r#"
rel double(r) {
    r ; r
}

rel inc {
    $x -> (s $x)
}
"#;
    // double(inc) should expand to inc ; inc, i.e., increment by 2
    assert_query_exact(
        program,
        "@z ; double(inc)",
        &[(shape_atom("z"), shape_peano(2))],
    );
}

#[test]
fn macro_non_recursive_with_two_params() {
    // Macro that sequences two relation-valued params
    let program = r#"
rel then(first, second) {
    first ; second
}

rel inc {
    $x -> (s $x)
}

rel wrap {
    $x -> (box $x)
}
"#;
    assert_query_exact(
        program,
        "@z ; then(inc, wrap)",
        &[(shape_atom("z"), shape_app("box", vec![shape_peano(1)]))],
    );
}

#[test]
fn macro_non_recursive_with_or() {
    // Macro that creates a choice between two relations
    let program = r#"
rel either(a, b) {
    a | b
}

rel toa { $x -> (pA $x) }
rel tob { $x -> (pB $x) }
"#;
    assert_query_exact(
        program,
        "@z ; either(toa, tob)",
        &[
            (shape_atom("z"), shape_app("pA", vec![shape_atom("z")])),
            (shape_atom("z"), shape_app("pB", vec![shape_atom("z")])),
        ],
    );
}

#[test]
fn macro_arity_overloading_e2e() {
    // foo/0 and foo/1 are completely different
    let program = r#"
rel foo {
    a -> b
}

rel foo(r) {
    r ; r
}

rel inc { $x -> (s $x) }
"#;
    // Bare foo uses foo/0 (a -> b)
    assert_query_exact(program, "foo", &[(shape_atom("a"), shape_atom("b"))]);
    // foo(inc) uses foo/1 (inc ; inc = add 2)
    assert_query_exact(
        program,
        "@z ; foo(inc)",
        &[(shape_atom("z"), shape_peano(2))],
    );
}

#[test]
fn macro_cross_call_e2e() {
    // Macro A calls macro B: compose(f, g) = f ; g, then double(r) = compose(r, r)
    let program = r#"
rel compose(f, g) {
    f ; g
}

rel double(r) {
    compose(r, r)
}

rel inc { $x -> (s $x) }
"#;
    assert_query_exact(
        program,
        "@z ; double(inc)",
        &[(shape_atom("z"), shape_peano(2))],
    );
}

#[test]
fn macro_recursive_identity_self_call_e2e() {
    // Recursive macro: peel strips (s ...) layers and then applies a base relation.
    // peel(base) = (s $x) -> $x ; peel(base) | base
    let program = r#"
rel peel(base) {
    (s $x) -> $x ; peel(base)
    | base
}
"#;
    // peel(z -> done) on (s (s z)) should strip two layers and produce done
    assert_query_exact(
        program,
        "@(s (s z)) ; peel(z -> done)",
        &[(shape_peano(2), shape_atom("done"))],
    );
}

#[test]
fn macro_repl_define_reports_name_and_arity() {
    let mut repl = Repl::new();
    let msg = repl
        .process_input("rel foo(x) { x ; x }")
        .expect("define macro")
        .expect("macro output");
    assert!(
        msg.contains("Defined macro 'foo/1'"),
        "Expected macro definition message, got: {}",
        msg
    );
}

#[test]
fn macro_repl_define_two_params_reports_arity() {
    let mut repl = Repl::new();
    let msg = repl
        .process_input("rel bar(a, b) { a ; b }")
        .expect("define macro")
        .expect("macro output");
    assert!(
        msg.contains("Defined macro 'bar/2'"),
        "Expected macro definition message, got: {}",
        msg
    );
}

#[test]
fn macro_repl_list_shows_macros() {
    let mut repl = Repl::new();
    repl.process_input("rel foo(x) { x ; x }")
        .expect("define macro");
    repl.process_input("rel f { a -> b }")
        .expect("define relation");
    let list = repl
        .process_input("list")
        .expect("list command")
        .expect("list output");
    assert!(
        list.contains("foo/1"),
        "Expected macro in list output, got: {}",
        list
    );
    assert!(
        list.contains('f'),
        "Expected relation in list output, got: {}",
        list
    );
}

#[test]
fn macro_repl_query_non_recursive() {
    let mut repl = Repl::new();
    repl.process_input("rel double(r) { r ; r }")
        .expect("define macro");
    repl.process_input("rel inc { $x -> (s $x) }")
        .expect("define relation");
    let output = repl
        .process_input("@z ; double(inc)")
        .expect("run query")
        .expect("query output");
    assert!(
        output.contains("(s (s z))"),
        "Expected double increment result, got: {}",
        output
    );
}

#[test]
fn macro_repl_query_recursive() {
    let mut repl = Repl::new();
    repl.process_input("rel peel(base) { (s $x) -> $x ; peel(base) | base }")
        .expect("define macro");
    let output = repl
        .process_input("@(s (s z)) ; peel(z -> done)")
        .expect("run query")
        .expect("query output");
    assert!(
        output.contains("done"),
        "Expected peeled result 'done', got: {}",
        output
    );
}

#[test]
fn macro_load_file_counts_macros() {
    let file = TempFile::new(
        "macro_load",
        r#"
rel double(r) {
    r ; r
}

rel inc {
    $x -> (s $x)
}
"#,
    );
    let mut repl = Repl::new();
    let msg = repl
        .process_input(&format!("load {}", file.path().display()))
        .expect("load file")
        .expect("load output");
    assert!(
        msg.contains("1 macro"),
        "Expected macro count in load output, got: {}",
        msg
    );
    assert!(
        msg.contains("1 relation"),
        "Expected relation count in load output, got: {}",
        msg
    );
}

#[test]
fn macro_undefined_call_errors_in_repl() {
    let mut repl = Repl::new();
    let err = repl
        .process_input("@z ; undefined_macro([$x -> $x])")
        .expect_err("should fail");
    assert!(
        err.to_string().contains("Parse error"),
        "Expected parse error for undefined macro, got: {}",
        err
    );
}

#[test]
fn macro_wrong_arity_errors_in_repl() {
    let mut repl = Repl::new();
    repl.process_input("rel foo(x) { x ; x }")
        .expect("define macro");
    let err = repl
        .process_input("@z ; foo([$x -> $x], [$y -> $y])")
        .expect_err("should fail");
    assert!(
        err.to_string().contains("Parse error"),
        "Expected parse error for wrong arity, got: {}",
        err
    );
}

#[test]
fn macro_complex_arg_expression() {
    // Macro arguments can be full relation expressions with |, ;, &
    let program = r#"
rel apply(r) {
    r
}
"#;
    // apply(a -> b | a -> c) should give both results
    assert_query_exact(
        program,
        "@a ; apply(a -> b | a -> c)",
        &[
            (shape_atom("a"), shape_atom("b")),
            (shape_atom("a"), shape_atom("c")),
        ],
    );
}

#[test]
fn macro_param_does_not_leak_into_later_definitions() {
    // After defining a macro with param x, using 'x' in later code
    // should not refer to the macro's parameter
    let program = r#"
rel foo(x) {
    x ; x
}

rel x {
    a -> b
}
"#;
    // Bare 'x' should be the relation x: a -> b, not the macro param
    assert_query_exact(program, "x", &[(shape_atom("a"), shape_atom("b"))]);
}

// =========================================================================
// Macro forward references
// =========================================================================

#[test]
fn macro_forward_reference_in_macro_body() {
    // double is defined BEFORE compose, but double's body calls compose.
    let program = r#"
rel double(r) {
    compose(r, r)
}

rel compose(f, g) {
    f ; g
}

rel inc { $x -> (s $x) }
"#;
    assert_query_exact(
        program,
        "@z ; double(inc)",
        &[(shape_atom("z"), shape_peano(2))],
    );
}

#[test]
fn macro_mutual_forward_references() {
    // Both macros reference each other's existence, though only one
    // actually calls the other (mutual calls would require recursion).
    // Here: apply_twice calls double, double calls compose.
    // Defined in reverse dependency order.
    let program = r#"
rel apply_twice(f) {
    double(f)
}

rel double(r) {
    compose(r, r)
}

rel compose(f, g) {
    f ; g
}

rel inc { $x -> (s $x) }
"#;
    assert_query_exact(
        program,
        "@z ; apply_twice(inc)",
        &[(shape_atom("z"), shape_peano(2))],
    );
}

#[test]
fn macro_forward_reference_in_regular_relation() {
    // A regular relation's body uses a macro defined later in the file.
    let program = r#"
rel inc { $x -> (s $x) }

rel add_two {
    double(inc)
}

rel double(r) {
    r ; r
}
"#;
    assert_query_exact(
        program,
        "@z ; add_two",
        &[(shape_atom("z"), shape_peano(2))],
    );
}

#[test]
fn macro_forward_reference_recursive_macro() {
    // A recursive macro references a non-recursive macro defined later.
    let program = r#"
rel peel(base) {
    (s $x) -> $x ; peel(base)
    | wrap(base)
}

rel wrap(r) {
    r
}
"#;
    assert_query_exact(
        program,
        "@(s z) ; peel(z -> done)",
        &[(shape_peano(1), shape_atom("done"))],
    );
}

#[test]
fn macro_forward_ref_load_file() {
    let file = TempFile::new(
        "macro_fwd",
        r#"
rel double(r) {
    compose(r, r)
}

rel compose(f, g) {
    f ; g
}

rel inc {
    $x -> (s $x)
}
"#,
    );
    let mut repl = Repl::new();
    let msg = repl
        .process_input(&format!("load {}", file.path().display()))
        .expect("load file")
        .expect("load output");
    assert!(
        msg.contains("1 relation"),
        "Expected relation count, got: {}",
        msg
    );
    assert!(
        msg.contains("2 macro"),
        "Expected macro count, got: {}",
        msg
    );

    let output = repl
        .process_input("@z ; double(inc)")
        .expect("run query")
        .expect("query output");
    assert!(
        output.contains("(s (s z))"),
        "Expected double increment result, got: {}",
        output
    );
}
