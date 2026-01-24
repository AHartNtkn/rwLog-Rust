use rwlog::repl::Repl;

#[test]
fn repl_query_composes_named_relations() {
    let mut repl = Repl::new();
    repl.process_input("rel f { a -> b }")
        .expect("define f")
        .expect("f output");
    repl.process_input("rel g { b -> c }")
        .expect("define g")
        .expect("g output");

    let output = repl
        .process_input("f ; g")
        .expect("query should run")
        .expect("query output");

    assert!(
        output.starts_with("1."),
        "Expected at least one answer, got: {}",
        output
    );
}
