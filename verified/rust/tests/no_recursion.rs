//! No function of the crate calls itself, directly or through another.
//!
//! Aeneas translates a loop to its `loop` combinator and a recursive function
//! to a definition by `partial_fixpoint` (or, with a termination proof, by
//! `termination_by`). The generated Lean is checked against the Rust in CI,
//! so its text decides the question.

#[test]
fn the_translation_has_no_recursive_definition() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../lean/RwlogCore/Funs.lean");
    let text = std::fs::read_to_string(path).expect("the generated Lean");
    assert!(text.contains("rwlog_core::term::rebuild"), "not the translation of this crate");
    for (i, line) in text.lines().enumerate() {
        let t = line.trim_start();
        for mark in ["partial_fixpoint", "termination_by", "decreasing_by", "divergent", "mutual"] {
            assert!(!t.starts_with(mark), "line {}: recursive definition ({mark})", i + 1);
        }
    }
}
