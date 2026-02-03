use super::Repl;
use serde_json::Value;
use std::fs;
use std::path::Path;

fn load_notebook_code_cells(path: &Path) -> Result<Vec<String>, String> {
    let content = fs::read_to_string(path)
        .map_err(|e| format!("Failed to read notebook '{}': {}", path.display(), e))?;
    let json: Value = serde_json::from_str(&content)
        .map_err(|e| format!("Failed to parse notebook '{}': {}", path.display(), e))?;
    let cells = json
        .get("cells")
        .and_then(|v| v.as_array())
        .ok_or_else(|| format!("Notebook '{}' missing cells array", path.display()))?;
    let mut out = Vec::new();
    for cell in cells {
        let cell_type = cell
            .get("cell_type")
            .and_then(|v| v.as_str())
            .unwrap_or_default();
        if cell_type != "code" {
            continue;
        }
        let source = cell
            .get("source")
            .ok_or_else(|| format!("Notebook '{}' missing cell source", path.display()))?;
        let src = if let Some(lines) = source.as_array() {
            let mut merged = String::new();
            for line in lines {
                if let Some(s) = line.as_str() {
                    merged.push_str(s);
                }
            }
            merged
        } else if let Some(s) = source.as_str() {
            s.to_string()
        } else {
            return Err(format!(
                "Notebook '{}' cell source has unexpected type",
                path.display()
            ));
        };
        out.push(src);
    }
    Ok(out)
}

fn adjust_load_paths(cell: &str, base_dir: &Path) -> String {
    let mut out_lines = Vec::new();
    for line in cell.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("load ") {
            let path_str = rest.trim();
            let path = Path::new(path_str);
            let adjusted = if path.exists() {
                None
            } else {
                let candidate = base_dir.join(path_str);
                if candidate.exists() {
                    Some(candidate)
                } else {
                    None
                }
            };
            if let Some(path) = adjusted {
                let leading: String = line.chars().take_while(|c| c.is_whitespace()).collect();
                out_lines.push(format!("{}load {}", leading, path.display()));
                continue;
            }
        }
        out_lines.push(line.to_string());
    }
    out_lines.join("\n")
}

fn cell_has_query(cell: &str) -> bool {
    let mut brace_depth: i32 = 0;
    for line in cell.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        if brace_depth > 0 {
            brace_depth += trimmed.chars().filter(|&ch| ch == '{').count() as i32;
            brace_depth -= trimmed.chars().filter(|&ch| ch == '}').count() as i32;
            continue;
        }
        if trimmed.starts_with("rel ") || trimmed.starts_with("theory ") {
            brace_depth += trimmed.chars().filter(|&ch| ch == '{').count() as i32;
            brace_depth -= trimmed.chars().filter(|&ch| ch == '}').count() as i32;
            continue;
        }
        if trimmed.starts_with("load ")
            || trimmed == "next"
            || trimmed == "reset"
            || trimmed == "list"
            || trimmed == "help"
            || trimmed.starts_with("more ")
        {
            continue;
        }
        return true;
    }
    false
}

#[test]
fn repl_process_cell_handles_multiple_lines() {
    let mut repl = Repl::new();
    let output = repl
        .process_cell("rel f { a -> b }\nf")
        .expect("process cell");
    assert!(
        output.unwrap_or_default().contains("1."),
        "Expected output from query line"
    );
}

#[test]
fn repl_process_cell_handles_comment_then_query() {
    let mut repl = Repl::new();
    repl.process_input("rel f { a -> b }").expect("define f");
    // Simulates a notebook cell with a comment header followed by a query
    let output = repl
        .process_cell("# This is a comment\nf")
        .expect("process cell with leading comment");
    assert!(
        output.unwrap_or_default().contains("1."),
        "Expected output from query after comment line"
    );
}

#[test]
fn repl_query_renders_rule_syntax() {
    let mut repl = Repl::new();
    repl.process_input("rel f { a -> b }").expect("define f");
    let output = repl
        .process_input("f")
        .expect("run query")
        .unwrap_or_default();
    assert!(
        output.contains("a -> b"),
        "Expected rule syntax in output, got: {}",
        output
    );
}

#[test]
fn repl_bare_query_runs_as_query() {
    let mut repl = Repl::new();
    let output = repl
        .process_input("@z")
        .expect("process bare query")
        .unwrap_or_default();
    assert!(
        output.contains("1."),
        "Expected answer numbering for bare query, got: {}",
        output
    );
}

#[test]
fn repl_next_advances_through_answers() {
    let mut repl = Repl::new();
    repl.process_input("rel f { a -> b | a -> c }")
        .expect("define f")
        .expect("define output");

    let first = repl
        .process_input("f")
        .expect("run query")
        .unwrap_or_default();
    assert!(first.contains("1."), "Expected first answer");

    let second = repl
        .process_input("next")
        .expect("next answer")
        .unwrap_or_default();
    assert!(second.contains("2."), "Expected second answer");

    let done = repl
        .process_input("next")
        .expect("next after exhausted")
        .unwrap_or_default();
    assert!(
        done.contains("No more answers"),
        "Expected exhaustion notice"
    );
}

#[test]
fn theory_notebook_demo_cells_run() {
    let mut repl = Repl::new();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let notebook = root.join("examples/theory_demos.ipynb");
    let base_dir = notebook
        .parent()
        .expect("notebook should have parent directory");
    let cells = load_notebook_code_cells(&notebook).expect("load notebook cells");

    for (idx, cell) in cells.iter().enumerate() {
        let adjusted = adjust_load_paths(cell, base_dir);
        let output = repl
            .process_cell(&adjusted)
            .unwrap_or_else(|e| panic!("cell {} failed: {}", idx, e));
        if cell_has_query(&adjusted) {
            let out = output.unwrap_or_default();
            assert!(
                out.contains("1."),
                "Expected an answer in cell {} output: {}",
                idx,
                out
            );
        } else if adjusted.trim_start().starts_with("load ") {
            let out = output.unwrap_or_default();
            assert!(
                out.contains("Loaded"),
                "Expected load output in cell {}: {}",
                idx,
                out
            );
        }
    }
}

#[test]
fn chr_simple_equality_guard() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let theory_path = root.join("examples/equality_constraints.txt");

    // Load the theory
    let load_result = repl.process_input(&format!("load {}", theory_path.display()));
    assert!(load_result.is_ok(), "Failed to load theory: {:?}", load_result);

    // Define a simple relation with an eq constraint
    let def_result = repl.process_input("rel same { (pair $x $y) { (eq $x $y) } -> $x }");
    assert!(def_result.is_ok(), "Failed to define relation: {:?}", def_result);

    // Run a query - equal terms should succeed
    let query_result = repl.process_input("@(pair z z) ; same");
    eprintln!("Query result: {:?}", query_result);
    let output = query_result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected answer, got: {}", output);
}

#[test]
fn chr_notebook_cell_0_load_and_define() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let theory_path = root.join("examples/equality_constraints.txt");

    // Cell 0: load + define relations
    eprintln!("Loading theory...");
    let load_result = repl.process_input(&format!("load {}", theory_path.display()));
    assert!(load_result.is_ok(), "Failed to load theory: {:?}", load_result);

    eprintln!("Defining same...");
    let def_same = repl.process_input("rel same { (pair $x $y) { (eq $x $y) } -> $x }");
    assert!(def_same.is_ok(), "Failed to define same: {:?}", def_same);

    eprintln!("Defining different...");
    let def_different = repl.process_input("rel different { (pair $x $y) { (neq $x $y) } -> (pair $x $y) }");
    assert!(def_different.is_ok(), "Failed to define different: {:?}", def_different);

    eprintln!("Defining nonzero_ok...");
    let def_nz = repl.process_input("rel nonzero_ok { $x { (nonzero $x) } -> $x }");
    assert!(def_nz.is_ok(), "Failed to define nonzero_ok: {:?}", def_nz);
}

#[test]
fn chr_notebook_cell_1_equal_query() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let theory_path = root.join("examples/equality_constraints.txt");

    repl.process_input(&format!("load {}", theory_path.display())).unwrap();
    repl.process_input("rel same { (pair $x $y) { (eq $x $y) } -> $x }").unwrap();

    eprintln!("Running equal query...");
    let result = repl.process_input("@(pair (s (s z)) (s (s z))) ; same");
    eprintln!("Result: {:?}", result);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected answer, got: {}", output);
}

#[test]
fn chr_notebook_cell_2_different_query() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let theory_path = root.join("examples/equality_constraints.txt");

    repl.process_input(&format!("load {}", theory_path.display())).unwrap();
    repl.process_input("rel different { (pair $x $y) { (neq $x $y) } -> (pair $x $y) }").unwrap();

    eprintln!("Running different query...");
    let result = repl.process_input("@(pair (s z) z) ; different");
    eprintln!("Result: {:?}", result);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected answer, got: {}", output);
}

#[test]
fn chr_notebook_cell_3_nonzero_query() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let theory_path = root.join("examples/equality_constraints.txt");

    repl.process_input(&format!("load {}", theory_path.display())).unwrap();
    repl.process_input("rel nonzero_ok { $x { (nonzero $x) } -> $x }").unwrap();

    eprintln!("Running nonzero query...");
    let result = repl.process_input("@(s z) ; nonzero_ok");
    eprintln!("Result: {:?}", result);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected answer, got: {}", output);
}

#[test]
fn chr_range_sets_load_theory() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let theory_path = root.join("examples/range_sets.txt");

    eprintln!("Loading range_sets theory...");
    let load_result = repl.process_input(&format!("load {}", theory_path.display()));
    eprintln!("Load result: {:?}", load_result);
    assert!(load_result.is_ok(), "Failed to load theory: {:?}", load_result);
}

#[test]
fn chr_range_sets_leq_ok() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let theory_path = root.join("examples/range_sets.txt");

    repl.process_input(&format!("load {}", theory_path.display())).unwrap();
    repl.process_input("rel leq_ok { (pair $x $y) { (leq $x $y) } -> (pair $x $y) }").unwrap();

    eprintln!("Running leq_ok query...");
    let result = repl.process_input("@(pair (s z) (s (s z))) ; leq_ok");
    eprintln!("Result: {:?}", result);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected answer, got: {}", output);
}

#[test]
fn chr_range_sets_pred_rel() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let theory_path = root.join("examples/range_sets.txt");

    repl.process_input(&format!("load {}", theory_path.display())).unwrap();
    repl.process_input("rel pred { (s $x) -> $x }").unwrap();

    eprintln!("Running pred query...");
    let result = repl.process_input("@(s (s z)) ; pred");
    eprintln!("Result: {:?}", result);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected answer, got: {}", output);
}

#[test]
fn chr_range_sets_close_range_base_case() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let theory_path = root.join("examples/range_sets.txt");

    repl.process_input(&format!("load {}", theory_path.display())).unwrap();
    // Just the first branch - base case
    repl.process_input("rel close_range_base { (range $lo (open z)) -> empty }").unwrap();

    eprintln!("Running close_range base query...");
    let result = repl.process_input("@(range (closed z) (open z)) ; close_range_base");
    eprintln!("Result: {:?}", result);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected answer, got: {}", output);
}

#[test]
fn chr_range_sets_card_range_base() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let theory_path = root.join("examples/range_sets.txt");

    repl.process_input(&format!("load {}", theory_path.display())).unwrap();
    // Base case of card_range
    repl.process_input("rel card_base { empty -> z }").unwrap();

    eprintln!("Running card_base query...");
    let result = repl.process_input("@empty ; card_base");
    eprintln!("Result: {:?}", result);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected answer, got: {}", output);
}

#[test]
fn chr_range_sets_card_range_full() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let theory_path = root.join("examples/range_sets.txt");

    repl.process_input(&format!("load {}", theory_path.display())).unwrap();

    // Full card_range with recursion - this is likely where the hang is
    let def = r#"rel card_range {
        empty -> z
        |
        (range (closed $x) (closed $x)) -> (s z)
        |
        (range (closed $lo) (closed $hi)) { (lt $hi $lo) } -> z
        |
        (range (closed $lo) (closed $hi)) { (lt $lo $hi) }
            -> (range (closed (s $lo)) (closed $hi)) ; card_range ; $n -> (s $n)
    }"#;
    repl.process_input(def).unwrap();

    eprintln!("Running card_range recursive query...");
    // Try a small range first: [0,1] = 2 elements
    let result = repl.process_input("@(range (closed z) (closed (s z))) ; card_range");
    eprintln!("Result: {:?}", result);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected answer, got: {}", output);
}

#[test]
fn simple_recursive_without_chr() {
    let mut repl = Repl::new();

    // Simplest recursive case without any CHR guards
    let def = r#"rel peel {
        z -> z
        |
        (s $x) -> $x ; peel
    }"#;
    eprintln!("Defining peel...");
    repl.process_input(def).unwrap();

    eprintln!("Running query on (s (s z))...");
    let result = repl.process_input("@(s (s z)) ; peel");
    eprintln!("Result: {:?}", result);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected answer for peel, got: {}", output);
}

#[test]
fn chr_recursive_guard_minimal() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let theory_path = root.join("examples/range_sets.txt");

    repl.process_input(&format!("load {}", theory_path.display())).unwrap();

    // Simplest recursive case with CHR guard - should hit base case immediately
    let def = r#"rel test_rec {
        z -> z
        |
        (s $x) { (lt z (s $x)) } -> $x ; test_rec
    }"#;
    eprintln!("Defining test_rec...");
    repl.process_input(def).unwrap();

    eprintln!("Running query on (s z)...");
    // (s z) should: match second branch, guard (lt z (s z)) succeeds,
    // recursively call test_rec on z, which hits base case
    let result = repl.process_input("@(s z) ; test_rec");
    eprintln!("Result: {:?}", result);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected answer, got: {}", output);
}

#[test]
fn chr_notebook_sequential_flow() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));

    eprintln!("=== Cell 0: Load equality_constraints + define relations ===");
    let eq_theory = root.join("examples/equality_constraints.txt");
    repl.process_cell(&format!("load {}\n\nrel same {{\n    (pair $x $y) {{ (eq $x $y) }} -> $x\n}}\n\nrel different {{\n    (pair $x $y) {{ (neq $x $y) }} -> (pair $x $y)\n}}\n\nrel nonzero_ok {{\n    $x {{ (nonzero $x) }} -> $x\n}}", eq_theory.display())).expect("cell 0 failed");
    eprintln!("Cell 0 complete");

    eprintln!("=== Cell 1: Equal numbers query ===");
    let out1 = repl.process_cell("@(pair (s (s z)) (s (s z))) ; same").expect("cell 1 failed").unwrap_or_default();
    eprintln!("Cell 1 output: {}", out1);
    assert!(out1.contains("1."), "Cell 1 should have answer");

    eprintln!("=== Cell 1b: next ===");
    let out1b = repl.process_cell("next").expect("cell 1b failed").unwrap_or_default();
    eprintln!("Cell 1b output: {}", out1b);

    eprintln!("=== Cell 2: Different numbers query ===");
    let out2 = repl.process_cell("@(pair (s z) z) ; different").expect("cell 2 failed").unwrap_or_default();
    eprintln!("Cell 2 output: {}", out2);
    assert!(out2.contains("1."), "Cell 2 should have answer");

    eprintln!("=== Cell 2b: next ===");
    let out2b = repl.process_cell("next").expect("cell 2b failed").unwrap_or_default();
    eprintln!("Cell 2b output: {}", out2b);

    eprintln!("=== Cell 3: nonzero query ===");
    let out3 = repl.process_cell("@(s z) ; nonzero_ok").expect("cell 3 failed").unwrap_or_default();
    eprintln!("Cell 3 output: {}", out3);
    assert!(out3.contains("1."), "Cell 3 should have answer");

    eprintln!("=== Cell 3b: next ===");
    let out3b = repl.process_cell("next").expect("cell 3b failed").unwrap_or_default();
    eprintln!("Cell 3b output: {}", out3b);

    eprintln!("=== Cell 4: Load range_sets + define relations ===");
    let range_theory = root.join("examples/range_sets.txt");
    // This is the complex cell from the notebook that loads range_sets and defines many relations
    let cell4 = format!(r#"load {}

rel pred {{
    (s $x) -> $x
}}

rel close_range {{
    (range $lo (open z)) -> empty
    |
    (range (closed $lo) (closed $hi)) -> (range (closed $lo) (closed $hi))
    |
    (range (open $lo) (closed $hi)) -> (range (closed (s $lo)) (closed $hi))
    |
    [(range (closed $lo) (open $hi)) -> $hi ; pred ; $hi2 -> (range (closed $lo) (closed $hi2))]
    |
    [(range (open $lo) (open $hi)) -> $hi ; pred ; $hi2 -> (range (closed (s $lo)) (closed $hi2))]
}}

rel card_range {{
    empty -> z
    |
    (range (closed $x) (closed $x)) -> (s z)
    |
    (range (closed $lo) (closed $hi)) {{ (lt $hi $lo) }} -> z
    |
    (range (closed $lo) (closed $hi)) {{ (lt $lo $hi) }}
        -> (range (closed (s $lo)) (closed $hi)) ; card_range ; $n -> (s $n)
}}

rel card {{
    close_range ; card_range
}}

rel leq_ok {{
    (pair $x $y) {{ (leq $x $y) }} -> (pair $x $y)
}}

rel member {{
    (pair $x (rcons $range $rest)) {{ (between $x $range) }} -> $x
    |
    (pair $x (rcons $range $rest)) -> (pair $x $rest) ; member
}}"#, range_theory.display());
    eprintln!("Processing cell 4...");
    let out4 = repl.process_cell(&cell4).expect("cell 4 failed").unwrap_or_default();
    eprintln!("Cell 4 output: {}", out4);
    assert!(out4.contains("Loaded"), "Cell 4 should load theory");

    eprintln!("=== Cell 5: member query ===");
    let out5 = repl.process_cell("@(pair (s (s z)) (rcons (range (closed z) (open (s (s (s z))))) rnil)) ; member").expect("cell 5 failed").unwrap_or_default();
    eprintln!("Cell 5 output: {}", out5);
    assert!(out5.contains("1."), "Cell 5 should have answer");

    eprintln!("=== Cell 5b: next ===");
    let _ = repl.process_cell("next");

    eprintln!("=== Cell 6: card query (cardinality of [0,3)) ===");
    let out6 = repl.process_cell("@(range (closed z) (open (s (s (s z))))) ; card").expect("cell 6 failed").unwrap_or_default();
    eprintln!("Cell 6 output: {}", out6);
    assert!(out6.contains("1."), "Cell 6 should have answer");

    eprintln!("=== Cell 6b: next ===");
    let _ = repl.process_cell("next");

    eprintln!("=== Cell 7: leq_ok query ===");
    let out7 = repl.process_cell("@(pair (s z) (s (s z))) ; leq_ok").expect("cell 7 failed").unwrap_or_default();
    eprintln!("Cell 7 output: {}", out7);
    assert!(out7.contains("1."), "Cell 7 should have answer");

    eprintln!("=== Cell 7b: next ===");
    let _ = repl.process_cell("next");

    eprintln!("All cells complete!");
}

#[test]
fn chr_card_query_isolated() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let range_theory = root.join("examples/range_sets.txt");

    repl.process_input(&format!("load {}", range_theory.display())).unwrap();
    repl.process_input("rel pred { (s $x) -> $x }").unwrap();
    repl.process_input(r#"rel close_range {
        (range $lo (open z)) -> empty
        |
        (range (closed $lo) (closed $hi)) -> (range (closed $lo) (closed $hi))
        |
        (range (open $lo) (closed $hi)) -> (range (closed (s $lo)) (closed $hi))
        |
        [(range (closed $lo) (open $hi)) -> $hi ; pred ; $hi2 -> (range (closed $lo) (closed $hi2))]
        |
        [(range (open $lo) (open $hi)) -> $hi ; pred ; $hi2 -> (range (closed (s $lo)) (closed $hi2))]
    }"#).unwrap();
    repl.process_input(r#"rel card_range {
        empty -> z
        |
        (range (closed $x) (closed $x)) -> (s z)
        |
        (range (closed $lo) (closed $hi)) { (lt $hi $lo) } -> z
        |
        (range (closed $lo) (closed $hi)) { (lt $lo $hi) }
            -> (range (closed (s $lo)) (closed $hi)) ; card_range ; $n -> (s $n)
    }"#).unwrap();
    repl.process_input("rel card { close_range ; card_range }").unwrap();

    eprintln!("Running card query on [0,3)...");
    // [0,3) open = elements 0,1,2 = cardinality 3
    let result = repl.process_input("@(range (closed z) (open (s (s (s z))))) ; card");
    eprintln!("Result: {:?}", result);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected answer, got: {}", output);
}

#[test]
fn chr_member_then_next_hangs() {
    let mut repl = Repl::new();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let range_theory = root.join("examples/range_sets.txt");

    repl.process_input(&format!("load {}", range_theory.display())).unwrap();
    repl.process_input(r#"rel member {
        (pair $x (rcons $range $rest)) { (between $x $range) } -> $x
        |
        (pair $x (rcons $range $rest)) -> (pair $x $rest) ; member
    }"#).unwrap();

    eprintln!("Running member query...");
    let result = repl.process_input("@(pair (s (s z)) (rcons (range (closed z) (open (s (s (s z))))) rnil)) ; member");
    eprintln!("First result: {:?}", result);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected first answer, got: {}", output);

    eprintln!("Running next...");
    let next_result = repl.process_input("next");
    eprintln!("Next result: {:?}", next_result);
    // Should return "No more answers" since member only has one answer for this input
    let next_output = next_result.expect("next should not fail").unwrap_or_default();
    eprintln!("Next output: {}", next_output);
}

// Simpler test - no CHR, just check if next works after exhaustion
#[test]
fn simple_rel_then_next_exhausted() {
    let mut repl = Repl::new();
    // Define a simple relation with one branch
    repl.process_input("rel f { a -> b }").unwrap();

    eprintln!("Running first query...");
    let result = repl.process_input("f");
    eprintln!("First result: {:?}", result);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected first answer");

    eprintln!("Running next...");
    let next_result = repl.process_input("next");
    eprintln!("Next result: {:?}", next_result);
    let next_output = next_result.expect("next should not fail").unwrap_or_default();
    assert!(next_output.contains("No more answers"), "Expected exhausted, got: {}", next_output);
}

// Test with Or - two branches
#[test]
fn or_rel_then_next_exhausted() {
    let mut repl = Repl::new();
    // Define a relation with two branches
    repl.process_input("rel f { a -> b | a -> c }").unwrap();

    eprintln!("Running first query...");
    let result = repl.process_input("f");
    eprintln!("First result: {:?}", result);

    eprintln!("Running next (should get second answer)...");
    let next_result = repl.process_input("next");
    eprintln!("Next result: {:?}", next_result);
    let next_output = next_result.expect("next should not fail").unwrap_or_default();
    assert!(next_output.contains("2."), "Expected second answer, got: {}", next_output);

    eprintln!("Running next (should be exhausted)...");
    let next2_result = repl.process_input("next");
    eprintln!("Next2 result: {:?}", next2_result);
    let next2_output = next2_result.expect("next should not fail").unwrap_or_default();
    assert!(next2_output.contains("No more answers"), "Expected exhausted, got: {}", next2_output);
}

// Test recursive relation with base case only
#[test]
fn recursive_base_case_only_then_next() {
    let mut repl = Repl::new();
    // A recursive relation that should hit base case and stop
    repl.process_input(r#"rel listlen {
        nil -> z
        |
        (cons $h $t) -> $t ; listlen ; $n -> (s $n)
    }"#).unwrap();

    eprintln!("Running query on nil (base case)...");
    let result = repl.process_input("@nil ; listlen");
    eprintln!("First result: {:?}", result);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected answer");

    eprintln!("Running next (should be exhausted)...");
    let next_result = repl.process_input("next");
    eprintln!("Next result: {:?}", next_result);
    let next_output = next_result.expect("next should not fail").unwrap_or_default();
    assert!(next_output.contains("No more answers"), "Expected exhausted, got: {}", next_output);
}

/// Test that forward execution through tree calculus app is fast.
/// This query from program_synth notebook should execute nearly instantly
/// because the input is fully ground and forward evaluation is deterministic.
#[test]
fn treecalc_forward_execution_is_fast() {
    let mut repl = Repl::new();

    // Load the theory with no_c constraint
    let theory = r#"theory treecalc_constraints {
        constraint no_c/1

        (no_c l) <=> .
        (no_c (b $x)) <=> (no_c $x).
        (no_c (f $x $y)) <=> (no_c $x), (no_c $y).
        (no_c (c $n)) <=> fail.
        (no_c (a $n $m)) <=> fail.
    }"#;
    let theory_result = repl.process_input(theory);
    assert!(theory_result.is_ok(), "Failed to define theory: {:?}", theory_result);

    // Define the app relation with all rules from program_synth notebook
    let app_rel = r#"rel app {
        (f (c $x) $y) -> (a (c $x) $y)
        |
        (f (a $x $y) $z) -> (a (a $x $y) $z)
        |
        (f l $z) -> (b $z)
        |
        (f (b $y) $z) -> (f $y $z)
        |
        (f (f l $y) $z) -> $y
        |
        (f (f (f $w $x) $y) l) -> $w
        |
        [
            [(f (f (b $x) $y) $z) -> (f $x $z) ; app ; $x -> (f $x $y)]
            &
            [(f (f (b $x) $y) $z) -> (f $y $z) ; app ; $y -> (f $x $y)]
            ; app
        ]
        |
        [
            (f (f (f $w $x) $y) (b $u)) -> (f $x $u)
            ; app
        ]
        |
        [
            (f (f (f $w $x) $y) (f $u $v)) -> (f (f $y $u) $v)
            ;
            [(f (f $a $b) $c) -> (f $a $b) ; app ; $a -> (f $a $b)]
            &
            (f (f $a $b) $c) -> (f $d $c)
            ; app
        ]
    }"#;
    let app_result = repl.process_input(app_rel);
    assert!(app_result.is_ok(), "Failed to define app: {:?}", app_result);

    // The query from program_synth notebook that should be instant
    // Input: a specific tree calculus term
    // Transform: wrap with (c z), apply app, wrap with (c (s z)), apply app
    let query = r#"@(f (b (f l (b (b (f (b (b l)) (f l l)))))) (b l)) ; [$x { (no_c $x) } -> (f $x (c z))] ; app ; [$x -> (f $x (c (s z)))] ; app"#;

    eprintln!("Running forward tree calculus query...");
    let start = std::time::Instant::now();
    let result = repl.process_input(query);
    let elapsed = start.elapsed();
    eprintln!("Query completed in {:?}", elapsed);
    eprintln!("Result: {:?}", result);

    // Should complete quickly (under 1 second for a ground forward query)
    assert!(elapsed.as_secs() < 1, "Query took too long: {:?}", elapsed);

    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("1."), "Expected answer, got: {}", output);
}

/// Simpler test: just verify app works on a basic ground term
#[test]
fn treecalc_app_simple_ground() {
    let mut repl = Repl::new();

    // Use same definitions as treecalc_forward_execution_is_fast
    let theory = r#"theory treecalc_constraints {
        constraint no_c/1
        (no_c l) <=> .
        (no_c (b $x)) <=> (no_c $x).
        (no_c (f $x $y)) <=> (no_c $x), (no_c $y).
        (no_c (c $n)) <=> fail.
        (no_c (a $n $m)) <=> fail.
    }"#;
    repl.process_input(theory).unwrap();

    let app_rel = r#"rel app {
        (f (c $x) $y) -> (a (c $x) $y)
        |
        (f (a $x $y) $z) -> (a (a $x $y) $z)
        |
        (f l $z) -> (b $z)
        |
        (f (b $y) $z) -> (f $y $z)
        |
        (f (f l $y) $z) -> $y
        |
        (f (f (f $w $x) $y) l) -> $w
        |
        [
            [(f (f (b $x) $y) $z) -> (f $x $z) ; app ; $x -> (f $x $y)]
            &
            [(f (f (b $x) $y) $z) -> (f $y $z) ; app ; $y -> (f $x $y)]
            ; app
        ]
        |
        [
            (f (f (f $w $x) $y) (b $u)) -> (f $x $u)
            ; app
        ]
        |
        [
            (f (f (f $w $x) $y) (f $u $v)) -> (f (f $y $u) $v)
            ;
            [(f (f $a $b) $c) -> (f $a $b) ; app ; $a -> (f $a $b)]
            &
            (f (f $a $b) $c) -> (f $d $c)
            ; app
        ]
    }"#;
    repl.process_input(app_rel).unwrap();

    // app(L, L) => B(L) by Rule 3: (f l $z) -> (b $z)
    let query = "@(f l l) ; app";
    let result = repl.process_input(query);
    let output = result.expect("query should not fail").unwrap_or_default();
    assert!(output.contains("(b l)"), "Expected (b l), got: {}", output);
}
