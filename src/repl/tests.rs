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
