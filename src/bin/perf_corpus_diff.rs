use serde::Deserialize;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug, Deserialize)]
struct Estimates {
    mean: Stat,
    median: Stat,
}

#[derive(Debug, Deserialize)]
struct Stat {
    point_estimate: f64,
}

#[derive(Debug)]
struct ChangeEntry {
    id: String,
    mean_change_pct: f64,
    median_change_pct: f64,
}

fn parse_threshold_pct() -> f64 {
    let mut args = std::env::args().skip(1);
    let mut threshold = 5.0;
    while let Some(arg) = args.next() {
        if arg == "--threshold-pct" {
            threshold = args
                .next()
                .expect("--threshold-pct needs value")
                .parse()
                .expect("threshold must be float");
            continue;
        }
        if arg == "--help" || arg == "-h" {
            println!("Usage: perf_corpus_diff [--threshold-pct <float>]");
            std::process::exit(0);
        }
        panic!("unknown argument: {arg}");
    }
    threshold
}

fn walk_dir(path: &Path, out: &mut Vec<PathBuf>) {
    let entries =
        fs::read_dir(path).unwrap_or_else(|e| panic!("read_dir {}: {}", path.display(), e));
    for entry in entries {
        let entry = entry.expect("dir entry");
        let p = entry.path();
        if p.is_dir() {
            walk_dir(&p, out);
        } else if p.file_name().and_then(|n| n.to_str()) == Some("estimates.json")
            && p.parent()
                .and_then(|p| p.file_name())
                .and_then(|n| n.to_str())
                == Some("change")
        {
            out.push(p);
        }
    }
}

fn case_id_from_path(path: &Path) -> String {
    let mut components = Vec::new();
    let mut cur = path.parent().and_then(|p| p.parent()); // strip /change/estimates.json
    while let Some(p) = cur {
        let name = p.file_name().and_then(|n| n.to_str());
        if name == Some("criterion") {
            break;
        }
        if let Some(name) = name {
            components.push(name.to_string());
        }
        cur = p.parent();
    }
    components.reverse();
    components.join("/")
}

fn load_changes(root: &Path) -> Vec<ChangeEntry> {
    let mut files = Vec::new();
    walk_dir(root, &mut files);
    let mut out = Vec::new();
    for file in files {
        let data =
            fs::read_to_string(&file).unwrap_or_else(|e| panic!("read {}: {}", file.display(), e));
        let est: Estimates = serde_json::from_str(&data)
            .unwrap_or_else(|e| panic!("parse {}: {}", file.display(), e));
        out.push(ChangeEntry {
            id: case_id_from_path(&file),
            mean_change_pct: est.mean.point_estimate * 100.0,
            median_change_pct: est.median.point_estimate * 100.0,
        });
    }
    out.sort_by(|a, b| a.id.cmp(&b.id));
    out
}

fn main() {
    let threshold = parse_threshold_pct();
    let root = Path::new("target/criterion");
    if !root.exists() {
        eprintln!("target/criterion not found. Run a baseline comparison first.");
        std::process::exit(2);
    }

    let changes = load_changes(root);
    if changes.is_empty() {
        eprintln!("No change estimates found in target/criterion/**/change/estimates.json");
        eprintln!("Run: cargo bench --bench perf_corpus -- --baseline <name>");
        std::process::exit(2);
    }

    println!(
        "id | mean_change_pct | median_change_pct | status (threshold {:.2}%)",
        threshold
    );
    let mut failed = false;
    for c in &changes {
        let regress = c.mean_change_pct > threshold || c.median_change_pct > threshold;
        if regress {
            failed = true;
        }
        println!(
            "{} | {:+.3}% | {:+.3}% | {}",
            c.id,
            c.mean_change_pct,
            c.median_change_pct,
            if regress { "REGRESSION" } else { "ok" }
        );
    }

    if failed {
        eprintln!("perf diff detected regressions above threshold");
        std::process::exit(1);
    }
}
