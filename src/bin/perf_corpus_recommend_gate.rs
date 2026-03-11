#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use rwlog::perf_corpus::{
    apply_filters, csv_escape, environment_fingerprint, load_cases, prepare_case, run_prepared,
    sort_cases, stats_percentile, CorpusCase, CorpusFilters, EnvironmentFingerprint, TierFilter,
};
use serde::Deserialize;
use serde::Serialize;
use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::PathBuf;
use std::time::Instant;
use std::time::SystemTime;
use std::time::UNIX_EPOCH;

#[derive(Debug, Deserialize)]
struct GateConfig {
    samples: usize,
    warmup: usize,
    tolerance_pct: f64,
}

#[derive(Debug, Serialize)]
struct RecommendationRow {
    id: String,
    category: String,
    observed_median_us: f64,
    observed_p95_us: f64,
    current_max_median_us: f64,
    current_max_p95_us: f64,
    recommended_max_median_us: f64,
    recommended_max_p95_us: f64,
    utilization_median: f64,
    utilization_p95: f64,
}

#[derive(Debug, Serialize)]
struct RecommendationReport {
    environment: EnvironmentFingerprint,
    samples: usize,
    warmup: usize,
    tolerance_pct: f64,
    headroom_pct: f64,
    round_us: f64,
    allow_lower: bool,
    applied: bool,
    apply_file: Option<String>,
    rows: Vec<RecommendationRow>,
}

#[derive(Debug)]
struct Args {
    samples: usize,
    warmup: usize,
    tolerance_pct: f64,
    headroom_pct: f64,
    round_us: f64,
    allow_lower: bool,
    filter: Option<String>,
    json: bool,
    csv: bool,
    apply: bool,
    apply_file: PathBuf,
}

fn load_gate_config() -> GateConfig {
    toml::from_str(include_str!("../../perf/quick_gate.toml")).expect("parse perf/quick_gate.toml")
}

fn quick_cases(filter: Option<&str>) -> Vec<CorpusCase> {
    let mut filters = CorpusFilters {
        tier: TierFilter::Quick,
        ..CorpusFilters::default()
    };
    if let Some(f) = filter {
        filters.filter_substring = Some(f.to_string());
    }
    let mut cases = apply_filters(load_cases(), &filters);
    sort_cases(&mut cases);
    if cases.is_empty() {
        panic!("no quick corpus cases selected");
    }
    cases
}

fn run_samples(case: &CorpusCase, samples: usize, warmup: usize) -> Vec<f64> {
    for _ in 0..warmup {
        let prepared = prepare_case(case);
        let _ = run_prepared(case, prepared);
    }

    let mut out = Vec::with_capacity(samples);
    for _ in 0..samples {
        let start = Instant::now();
        let prepared = prepare_case(case);
        let _ = run_prepared(case, prepared);
        out.push(start.elapsed().as_secs_f64() * 1_000_000.0);
    }
    out.sort_by(|a, b| a.partial_cmp(b).expect("finite float"));
    out
}

fn parse_args() -> Args {
    let cfg = load_gate_config();
    let mut args_out = Args {
        samples: cfg.samples,
        warmup: cfg.warmup,
        tolerance_pct: cfg.tolerance_pct,
        headroom_pct: 20.0,
        round_us: 100.0,
        allow_lower: false,
        filter: None,
        json: false,
        csv: false,
        apply: false,
        apply_file: PathBuf::from("benches/perf_corpus_cases.toml"),
    };

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        if arg == "--samples" {
            args_out.samples = args
                .next()
                .expect("--samples requires value")
                .parse()
                .expect("--samples must be integer");
            continue;
        }
        if arg == "--warmup" {
            args_out.warmup = args
                .next()
                .expect("--warmup requires value")
                .parse()
                .expect("--warmup must be integer");
            continue;
        }
        if arg == "--tolerance-pct" {
            args_out.tolerance_pct = args
                .next()
                .expect("--tolerance-pct requires value")
                .parse()
                .expect("--tolerance-pct must be float");
            continue;
        }
        if arg == "--headroom-pct" {
            args_out.headroom_pct = args
                .next()
                .expect("--headroom-pct requires value")
                .parse()
                .expect("--headroom-pct must be float");
            continue;
        }
        if arg == "--round-us" {
            args_out.round_us = args
                .next()
                .expect("--round-us requires value")
                .parse()
                .expect("--round-us must be float");
            continue;
        }
        if arg == "--allow-lower" {
            args_out.allow_lower = true;
            continue;
        }
        if arg == "--filter" {
            args_out.filter = Some(args.next().expect("--filter requires value"));
            continue;
        }
        if arg == "--json" {
            args_out.json = true;
            continue;
        }
        if arg == "--csv" {
            args_out.csv = true;
            continue;
        }
        if arg == "--apply" {
            args_out.apply = true;
            continue;
        }
        if arg == "--apply-file" {
            args_out.apply_file = PathBuf::from(args.next().expect("--apply-file requires value"));
            continue;
        }
        if arg == "--help" || arg == "-h" {
            println!(
                "Usage: perf_corpus_recommend_gate [--samples N] [--warmup N] [--tolerance-pct F] [--headroom-pct F] [--round-us F] [--filter SUBSTR] [--allow-lower] [--apply] [--apply-file PATH] [--json|--csv]"
            );
            std::process::exit(0);
        }
        panic!("unknown argument: {arg}");
    }

    assert!(args_out.samples > 0, "--samples must be > 0");
    assert!(args_out.round_us > 0.0, "--round-us must be > 0");
    assert!(
        !args_out.json || !args_out.csv,
        "--json and --csv are mutually exclusive"
    );
    args_out
}

fn round_up(value: f64, quantum: f64) -> f64 {
    (value / quantum).ceil() * quantum
}

fn recommend_base(
    observed_us: f64,
    current_base: f64,
    tolerance_pct: f64,
    headroom_pct: f64,
    round_us: f64,
    allow_lower: bool,
) -> f64 {
    let allowed = observed_us * (1.0 + headroom_pct / 100.0);
    let raw_base = allowed / (1.0 + tolerance_pct / 100.0);
    let mut recommended = round_up(raw_base.max(round_us), round_us);
    if !allow_lower {
        recommended = recommended.max(current_base);
    }
    recommended
}

fn parse_case_id(block: &str) -> Option<String> {
    for line in block.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("id = \"") {
            let rest = trimmed.strip_prefix("id = \"").expect("id prefix");
            if let Some(end_quote) = rest.find('"') {
                return Some(rest[..end_quote].to_string());
            }
        }
    }
    None
}

fn rewrite_case_block(block: &str, median: f64, p95: f64) -> String {
    let keep_trailing_newline = block.ends_with('\n');
    let mut filtered = Vec::new();
    let mut insert_idx = None;

    for line in block.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("quick_gate_max_median_us =")
            || trimmed.starts_with("quick_gate_max_p95_us =")
        {
            continue;
        }
        filtered.push(line.to_string());
        if trimmed.starts_with("infinite_stream =") {
            insert_idx = Some(filtered.len());
        }
    }

    let idx = insert_idx.unwrap_or(filtered.len());
    filtered.insert(idx, format!("quick_gate_max_median_us = {:.1}", median));
    filtered.insert(idx + 1, format!("quick_gate_max_p95_us = {:.1}", p95));

    let mut out = filtered.join("\n");
    if keep_trailing_newline {
        out.push('\n');
    }
    out
}

fn atomic_write(path: &PathBuf, content: &str) -> Result<(), io::Error> {
    let parent = path.parent().unwrap_or_else(|| std::path::Path::new("."));
    let file_name = path
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("cases.toml");
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let tmp_name = format!(".{}.tmp-{}-{}", file_name, std::process::id(), nonce);
    let tmp_path = parent.join(tmp_name);
    fs::write(&tmp_path, content)?;
    match fs::rename(&tmp_path, path) {
        Ok(()) => Ok(()),
        Err(err) => {
            let _ = fs::remove_file(&tmp_path);
            Err(err)
        }
    }
}

fn apply_recommendations_to_file(
    path: &PathBuf,
    rows: &[RecommendationRow],
) -> Result<usize, String> {
    let content = fs::read_to_string(path)
        .map_err(|e| format!("failed to read {}: {}", path.display(), e))?;

    let marker = "[[case]]";
    let Some(first_case_pos) = content.find(marker) else {
        return Err(format!(
            "failed to locate any case blocks in {}",
            path.display()
        ));
    };

    let prefix = &content[..first_case_pos];
    let case_text = &content[first_case_pos..];

    let offsets: Vec<usize> = case_text.match_indices(marker).map(|(idx, _)| idx).collect();

    let mut patches: BTreeMap<String, (f64, f64)> = BTreeMap::new();
    for row in rows {
        patches.insert(
            row.id.clone(),
            (row.recommended_max_median_us, row.recommended_max_p95_us),
        );
    }

    let mut found: BTreeMap<String, bool> = patches.keys().map(|k| (k.clone(), false)).collect();
    let mut rewritten_blocks = Vec::new();
    let mut changed = 0usize;

    for (i, start) in offsets.iter().enumerate() {
        let end = if i + 1 < offsets.len() {
            offsets[i + 1]
        } else {
            case_text.len()
        };
        let block = &case_text[*start..end];
        let Some(case_id) = parse_case_id(block) else {
            rewritten_blocks.push(block.to_string());
            continue;
        };
        if let Some((median, p95)) = patches.get(&case_id).copied() {
            let rewritten = rewrite_case_block(block, median, p95);
            if rewritten != block {
                changed += 1;
            }
            rewritten_blocks.push(rewritten);
            found.insert(case_id, true);
        } else {
            rewritten_blocks.push(block.to_string());
        }
    }

    let missing: Vec<String> = found
        .into_iter()
        .filter_map(|(id, ok)| if ok { None } else { Some(id) })
        .collect();
    if !missing.is_empty() {
        return Err(format!(
            "failed to apply recommendations; missing case ids in {}: {}",
            path.display(),
            missing.join(", ")
        ));
    }

    let mut new_content = String::new();
    new_content.push_str(prefix);
    for block in rewritten_blocks {
        new_content.push_str(&block);
    }

    atomic_write(path, &new_content)
        .map_err(|e| format!("failed to atomically write {}: {}", path.display(), e))?;
    Ok(changed)
}

fn main() {
    let args = parse_args();
    let cases = quick_cases(args.filter.as_deref());
    let env = environment_fingerprint();

    let mut rows = Vec::new();
    for case in &cases {
        let current_median = case
            .quick_gate_max_median_us
            .expect("quick case missing quick_gate_max_median_us");
        let current_p95 = case
            .quick_gate_max_p95_us
            .expect("quick case missing quick_gate_max_p95_us");

        let samples_us = run_samples(case, args.samples, args.warmup);
        let observed_median = stats_percentile(&samples_us, 0.50);
        let observed_p95 = stats_percentile(&samples_us, 0.95);

        let recommended_median = recommend_base(
            observed_median,
            current_median,
            args.tolerance_pct,
            args.headroom_pct,
            args.round_us,
            args.allow_lower,
        );
        let recommended_p95 = recommend_base(
            observed_p95,
            current_p95,
            args.tolerance_pct,
            args.headroom_pct,
            args.round_us,
            args.allow_lower,
        );

        let current_median_budget = current_median * (1.0 + args.tolerance_pct / 100.0);
        let current_p95_budget = current_p95 * (1.0 + args.tolerance_pct / 100.0);

        rows.push(RecommendationRow {
            id: case.id.clone(),
            category: case.category.as_str().to_string(),
            observed_median_us: observed_median,
            observed_p95_us: observed_p95,
            current_max_median_us: current_median,
            current_max_p95_us: current_p95,
            recommended_max_median_us: recommended_median,
            recommended_max_p95_us: recommended_p95,
            utilization_median: observed_median / current_median_budget,
            utilization_p95: observed_p95 / current_p95_budget,
        });
    }

    rows.sort_by(|a, b| a.id.cmp(&b.id));

    if args.apply {
        let changed = apply_recommendations_to_file(&args.apply_file, &rows)
            .unwrap_or_else(|e| panic!("apply failed: {}", e));
        eprintln!(
            "applied recommendations to {} ({} case blocks changed)",
            args.apply_file.display(),
            changed
        );
    }

    if args.json {
        let report = RecommendationReport {
            environment: env,
            samples: args.samples,
            warmup: args.warmup,
            tolerance_pct: args.tolerance_pct,
            headroom_pct: args.headroom_pct,
            round_us: args.round_us,
            allow_lower: args.allow_lower,
            applied: args.apply,
            apply_file: if args.apply {
                Some(args.apply_file.display().to_string())
            } else {
                None
            },
            rows,
        };
        println!(
            "{}",
            serde_json::to_string_pretty(&report).expect("serialize recommendation report")
        );
        return;
    }

    if args.csv {
        println!(
            "id,category,observed_median_us,observed_p95_us,current_max_median_us,current_max_p95_us,recommended_max_median_us,recommended_max_p95_us,utilization_median,utilization_p95,samples,warmup,tolerance_pct,headroom_pct,round_us,allow_lower,applied,apply_file,env_os,env_arch,env_cpu,env_rustc,env_rustflags,env_git_sha"
        );
        for row in rows {
            println!(
                "{},{},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3},{:.6},{:.6},{},{},{:.3},{:.3},{:.3},{},{},{},{},{},{},{},{},{}",
                csv_escape(&row.id),
                csv_escape(&row.category),
                row.observed_median_us,
                row.observed_p95_us,
                row.current_max_median_us,
                row.current_max_p95_us,
                row.recommended_max_median_us,
                row.recommended_max_p95_us,
                row.utilization_median,
                row.utilization_p95,
                args.samples,
                args.warmup,
                args.tolerance_pct,
                args.headroom_pct,
                args.round_us,
                args.allow_lower,
                args.apply,
                csv_escape(if args.apply {
                    args.apply_file.to_str().unwrap_or("")
                } else {
                    ""
                }),
                csv_escape(&env.os),
                csv_escape(&env.arch),
                csv_escape(env.cpu_model.as_deref().unwrap_or("")),
                csv_escape(&env.rustc_version),
                csv_escape(env.rustflags.as_deref().unwrap_or("")),
                csv_escape(env.git_sha.as_deref().unwrap_or("")),
            );
        }
        return;
    }

    println!(
        "quick gate threshold recommendations: samples={} warmup={} tolerance_pct={:.3} headroom_pct={:.3} round_us={:.3} allow_lower={} apply={}",
        args.samples,
        args.warmup,
        args.tolerance_pct,
        args.headroom_pct,
        args.round_us,
        args.allow_lower,
        args.apply
    );
    println!(
        "id | observed_median | observed_p95 | current_median | current_p95 | recommend_median | recommend_p95 | util_median | util_p95"
    );
    for row in &rows {
        println!(
            "{} | {:.3} | {:.3} | {:.3} | {:.3} | {:.3} | {:.3} | {:.4} | {:.4}",
            row.id,
            row.observed_median_us,
            row.observed_p95_us,
            row.current_max_median_us,
            row.current_max_p95_us,
            row.recommended_max_median_us,
            row.recommended_max_p95_us,
            row.utilization_median,
            row.utilization_p95,
        );
    }
    println!("\n# Suggested case-field updates (benches/perf_corpus_cases.toml)");
    for row in &rows {
        println!("# case: {}", row.id);
        println!(
            "quick_gate_max_median_us = {:.1}",
            row.recommended_max_median_us
        );
        println!("quick_gate_max_p95_us = {:.1}", row.recommended_max_p95_us);
    }
}
