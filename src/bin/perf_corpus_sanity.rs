#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use rwlog::perf_corpus::{
    apply_filters, csv_escape, csv_escape_opt, environment_fingerprint, lint_cases,
    lint_full_corpus, load_cases, sort_cases, summary_string, validate_cases, CorpusFilters,
    EnvironmentFingerprint,
};
use serde::Serialize;

#[derive(Debug, Serialize)]
struct SanityCaseRow {
    id: String,
    title: String,
    tier: String,
    category: String,
    mode: String,
    expected: String,
    determinism: String,
    answer_shape: String,
    infinite_stream: bool,
    quick_gate_max_median_us: Option<f64>,
    quick_gate_max_p95_us: Option<f64>,
    noise_target_cv_pct: Option<f64>,
    noise_flaky_cv_pct: Option<f64>,
    adaptive_min_samples: Option<usize>,
    adaptive_max_samples: Option<usize>,
    tags: Vec<String>,
    description: String,
}

#[derive(Debug, Serialize)]
struct SanityReport {
    environment: EnvironmentFingerprint,
    selected_cases: usize,
    lint_requested: bool,
    lint_ok: bool,
    validate_requested: bool,
    validate_ok: bool,
    rows: Vec<SanityCaseRow>,
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let validate = args.iter().any(|arg| arg == "--validate");
    let lint = args.iter().any(|arg| arg == "--lint");
    let json = args.iter().any(|arg| arg == "--json");
    let csv = args.iter().any(|arg| arg == "--csv");
    if json && csv {
        panic!("--json and --csv are mutually exclusive");
    }

    let filters = CorpusFilters::from_env();
    let mut cases = apply_filters(load_cases(), &filters);
    sort_cases(&mut cases);
    let env = environment_fingerprint();

    if cases.is_empty() {
        eprintln!("no corpus cases selected after filtering");
        std::process::exit(2);
    }

    if !json && !csv {
        println!("{}", summary_string(&cases, &filters));
    }

    let lint_ok = if lint {
        match lint_full_corpus() {
            Ok(report) => {
                if !json && !csv {
                    println!("{}", report);
                }
            }
            Err(err) => {
                eprintln!("lint: failed: {}", err);
                std::process::exit(1);
            }
        }
        if let Err(err) = lint_cases(&cases) {
            eprintln!("lint(selected): failed: {}", err);
            std::process::exit(1);
        }
        if !json && !csv {
            println!("lint: ok");
        }
        true
    } else {
        false
    };

    let validate_ok = if validate {
        match validate_cases(&cases) {
            Ok(()) => {
                if !json && !csv {
                    println!("validation: ok ({} cases)", cases.len());
                }
            }
            Err(err) => {
                eprintln!("validation: failed: {}", err);
                std::process::exit(1);
            }
        }
        true
    } else {
        false
    };

    if json {
        let rows: Vec<SanityCaseRow> = cases
            .iter()
            .map(|c| SanityCaseRow {
                id: c.id.clone(),
                title: c.title.clone(),
                tier: c.tier.as_str().to_string(),
                category: c.category.as_str().to_string(),
                mode: c.mode.as_str().to_string(),
                expected: c.expected.as_str(),
                determinism: c.determinism.as_str().to_string(),
                answer_shape: c.answer_shape.as_str().to_string(),
                infinite_stream: c.infinite_stream,
                quick_gate_max_median_us: c.quick_gate_max_median_us,
                quick_gate_max_p95_us: c.quick_gate_max_p95_us,
                noise_target_cv_pct: c.noise_target_cv_pct,
                noise_flaky_cv_pct: c.noise_flaky_cv_pct,
                adaptive_min_samples: c.adaptive_min_samples,
                adaptive_max_samples: c.adaptive_max_samples,
                tags: c.tags.clone(),
                description: c.description.clone(),
            })
            .collect();
        let report = SanityReport {
            environment: env,
            selected_cases: rows.len(),
            lint_requested: lint,
            lint_ok,
            validate_requested: validate,
            validate_ok,
            rows,
        };
        println!(
            "{}",
            serde_json::to_string_pretty(&report).expect("serialize sanity report")
        );
        return;
    }
    if csv {
        println!(
            "id,title,tier,category,mode,expected,determinism,answer_shape,infinite_stream,quick_gate_max_median_us,quick_gate_max_p95_us,noise_target_cv_pct,noise_flaky_cv_pct,adaptive_min_samples,adaptive_max_samples,tags,description,env_os,env_arch,env_cpu,env_rustc,env_rustflags,env_timestamp_unix_s,env_git_sha,env_run_id"
        );
        for c in cases {
            println!(
                "{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}",
                csv_escape(&c.id),
                csv_escape(&c.title),
                csv_escape(c.tier.as_str()),
                csv_escape(c.category.as_str()),
                csv_escape(c.mode.as_str()),
                csv_escape(&c.expected.as_str()),
                csv_escape(c.determinism.as_str()),
                csv_escape(c.answer_shape.as_str()),
                c.infinite_stream,
                csv_escape_opt_f64(c.quick_gate_max_median_us),
                csv_escape_opt_f64(c.quick_gate_max_p95_us),
                csv_escape_opt_f64(c.noise_target_cv_pct),
                csv_escape_opt_f64(c.noise_flaky_cv_pct),
                csv_escape_opt_usize(c.adaptive_min_samples),
                csv_escape_opt_usize(c.adaptive_max_samples),
                csv_escape(&c.tags.join("|")),
                csv_escape(&c.description),
                csv_escape(&env.os),
                csv_escape(&env.arch),
                csv_escape_opt(env.cpu_model.as_deref()),
                csv_escape(&env.rustc_version),
                csv_escape_opt(env.rustflags.as_deref()),
                env.timestamp_unix_s,
                csv_escape_opt(env.git_sha.as_deref()),
                csv_escape_opt(env.run_id.as_deref()),
            );
        }
    }
}

fn csv_escape_opt_f64(v: Option<f64>) -> String {
    match v {
        Some(n) => format!("{n:.3}"),
        None => String::new(),
    }
}

fn csv_escape_opt_usize(v: Option<usize>) -> String {
    match v {
        Some(n) => n.to_string(),
        None => String::new(),
    }
}
