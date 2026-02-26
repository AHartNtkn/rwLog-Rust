#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use rwlog::perf_corpus::{
    apply_filters, compile_prepared, environment_fingerprint, load_cases, prepare_case,
    run_compiled, sort_cases, CorpusCase, CorpusFilters, EnvironmentFingerprint, TierFilter,
};
use serde::Deserialize;
use serde::Serialize;
use std::time::Instant;

#[derive(Debug, Deserialize)]
struct GateConfig {
    samples: usize,
    warmup: usize,
    tolerance_pct: f64,
    #[serde(default = "default_adaptive_step")]
    adaptive_step: usize,
    #[serde(default = "default_adaptive_max_samples")]
    adaptive_max_samples: usize,
    #[serde(default = "default_target_cv_pct")]
    default_target_cv_pct: f64,
    #[serde(default = "default_flaky_cv_pct")]
    default_flaky_cv_pct: f64,
    #[serde(default)]
    enforce_noise: bool,
}

fn default_adaptive_step() -> usize {
    5
}

fn default_adaptive_max_samples() -> usize {
    40
}

fn default_target_cv_pct() -> f64 {
    35.0
}

fn default_flaky_cv_pct() -> f64 {
    55.0
}

#[derive(Debug, Serialize)]
struct GateRow {
    id: String,
    median_us: f64,
    p95_us: f64,
    budget_median_us: f64,
    budget_p95_us: f64,
    latency_ok: bool,
    noise_ok: bool,
    flaky: bool,
    samples_used: usize,
    adaptive_resamples: usize,
    cv_pct: f64,
    mad_pct: f64,
    ci95_halfwidth_pct: f64,
    target_cv_pct: f64,
    flaky_cv_pct: f64,
    ok: bool,
}

#[derive(Debug, Serialize)]
struct GateReport {
    environment: EnvironmentFingerprint,
    samples: usize,
    warmup: usize,
    tolerance_pct: f64,
    adaptive_step: usize,
    adaptive_max_samples: usize,
    default_target_cv_pct: f64,
    default_flaky_cv_pct: f64,
    enforce_noise: bool,
    noisy_cases: usize,
    flaky_cases: usize,
    rows: Vec<GateRow>,
    failed: bool,
}

fn load_gate_config() -> GateConfig {
    toml::from_str(include_str!("../../perf/quick_gate.toml")).expect("parse perf/quick_gate.toml")
}

#[derive(Debug)]
struct GatedCase {
    case: CorpusCase,
    max_median_us: f64,
    max_p95_us: f64,
    target_cv_pct: f64,
    flaky_cv_pct: f64,
    min_samples: usize,
    max_samples: usize,
}

fn quick_gate_cases(cfg: &GateConfig) -> Vec<GatedCase> {
    let filters = CorpusFilters {
        tier: TierFilter::Quick,
        ..CorpusFilters::default()
    };
    let mut cases = apply_filters(load_cases(), &filters);
    sort_cases(&mut cases);
    if cases.is_empty() {
        panic!("no quick corpus cases found");
    }

    let mut out = Vec::with_capacity(cases.len());
    for case in cases {
        match (case.quick_gate_max_median_us, case.quick_gate_max_p95_us) {
            (Some(max_median_us), Some(max_p95_us)) => {
                let target_cv_pct = case
                    .noise_target_cv_pct
                    .unwrap_or(cfg.default_target_cv_pct);
                let flaky_cv_pct = case
                    .noise_flaky_cv_pct
                    .unwrap_or(cfg.default_flaky_cv_pct)
                    .max(target_cv_pct);
                let min_samples = case.adaptive_min_samples.unwrap_or(cfg.samples).max(1);
                let max_samples = case
                    .adaptive_max_samples
                    .unwrap_or(cfg.adaptive_max_samples)
                    .max(min_samples);
                out.push(GatedCase {
                    case,
                    max_median_us,
                    max_p95_us,
                    target_cv_pct,
                    flaky_cv_pct,
                    min_samples,
                    max_samples,
                });
            }
            _ => {
                panic!(
                    "quick case '{}' is missing quick gate thresholds in benches/perf_corpus_cases.toml",
                    case.id
                );
            }
        }
    }
    out
}

fn run_samples_adaptive(
    case: &CorpusCase,
    cfg: &GateConfig,
    min_samples: usize,
    max_samples: usize,
    target_cv_pct: f64,
) -> Vec<f64> {
    let min_samples = min_samples.max(1);
    let max_samples = max_samples.max(min_samples);
    for _ in 0..cfg.warmup {
        let prepared = prepare_case(case);
        let engine = compile_prepared(prepared);
        let _ = run_compiled(case, engine);
    }

    let mut out = Vec::with_capacity(max_samples);
    let mut remaining = min_samples;
    while out.len() < max_samples {
        for _ in 0..remaining {
            let prepared = prepare_case(case);
            let engine = compile_prepared(prepared);
            let start = Instant::now();
            let _ = run_compiled(case, engine);
            out.push(start.elapsed().as_secs_f64() * 1_000_000.0);
        }
        if out.len() >= max_samples {
            break;
        }
        let cv_pct = coefficient_of_variation_pct(&out);
        if cv_pct <= target_cv_pct {
            break;
        }
        let left = max_samples - out.len();
        remaining = cfg.adaptive_step.max(1).min(left);
    }
    out
}

fn percentile(sorted: &[f64], p: f64) -> f64 {
    let idx = ((sorted.len() as f64) * p).ceil() as usize - 1;
    sorted[idx.min(sorted.len() - 1)]
}

fn median_sorted(sorted: &[f64]) -> f64 {
    sorted[sorted.len() / 2]
}

fn mean(values: &[f64]) -> f64 {
    values.iter().sum::<f64>() / (values.len() as f64)
}

fn stddev(values: &[f64]) -> f64 {
    if values.len() < 2 {
        return 0.0;
    }
    let m = mean(values);
    let var = values
        .iter()
        .map(|v| {
            let d = v - m;
            d * d
        })
        .sum::<f64>()
        / (values.len() as f64);
    var.sqrt()
}

fn coefficient_of_variation_pct(values: &[f64]) -> f64 {
    if values.len() < 2 {
        return 0.0;
    }
    let m = mean(values);
    if m <= 0.0 {
        return 0.0;
    }
    (stddev(values) / m) * 100.0
}

fn median_absolute_deviation_pct(sorted: &[f64]) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let median = median_sorted(sorted);
    if median <= 0.0 {
        return 0.0;
    }
    let mut abs_dev: Vec<f64> = sorted.iter().map(|v| (v - median).abs()).collect();
    abs_dev.sort_by(|a, b| a.partial_cmp(b).expect("finite float"));
    (median_sorted(&abs_dev) / median) * 100.0
}

fn ci95_halfwidth_pct(values: &[f64]) -> f64 {
    if values.len() < 2 {
        return 0.0;
    }
    let m = mean(values);
    if m <= 0.0 {
        return 0.0;
    }
    let se = stddev(values) / (values.len() as f64).sqrt();
    ((1.96 * se) / m) * 100.0
}

fn main() {
    let json = std::env::args().any(|arg| arg == "--json");
    let csv = std::env::args().any(|arg| arg == "--csv");
    if json && csv {
        panic!("--json and --csv are mutually exclusive");
    }
    let cfg = load_gate_config();
    assert!(cfg.samples > 0, "samples must be > 0");
    assert!(cfg.adaptive_step > 0, "adaptive_step must be > 0");
    assert!(
        cfg.adaptive_max_samples > 0,
        "adaptive_max_samples must be > 0"
    );
    assert!(
        cfg.default_target_cv_pct.is_finite() && cfg.default_target_cv_pct > 0.0,
        "default_target_cv_pct must be finite and > 0"
    );
    assert!(
        cfg.default_flaky_cv_pct.is_finite() && cfg.default_flaky_cv_pct > 0.0,
        "default_flaky_cv_pct must be finite and > 0"
    );
    let gated_cases = quick_gate_cases(&cfg);
    let env = environment_fingerprint();

    if !json && !csv {
        println!(
            "perf corpus quick gate: samples={} warmup={} tolerance_pct={} adaptive_step={} adaptive_max_samples={} default_target_cv_pct={} default_flaky_cv_pct={} enforce_noise={}",
            cfg.samples,
            cfg.warmup,
            cfg.tolerance_pct,
            cfg.adaptive_step,
            cfg.adaptive_max_samples,
            cfg.default_target_cv_pct,
            cfg.default_flaky_cv_pct,
            cfg.enforce_noise
        );
        println!("id | median_us | p95_us | budget_median_us | budget_p95_us | cv_pct | mad_pct | ci95_halfwidth_pct | samples_used | result");
    }

    let mut failed = false;
    let mut noisy_cases = 0usize;
    let mut flaky_cases = 0usize;
    let mut rows = Vec::new();
    for gated in &gated_cases {
        let mut samples = run_samples_adaptive(
            &gated.case,
            &cfg,
            gated.min_samples,
            gated.max_samples,
            gated.target_cv_pct,
        );
        let cv_pct = coefficient_of_variation_pct(&samples);
        samples.sort_by(|a, b| a.partial_cmp(b).expect("finite float"));
        let median = percentile(&samples, 0.50);
        let p95 = percentile(&samples, 0.95);
        let mad_pct = median_absolute_deviation_pct(&samples);
        let ci95_pct = ci95_halfwidth_pct(&samples);

        let median_budget = gated.max_median_us * (1.0 + cfg.tolerance_pct / 100.0);
        let p95_budget = gated.max_p95_us * (1.0 + cfg.tolerance_pct / 100.0);

        let latency_ok = median <= median_budget && p95 <= p95_budget;
        let noise_ok = cv_pct <= gated.target_cv_pct;
        let flaky = cv_pct > gated.flaky_cv_pct;
        let ok = latency_ok && (!cfg.enforce_noise || noise_ok);
        if !noise_ok {
            noisy_cases += 1;
        }
        if flaky {
            flaky_cases += 1;
        }
        if !json && !csv {
            println!(
                "{} | {:.3} | {:.3} | {:.3} | {:.3} | {:.3}% | {:.3}% | {:.3}% | {} | {}",
                gated.case.id,
                median,
                p95,
                median_budget,
                p95_budget,
                cv_pct,
                mad_pct,
                ci95_pct,
                samples.len(),
                if ok { "ok" } else { "FAIL" }
            );
        }
        rows.push(GateRow {
            id: gated.case.id.clone(),
            median_us: median,
            p95_us: p95,
            budget_median_us: median_budget,
            budget_p95_us: p95_budget,
            latency_ok,
            noise_ok,
            flaky,
            samples_used: samples.len(),
            adaptive_resamples: samples.len().saturating_sub(cfg.samples),
            cv_pct,
            mad_pct,
            ci95_halfwidth_pct: ci95_pct,
            target_cv_pct: gated.target_cv_pct,
            flaky_cv_pct: gated.flaky_cv_pct,
            ok,
        });
        if !ok {
            failed = true;
        }
    }

    if json {
        let report = GateReport {
            environment: env,
            samples: cfg.samples,
            warmup: cfg.warmup,
            tolerance_pct: cfg.tolerance_pct,
            adaptive_step: cfg.adaptive_step,
            adaptive_max_samples: cfg.adaptive_max_samples,
            default_target_cv_pct: cfg.default_target_cv_pct,
            default_flaky_cv_pct: cfg.default_flaky_cv_pct,
            enforce_noise: cfg.enforce_noise,
            noisy_cases,
            flaky_cases,
            rows,
            failed,
        };
        println!(
            "{}",
            serde_json::to_string_pretty(&report).expect("serialize gate report")
        );
        if failed {
            eprintln!("perf corpus quick gate failed");
            std::process::exit(1);
        }
        return;
    }
    if csv {
        println!(
            "id,median_us,p95_us,budget_median_us,budget_p95_us,latency_ok,noise_ok,flaky,samples_used,adaptive_resamples,cv_pct,mad_pct,ci95_halfwidth_pct,target_cv_pct,flaky_cv_pct,ok,samples,warmup,tolerance_pct,adaptive_step,adaptive_max_samples,default_target_cv_pct,default_flaky_cv_pct,enforce_noise,env_os,env_arch,env_cpu,env_rustc,env_rustflags,env_timestamp_unix_s,env_git_sha,env_run_id"
        );
        for row in rows {
            println!(
                "{},{:.3},{:.3},{:.3},{:.3},{},{},{},{},{},{:.3},{:.3},{:.3},{:.3},{:.3},{},{},{},{:.3},{},{},{:.3},{:.3},{},{},{},{},{},{},{},{},{}",
                csv_escape(&row.id),
                row.median_us,
                row.p95_us,
                row.budget_median_us,
                row.budget_p95_us,
                row.latency_ok,
                row.noise_ok,
                row.flaky,
                row.samples_used,
                row.adaptive_resamples,
                row.cv_pct,
                row.mad_pct,
                row.ci95_halfwidth_pct,
                row.target_cv_pct,
                row.flaky_cv_pct,
                row.ok,
                cfg.samples,
                cfg.warmup,
                cfg.tolerance_pct,
                cfg.adaptive_step,
                cfg.adaptive_max_samples,
                cfg.default_target_cv_pct,
                cfg.default_flaky_cv_pct,
                cfg.enforce_noise,
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
        if failed {
            eprintln!("perf corpus quick gate failed");
            std::process::exit(1);
        }
        return;
    }
    if !cfg.enforce_noise && noisy_cases > 0 {
        eprintln!(
            "warning: {} cases exceeded target CV but enforce_noise=false (flaky_cases={})",
            noisy_cases, flaky_cases
        );
    }

    if failed {
        eprintln!("perf corpus quick gate failed");
        std::process::exit(1);
    }
}

fn csv_escape(s: &str) -> String {
    if s.contains(',') || s.contains('"') || s.contains('\n') {
        format!("\"{}\"", s.replace('"', "\"\""))
    } else {
        s.to_string()
    }
}

fn csv_escape_opt(s: Option<&str>) -> String {
    match s {
        Some(v) => csv_escape(v),
        None => String::new(),
    }
}
