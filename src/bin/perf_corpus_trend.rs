#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use rwlog::perf_corpus::{
    csv_escape, load_cases, load_snapshots, PerfSnapshot, SourceFilter, stats_cv_pct,
    stats_mad_pct,
};
use serde::Serialize;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::path::PathBuf;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MetricFilter {
    Median,
    P95,
    All,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EnvCompatMode {
    Warn,
    Fail,
    Off,
}

#[derive(Clone, Debug)]
struct Args {
    history_dir: PathBuf,
    source: SourceFilter,
    metric: MetricFilter,
    env_compat: EnvCompatMode,
    window: Option<usize>,
    top: usize,
    filter: Option<String>,
    fail_regressions_pct: Option<f64>,
    min_regression_confidence: f64,
    default_noise_target_cv_pct: f64,
    json: bool,
    csv: bool,
}

#[derive(Clone, Debug, Serialize)]
struct TrendRow {
    source: String,
    metric: String,
    id: String,
    points: usize,
    first_snapshot: String,
    last_snapshot: String,
    first_us: f64,
    last_us: f64,
    delta_us: f64,
    delta_pct: f64,
    min_us: f64,
    max_us: f64,
    slope_us_per_snapshot: f64,
    volatility_cv_pct: f64,
    volatility_mad_pct: f64,
    noise_target_cv_pct: f64,
    regression_confidence: f64,
    effective_threshold_pct: Option<f64>,
    regression_over_effective_threshold: Option<bool>,
}

#[derive(Clone, Debug, Serialize)]
struct TrendReport {
    history_dir: String,
    source: String,
    metric: String,
    env_compat: String,
    env_mismatch_fields: Vec<String>,
    window: Option<usize>,
    snapshots_scanned: usize,
    regressions_over_threshold: Option<usize>,
    fail_regressions_pct: Option<f64>,
    min_regression_confidence: f64,
    default_noise_target_cv_pct: f64,
    rows: Vec<TrendRow>,
}

fn parse_args() -> Args {
    let mut args_out = Args {
        history_dir: PathBuf::from("perf/history"),
        source: SourceFilter::All,
        metric: MetricFilter::Median,
        env_compat: EnvCompatMode::Warn,
        window: None,
        top: 20,
        filter: None,
        fail_regressions_pct: None,
        min_regression_confidence: 1.0,
        default_noise_target_cv_pct: 35.0,
        json: false,
        csv: false,
    };

    let mut args = std::env::args().skip(1).peekable();
    while let Some(arg) = args.next() {
        if arg == "--history-dir" {
            args_out.history_dir =
                PathBuf::from(args.next().expect("--history-dir requires value"));
            continue;
        }
        if arg == "--source" {
            args_out.source = match args.next().expect("--source requires value").as_str() {
                "gate" => SourceFilter::Gate,
                "probe" => SourceFilter::Probe,
                "all" => SourceFilter::All,
                other => panic!("--source must be gate|probe|all, got '{other}'"),
            };
            continue;
        }
        if arg == "--metric" {
            args_out.metric = match args.next().expect("--metric requires value").as_str() {
                "median" => MetricFilter::Median,
                "p95" => MetricFilter::P95,
                "all" => MetricFilter::All,
                other => panic!("--metric must be median|p95|all, got '{other}'"),
            };
            continue;
        }
        if arg == "--env-compat" {
            args_out.env_compat = match args.next().expect("--env-compat requires value").as_str() {
                "warn" => EnvCompatMode::Warn,
                "fail" => EnvCompatMode::Fail,
                "off" => EnvCompatMode::Off,
                other => panic!("--env-compat must be warn|fail|off, got '{other}'"),
            };
            continue;
        }
        if arg == "--window" {
            args_out.window = Some(
                args.next()
                    .expect("--window requires value")
                    .parse()
                    .expect("--window must be integer"),
            );
            continue;
        }
        if arg == "--top" {
            args_out.top = args
                .next()
                .expect("--top requires value")
                .parse()
                .expect("--top must be integer");
            continue;
        }
        if arg == "--filter" {
            args_out.filter = Some(args.next().expect("--filter requires value"));
            continue;
        }
        if arg == "--fail-regressions-pct" {
            args_out.fail_regressions_pct = Some(
                args.next()
                    .expect("--fail-regressions-pct requires value")
                    .parse()
                    .expect("--fail-regressions-pct must be float"),
            );
            continue;
        }
        if arg == "--min-regression-confidence" {
            args_out.min_regression_confidence = args
                .next()
                .expect("--min-regression-confidence requires value")
                .parse()
                .expect("--min-regression-confidence must be float");
            continue;
        }
        if arg == "--default-noise-target-cv-pct" {
            args_out.default_noise_target_cv_pct = args
                .next()
                .expect("--default-noise-target-cv-pct requires value")
                .parse()
                .expect("--default-noise-target-cv-pct must be float");
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
        if arg == "--help" || arg == "-h" {
            println!(
                "Usage: perf_corpus_trend [--history-dir PATH] [--source gate|probe|all] [--metric median|p95|all] [--env-compat warn|fail|off] [--window N] [--top N] [--filter SUBSTR] [--fail-regressions-pct F] [--min-regression-confidence F] [--default-noise-target-cv-pct F] [--json|--csv]"
            );
            std::process::exit(0);
        }
        panic!("unknown argument: {arg}");
    }

    assert!(args_out.top > 0, "--top must be > 0");
    assert!(
        args_out.window.map(|w| w > 0).unwrap_or(true),
        "--window must be > 0"
    );
    assert!(
        args_out
            .fail_regressions_pct
            .map(|t| t >= 0.0)
            .unwrap_or(true),
        "--fail-regressions-pct must be >= 0"
    );
    assert!(
        args_out.min_regression_confidence >= 0.0,
        "--min-regression-confidence must be >= 0"
    );
    assert!(
        args_out.default_noise_target_cv_pct.is_finite()
            && args_out.default_noise_target_cv_pct > 0.0,
        "--default-noise-target-cv-pct must be finite and > 0"
    );
    assert!(
        !args_out.json || !args_out.csv,
        "--json and --csv are mutually exclusive"
    );
    args_out
}

fn metric_to_str(metric: MetricFilter) -> &'static str {
    match metric {
        MetricFilter::Median => "median",
        MetricFilter::P95 => "p95",
        MetricFilter::All => "all",
    }
}

fn env_mode_to_str(mode: EnvCompatMode) -> &'static str {
    match mode {
        EnvCompatMode::Warn => "warn",
        EnvCompatMode::Fail => "fail",
        EnvCompatMode::Off => "off",
    }
}

fn snapshot_env(snapshot: &PerfSnapshot) -> Option<(&str, &str, Option<&str>, &str)> {
    let env = snapshot
        .gate
        .as_ref()
        .and_then(|g| g.environment.as_ref())
        .or_else(|| snapshot.probe.as_ref().and_then(|p| p.environment.as_ref()))?;
    Some((
        &env.os,
        &env.arch,
        env.cpu_model.as_deref(),
        &env.rustc_version,
    ))
}

fn env_mismatch_fields(snapshots: &[PerfSnapshot]) -> Vec<String> {
    let mut os_vals: BTreeSet<&str> = BTreeSet::new();
    let mut arch_vals: BTreeSet<&str> = BTreeSet::new();
    let mut cpu_vals: BTreeSet<Option<&str>> = BTreeSet::new();
    let mut rustc_vals: BTreeSet<&str> = BTreeSet::new();
    for snapshot in snapshots {
        if let Some((os, arch, cpu, rustc)) = snapshot_env(snapshot) {
            os_vals.insert(os);
            arch_vals.insert(arch);
            cpu_vals.insert(cpu);
            rustc_vals.insert(rustc);
        }
    }
    let mut out = Vec::new();
    if os_vals.len() > 1 {
        out.push("os".to_string());
    }
    if arch_vals.len() > 1 {
        out.push("arch".to_string());
    }
    if cpu_vals.len() > 1 {
        out.push("cpu_model".to_string());
    }
    if rustc_vals.len() > 1 {
        out.push("rustc_version".to_string());
    }
    out
}

fn case_noise_targets(default_noise_target_cv_pct: f64) -> BTreeMap<String, f64> {
    let mut out = BTreeMap::new();
    for case in load_cases() {
        out.insert(
            case.id.clone(),
            case.noise_target_cv_pct
                .unwrap_or(default_noise_target_cv_pct),
        );
    }
    out
}

fn aggregate_rows(
    snapshots: &[PerfSnapshot],
    source: SourceFilter,
    metric: MetricFilter,
    case_noise_targets: &BTreeMap<String, f64>,
    default_noise_target_cv_pct: f64,
) -> Vec<TrendRow> {
    let mut series: BTreeMap<(String, String, String), Vec<(String, f64)>> = BTreeMap::new();
    for snapshot in snapshots {
        if let Some(gate) = snapshot
            .gate
            .as_ref()
            .filter(|_| source.includes_gate())
        {
            for row in &gate.rows {
                if metric == MetricFilter::Median || metric == MetricFilter::All {
                    series
                        .entry(("gate".to_string(), "median".to_string(), row.id.clone()))
                        .or_default()
                        .push((snapshot.name.clone(), row.median_us));
                }
                if metric == MetricFilter::P95 || metric == MetricFilter::All {
                    series
                        .entry(("gate".to_string(), "p95".to_string(), row.id.clone()))
                        .or_default()
                        .push((snapshot.name.clone(), row.p95_us));
                }
            }
        }
        if let Some(probe) = snapshot
            .probe
            .as_ref()
            .filter(|_| source.includes_probe())
        {
            for row in &probe.rows {
                if metric == MetricFilter::Median || metric == MetricFilter::All {
                    series
                        .entry(("probe".to_string(), "median".to_string(), row.id.clone()))
                        .or_default()
                        .push((snapshot.name.clone(), row.median_us));
                }
                if metric == MetricFilter::P95 || metric == MetricFilter::All {
                    series
                        .entry(("probe".to_string(), "p95".to_string(), row.id.clone()))
                        .or_default()
                        .push((snapshot.name.clone(), row.p95_us));
                }
            }
        }
    }

    let mut out = Vec::new();
    for ((src, m, id), values) in series {
        if values.len() < 2 {
            continue;
        }
        let first = values.first().expect("first value");
        let last = values.last().expect("last value");
        let mut sorted_values: Vec<f64> = values.iter().map(|(_, v)| *v).collect();
        let volatility_cv_pct = stats_cv_pct(&sorted_values);
        sorted_values.sort_by(|a, b| a.partial_cmp(b).expect("finite floats"));
        let min_v = sorted_values[0];
        let max_v = sorted_values[sorted_values.len() - 1];
        let volatility_mad_pct = stats_mad_pct(&sorted_values);
        let delta = last.1 - first.1;
        let delta_pct = if first.1 == 0.0 {
            0.0
        } else {
            (delta / first.1) * 100.0
        };
        let slope = delta / ((values.len() - 1) as f64);
        let noise_target_cv_pct = case_noise_targets
            .get(&id)
            .copied()
            .unwrap_or(default_noise_target_cv_pct);
        let regression_confidence = if delta_pct <= 0.0 {
            0.0
        } else {
            delta_pct / volatility_mad_pct.max(0.001)
        };
        out.push(TrendRow {
            source: src,
            metric: m,
            id,
            points: values.len(),
            first_snapshot: first.0.clone(),
            last_snapshot: last.0.clone(),
            first_us: first.1,
            last_us: last.1,
            delta_us: delta,
            delta_pct,
            min_us: min_v,
            max_us: max_v,
            slope_us_per_snapshot: slope,
            volatility_cv_pct,
            volatility_mad_pct,
            noise_target_cv_pct,
            regression_confidence,
            effective_threshold_pct: None,
            regression_over_effective_threshold: None,
        });
    }
    out
}

fn effective_threshold_pct(row: &TrendRow, base_threshold_pct: f64) -> f64 {
    base_threshold_pct + (row.volatility_cv_pct - row.noise_target_cv_pct).max(0.0)
}

fn annotate_regressions(
    rows: &mut [TrendRow],
    threshold_pct: f64,
    min_regression_confidence: f64,
) -> usize {
    let mut count = 0;
    for row in rows {
        let threshold = effective_threshold_pct(row, threshold_pct);
        let over =
            row.delta_pct > threshold && row.regression_confidence >= min_regression_confidence;
        row.effective_threshold_pct = Some(threshold);
        row.regression_over_effective_threshold = Some(over);
        if over {
            count += 1;
        }
    }
    count
}

fn main() {
    let args = parse_args();
    if !args.history_dir.exists() {
        panic!(
            "history dir '{}' does not exist",
            args.history_dir.display()
        );
    }
    let mut snapshots = load_snapshots(&args.history_dir);
    if snapshots.is_empty() {
        panic!(
            "no recognizable snapshots in '{}'; expected subdirs containing gate/probe json",
            args.history_dir.display()
        );
    }
    if let Some(window) = args.window {
        if snapshots.len() > window {
            let keep_from = snapshots.len() - window;
            snapshots = snapshots.split_off(keep_from);
        }
    }

    let mismatch_fields = if args.env_compat == EnvCompatMode::Off {
        Vec::new()
    } else {
        env_mismatch_fields(&snapshots)
    };
    if !mismatch_fields.is_empty() {
        let msg = format!(
            "environment mismatch across snapshots (fields: {})",
            mismatch_fields.join(", ")
        );
        match args.env_compat {
            EnvCompatMode::Warn => eprintln!("warning: {}", msg),
            EnvCompatMode::Fail => {
                eprintln!("error: {}", msg);
                std::process::exit(2);
            }
            EnvCompatMode::Off => {}
        }
    }

    let case_noise_targets = case_noise_targets(args.default_noise_target_cv_pct);
    let mut rows = aggregate_rows(
        &snapshots,
        args.source,
        args.metric,
        &case_noise_targets,
        args.default_noise_target_cv_pct,
    );
    if let Some(filter) = &args.filter {
        rows.retain(|r| r.id.contains(filter));
    }
    rows.sort_by(|a, b| {
        b.delta_pct
            .abs()
            .partial_cmp(&a.delta_pct.abs())
            .expect("finite delta pct")
            .then_with(|| a.source.cmp(&b.source))
            .then_with(|| a.metric.cmp(&b.metric))
            .then_with(|| a.id.cmp(&b.id))
    });
    if rows.len() > args.top {
        rows.truncate(args.top);
    }

    let regressions_over_threshold = args.fail_regressions_pct.map(|threshold_pct| {
        annotate_regressions(&mut rows, threshold_pct, args.min_regression_confidence)
    });

    if args.json {
        let report = TrendReport {
            history_dir: args.history_dir.display().to_string(),
            source: args.source.to_str().to_string(),
            metric: metric_to_str(args.metric).to_string(),
            env_compat: env_mode_to_str(args.env_compat).to_string(),
            env_mismatch_fields: mismatch_fields.clone(),
            window: args.window,
            snapshots_scanned: snapshots.len(),
            regressions_over_threshold,
            fail_regressions_pct: args.fail_regressions_pct,
            min_regression_confidence: args.min_regression_confidence,
            default_noise_target_cv_pct: args.default_noise_target_cv_pct,
            rows,
        };
        println!(
            "{}",
            serde_json::to_string_pretty(&report).expect("serialize trend report")
        );
        return;
    }

    if args.csv {
        println!(
            "source,metric,id,points,first_snapshot,last_snapshot,first_us,last_us,delta_us,delta_pct,min_us,max_us,slope_us_per_snapshot,volatility_cv_pct,volatility_mad_pct,noise_target_cv_pct,regression_confidence,effective_threshold_pct,regression_over_effective_threshold"
        );
        for row in rows {
            println!(
                "{},{},{},{},{},{},{:.3},{:.3},{:+.3},{:+.6},{:.3},{:.3},{:+.6},{:.3},{:.3},{:.3},{:.3},{},{}",
                csv_escape(&row.source),
                csv_escape(&row.metric),
                csv_escape(&row.id),
                row.points,
                csv_escape(&row.first_snapshot),
                csv_escape(&row.last_snapshot),
                row.first_us,
                row.last_us,
                row.delta_us,
                row.delta_pct,
                row.min_us,
                row.max_us,
                row.slope_us_per_snapshot,
                row.volatility_cv_pct,
                row.volatility_mad_pct,
                row.noise_target_cv_pct,
                row.regression_confidence,
                row.effective_threshold_pct
                    .map(|v| format!("{v:.3}"))
                    .unwrap_or_default(),
                row.regression_over_effective_threshold
                    .map(|v| v.to_string())
                    .unwrap_or_default()
            );
        }
        return;
    }

    println!(
        "perf trend history_dir={} snapshots={} source={} metric={} env_compat={} env_mismatch_fields={} window={} top={} fail_regressions_pct={} min_regression_confidence={:.3} default_noise_target_cv_pct={:.3}",
        args.history_dir.display(),
        snapshots.len(),
        args.source.to_str(),
        metric_to_str(args.metric),
        env_mode_to_str(args.env_compat),
        if mismatch_fields.is_empty() {
            "-".to_string()
        } else {
            mismatch_fields.join(",")
        },
        args.window
            .map(|w| w.to_string())
            .unwrap_or_else(|| "-".to_string()),
        args.top
        ,
        args.fail_regressions_pct
            .map(|t| format!("{:.3}", t))
            .unwrap_or_else(|| "-".to_string()),
        args.min_regression_confidence,
        args.default_noise_target_cv_pct
    );
    println!(
        "source | metric | id | points | first_snapshot | last_snapshot | first_us | last_us | delta_us | delta_pct | cv_pct | mad_pct | confidence | eff_threshold | over_threshold | slope_us/snap"
    );
    for row in &rows {
        println!(
            "{} | {} | {} | {} | {} | {} | {:.3} | {:.3} | {:+.3} | {:+.4}% | {:.3}% | {:.3}% | {:.3} | {} | {} | {:+.4}",
            row.source,
            row.metric,
            row.id,
            row.points,
            row.first_snapshot,
            row.last_snapshot,
            row.first_us,
            row.last_us,
            row.delta_us,
            row.delta_pct,
            row.volatility_cv_pct,
            row.volatility_mad_pct,
            row.regression_confidence,
            row.effective_threshold_pct
                .map(|v| format!("{v:.3}%"))
                .unwrap_or_else(|| "-".to_string()),
            row.regression_over_effective_threshold
                .map(|v| v.to_string())
                .unwrap_or_else(|| "-".to_string()),
            row.slope_us_per_snapshot
        );
    }

    if let Some(threshold_pct) = args.fail_regressions_pct {
        let regressions = regressions_over_threshold.unwrap_or(0);
        println!(
            "\nregressions over threshold ({:.3}%, min_confidence={:.3}): {}",
            threshold_pct, args.min_regression_confidence, regressions
        );
        if regressions > 0 {
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{annotate_regressions, TrendRow};

    fn mk_row(delta_pct: f64, volatility_cv_pct: f64, volatility_mad_pct: f64) -> TrendRow {
        TrendRow {
            source: "probe".to_string(),
            metric: "median".to_string(),
            id: "id".to_string(),
            points: 2,
            first_snapshot: "a".to_string(),
            last_snapshot: "b".to_string(),
            first_us: 1.0,
            last_us: 1.0,
            delta_us: 0.0,
            delta_pct,
            min_us: 1.0,
            max_us: 1.0,
            slope_us_per_snapshot: 0.0,
            volatility_cv_pct,
            volatility_mad_pct,
            noise_target_cv_pct: 10.0,
            regression_confidence: if delta_pct > 0.0 {
                delta_pct / volatility_mad_pct.max(0.001)
            } else {
                0.0
            },
            effective_threshold_pct: None,
            regression_over_effective_threshold: None,
        }
    }

    #[test]
    fn annotate_regressions_counts_only_positive_deltas_above_threshold() {
        let mut rows = vec![
            mk_row(-5.0, 5.0, 5.0),
            mk_row(0.0, 5.0, 5.0),
            mk_row(4.9, 5.0, 5.0),
            mk_row(5.1, 5.0, 5.0),
            mk_row(9.0, 5.0, 5.0),
        ];
        assert_eq!(annotate_regressions(&mut rows, 5.0, 0.5), 2);
    }

    #[test]
    fn annotate_regressions_ignores_equal_threshold() {
        let mut rows = vec![mk_row(5.0, 5.0, 5.0), mk_row(5.00001, 5.0, 5.0)];
        assert_eq!(annotate_regressions(&mut rows, 5.0, 0.5), 1);
    }

    #[test]
    fn annotate_regressions_respects_confidence_floor() {
        let mut rows = vec![
            mk_row(12.0, 30.0, 20.0),
            mk_row(15.0, 8.0, 3.0),
            mk_row(30.0, 80.0, 25.0),
        ];
        assert_eq!(annotate_regressions(&mut rows, 10.0, 2.0), 1);
    }
}
