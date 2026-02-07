use rwlog::perf_corpus::load_cases;
use serde::Deserialize;
use serde::Serialize;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SourceFilter {
    Gate,
    Probe,
    All,
}

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

#[derive(Clone, Debug, Deserialize)]
struct EnvironmentFingerprint {
    os: String,
    arch: String,
    #[serde(default)]
    cpu_model: Option<String>,
    rustc_version: String,
}

#[derive(Clone, Debug, Deserialize)]
struct GateRow {
    id: String,
    median_us: f64,
    p95_us: f64,
    #[allow(dead_code)]
    ok: bool,
}

#[derive(Clone, Debug, Deserialize)]
struct GateReport {
    #[serde(default)]
    environment: Option<EnvironmentFingerprint>,
    rows: Vec<GateRow>,
}

#[derive(Clone, Debug, Deserialize)]
struct RunRow {
    id: String,
    median_us: f64,
    p95_us: f64,
}

#[derive(Clone, Debug, Deserialize)]
struct RunReport {
    #[serde(default)]
    environment: Option<EnvironmentFingerprint>,
    rows: Vec<RunRow>,
}

#[derive(Clone, Debug)]
struct Snapshot {
    name: String,
    gate: Option<GateReport>,
    probe: Option<RunReport>,
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
        args_out.default_noise_target_cv_pct.is_finite() && args_out.default_noise_target_cv_pct > 0.0,
        "--default-noise-target-cv-pct must be finite and > 0"
    );
    assert!(
        !args_out.json || !args_out.csv,
        "--json and --csv are mutually exclusive"
    );
    args_out
}

fn load_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Option<T> {
    let text = fs::read_to_string(path).ok()?;
    serde_json::from_str(&text).ok()
}

fn load_snapshot(dir: &Path) -> Option<Snapshot> {
    let name = dir.file_name()?.to_str()?.to_string();
    let gate = load_json::<GateReport>(&dir.join("gate.json"))
        .or_else(|| load_json::<GateReport>(&dir.join("quick_gate.json")));
    let probe = load_json::<RunReport>(&dir.join("probe.json"))
        .or_else(|| load_json::<RunReport>(&dir.join("quick_probe.json")))
        .or_else(|| load_json::<RunReport>(&dir.join("stress_probe.json")));
    if gate.is_none() && probe.is_none() {
        return None;
    }
    Some(Snapshot { name, gate, probe })
}

fn load_snapshots(history_dir: &Path) -> Vec<Snapshot> {
    let entries = fs::read_dir(history_dir)
        .unwrap_or_else(|e| panic!("read_dir {}: {}", history_dir.display(), e));
    let mut dirs = Vec::new();
    for entry in entries {
        let entry = entry.expect("dir entry");
        let path = entry.path();
        if path.is_dir() {
            dirs.push(path);
        }
    }
    dirs.sort();
    let mut snapshots = Vec::new();
    for dir in dirs {
        if let Some(s) = load_snapshot(&dir) {
            snapshots.push(s);
        }
    }
    snapshots
}

fn csv_escape(s: &str) -> String {
    if s.contains(',') || s.contains('"') || s.contains('\n') {
        format!("\"{}\"", s.replace('"', "\"\""))
    } else {
        s.to_string()
    }
}

fn source_to_str(source: SourceFilter) -> &'static str {
    match source {
        SourceFilter::Gate => "gate",
        SourceFilter::Probe => "probe",
        SourceFilter::All => "all",
    }
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

fn snapshot_env(snapshot: &Snapshot) -> Option<&EnvironmentFingerprint> {
    if let Some(g) = &snapshot.gate {
        if let Some(env) = &g.environment {
            return Some(env);
        }
    }
    if let Some(p) = &snapshot.probe {
        if let Some(env) = &p.environment {
            return Some(env);
        }
    }
    None
}

fn env_mismatch_fields(snapshots: &[Snapshot]) -> Vec<String> {
    let mut os_vals = BTreeSet::new();
    let mut arch_vals = BTreeSet::new();
    let mut cpu_vals = BTreeSet::new();
    let mut rustc_vals = BTreeSet::new();
    for snapshot in snapshots {
        if let Some(env) = snapshot_env(snapshot) {
            os_vals.insert(env.os.clone());
            arch_vals.insert(env.arch.clone());
            cpu_vals.insert(env.cpu_model.clone().unwrap_or_else(|| "-".to_string()));
            rustc_vals.insert(env.rustc_version.clone());
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

fn median_absolute_deviation_pct(values: &[f64]) -> f64 {
    if values.is_empty() {
        return 0.0;
    }
    let mut sorted = values.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).expect("finite floats"));
    let median = median_sorted(&sorted);
    if median <= 0.0 {
        return 0.0;
    }
    let mut abs_dev: Vec<f64> = sorted.iter().map(|v| (v - median).abs()).collect();
    abs_dev.sort_by(|a, b| a.partial_cmp(b).expect("finite floats"));
    (median_sorted(&abs_dev) / median) * 100.0
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
    snapshots: &[Snapshot],
    source: SourceFilter,
    metric: MetricFilter,
    case_noise_targets: &BTreeMap<String, f64>,
    default_noise_target_cv_pct: f64,
) -> Vec<TrendRow> {
    let mut series: BTreeMap<(String, String, String), Vec<(String, f64)>> = BTreeMap::new();
    for snapshot in snapshots {
        if (source == SourceFilter::Gate || source == SourceFilter::All) && snapshot.gate.is_some()
        {
            let gate = snapshot.gate.as_ref().expect("gate exists");
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
        if (source == SourceFilter::Probe || source == SourceFilter::All)
            && snapshot.probe.is_some()
        {
            let probe = snapshot.probe.as_ref().expect("probe exists");
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
        let mut min_v = f64::INFINITY;
        let mut max_v = f64::NEG_INFINITY;
        let numeric_values: Vec<f64> = values.iter().map(|(_, v)| *v).collect();
        for (_, v) in &values {
            min_v = min_v.min(*v);
            max_v = max_v.max(*v);
        }
        let delta = last.1 - first.1;
        let delta_pct = if first.1 == 0.0 {
            0.0
        } else {
            (delta / first.1) * 100.0
        };
        let slope = delta / ((values.len() - 1) as f64);
        let volatility_cv_pct = coefficient_of_variation_pct(&numeric_values);
        let volatility_mad_pct = median_absolute_deviation_pct(&numeric_values);
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

fn is_regression(row: &TrendRow, threshold_pct: f64, min_regression_confidence: f64) -> bool {
    let threshold = effective_threshold_pct(row, threshold_pct);
    row.delta_pct > threshold && row.regression_confidence >= min_regression_confidence
}

fn annotate_regressions(
    rows: &mut [TrendRow],
    threshold_pct: f64,
    min_regression_confidence: f64,
) {
    for row in rows {
        let threshold = effective_threshold_pct(row, threshold_pct);
        let over = is_regression(row, threshold_pct, min_regression_confidence);
        row.effective_threshold_pct = Some(threshold);
        row.regression_over_effective_threshold = Some(over);
    }
}

fn count_regressions(
    rows: &[TrendRow],
    threshold_pct: f64,
    min_regression_confidence: f64,
) -> usize {
    rows.iter()
        .filter(|r| is_regression(r, threshold_pct, min_regression_confidence))
        .count()
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
        annotate_regressions(&mut rows, threshold_pct, args.min_regression_confidence);
        count_regressions(&rows, threshold_pct, args.min_regression_confidence)
    });

    if args.json {
        let report = TrendReport {
            history_dir: args.history_dir.display().to_string(),
            source: source_to_str(args.source).to_string(),
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
        source_to_str(args.source),
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
    use super::{count_regressions, TrendRow};

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
    fn count_regressions_counts_only_positive_deltas_above_threshold() {
        let rows = vec![
            mk_row(-5.0, 5.0, 5.0),
            mk_row(0.0, 5.0, 5.0),
            mk_row(4.9, 5.0, 5.0),
            mk_row(5.1, 5.0, 5.0),
            mk_row(9.0, 5.0, 5.0),
        ];
        assert_eq!(count_regressions(&rows, 5.0, 0.5), 2);
    }

    #[test]
    fn count_regressions_ignores_equal_threshold() {
        let rows = vec![mk_row(5.0, 5.0, 5.0), mk_row(5.00001, 5.0, 5.0)];
        assert_eq!(count_regressions(&rows, 5.0, 0.5), 1);
    }

    #[test]
    fn count_regressions_respects_confidence_floor() {
        let rows = vec![
            mk_row(12.0, 30.0, 20.0),
            mk_row(15.0, 8.0, 3.0),
            mk_row(30.0, 80.0, 25.0),
        ];
        assert_eq!(count_regressions(&rows, 10.0, 2.0), 1);
    }
}
