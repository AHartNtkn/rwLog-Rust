#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use rwlog::perf_corpus::{
    load_cases, load_snapshots, PerfSnapshot, SourceFilter, stats_cv_pct, stats_mad_pct,
    stats_mean, stats_median_sorted,
};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

/// Time-series data keyed by (source, metric, case_id) -> list of (snapshot_name, value).
type MetricSeries = BTreeMap<(String, String, String), Vec<(String, f64)>>;

/// Series grouped by (source, metric) -> list of (case_id, values).
type GroupedSeries = BTreeMap<(String, String), Vec<(String, Vec<(String, f64)>)>>;

#[derive(Clone, Debug)]
struct Args {
    history_dir: PathBuf,
    source: SourceFilter,
    window: Option<usize>,
    min_points: usize,
    noisy_cv_pct: f64,
    redundancy_corr_min: f64,
    top_redundant: usize,
    json: bool,
}

#[derive(Clone, Debug, Serialize)]
struct StaleCase {
    id: String,
    points: usize,
    in_latest_snapshot: bool,
    reason: String,
}

#[derive(Clone, Debug, Serialize)]
struct NoisyCase {
    source: String,
    metric: String,
    id: String,
    points: usize,
    cv_pct: f64,
    mad_pct: f64,
}

#[derive(Clone, Debug, Serialize)]
struct RedundantPair {
    source: String,
    metric: String,
    left_id: String,
    right_id: String,
    points: usize,
    corr: f64,
    median_ratio: f64,
}

#[derive(Clone, Debug, Serialize)]
struct HealthReport {
    history_dir: String,
    source: String,
    window: Option<usize>,
    snapshots_scanned: usize,
    min_points: usize,
    noisy_cv_pct: f64,
    redundancy_corr_min: f64,
    stale_cases: Vec<StaleCase>,
    noisy_cases: Vec<NoisyCase>,
    redundant_pairs: Vec<RedundantPair>,
}

fn parse_args() -> Args {
    let mut args_out = Args {
        history_dir: PathBuf::from("perf/history"),
        source: SourceFilter::All,
        window: None,
        min_points: 3,
        noisy_cv_pct: 25.0,
        redundancy_corr_min: 0.995,
        top_redundant: 50,
        json: false,
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
        if arg == "--window" {
            args_out.window = Some(
                args.next()
                    .expect("--window requires value")
                    .parse()
                    .expect("--window must be integer"),
            );
            continue;
        }
        if arg == "--min-points" {
            args_out.min_points = args
                .next()
                .expect("--min-points requires value")
                .parse()
                .expect("--min-points must be integer");
            continue;
        }
        if arg == "--noisy-cv-pct" {
            args_out.noisy_cv_pct = args
                .next()
                .expect("--noisy-cv-pct requires value")
                .parse()
                .expect("--noisy-cv-pct must be float");
            continue;
        }
        if arg == "--redundancy-corr-min" {
            args_out.redundancy_corr_min = args
                .next()
                .expect("--redundancy-corr-min requires value")
                .parse()
                .expect("--redundancy-corr-min must be float");
            continue;
        }
        if arg == "--top-redundant" {
            args_out.top_redundant = args
                .next()
                .expect("--top-redundant requires value")
                .parse()
                .expect("--top-redundant must be integer");
            continue;
        }
        if arg == "--json" {
            args_out.json = true;
            continue;
        }
        if arg == "--help" || arg == "-h" {
            println!(
                "Usage: perf_corpus_health [--history-dir PATH] [--source gate|probe|all] [--window N] [--min-points N] [--noisy-cv-pct F] [--redundancy-corr-min F] [--top-redundant N] [--json]"
            );
            std::process::exit(0);
        }
        panic!("unknown argument: {arg}");
    }

    assert!(args_out.min_points > 0, "--min-points must be > 0");
    assert!(
        args_out.window.map(|w| w > 0).unwrap_or(true),
        "--window must be > 0"
    );
    assert!(
        args_out.noisy_cv_pct.is_finite() && args_out.noisy_cv_pct >= 0.0,
        "--noisy-cv-pct must be finite and >= 0"
    );
    assert!(
        args_out.redundancy_corr_min.is_finite()
            && args_out.redundancy_corr_min >= -1.0
            && args_out.redundancy_corr_min <= 1.0,
        "--redundancy-corr-min must be between -1 and 1"
    );
    assert!(args_out.top_redundant > 0, "--top-redundant must be > 0");
    args_out
}

fn pearson_corr(xs: &[f64], ys: &[f64]) -> Option<f64> {
    if xs.len() != ys.len() || xs.len() < 2 {
        return None;
    }
    let mx = stats_mean(xs);
    let my = stats_mean(ys);
    let mut num = 0.0;
    let mut den_x = 0.0;
    let mut den_y = 0.0;
    for (x, y) in xs.iter().zip(ys.iter()) {
        let dx = x - mx;
        let dy = y - my;
        num += dx * dy;
        den_x += dx * dx;
        den_y += dy * dy;
    }
    let den = (den_x * den_y).sqrt();
    if den == 0.0 {
        return None;
    }
    Some(num / den)
}

fn push_rows(
    series: &mut MetricSeries,
    snapshot_name: &str,
    source_str: &str,
    rows: impl Iterator<Item = (String, f64, f64)>,
) {
    for (id, median, p95) in rows {
        series
            .entry((source_str.to_string(), "median".to_string(), id.clone()))
            .or_default()
            .push((snapshot_name.to_string(), median));
        series
            .entry((source_str.to_string(), "p95".to_string(), id))
            .or_default()
            .push((snapshot_name.to_string(), p95));
    }
}

fn collect_series(snapshots: &[PerfSnapshot], source: SourceFilter) -> MetricSeries {
    let mut series: MetricSeries = BTreeMap::new();
    for snapshot in snapshots {
        if let Some(gate) = snapshot.gate.as_ref().filter(|_| source.includes_gate()) {
            push_rows(
                &mut series,
                &snapshot.name,
                "gate",
                gate.rows
                    .iter()
                    .map(|r| (r.id.clone(), r.median_us, r.p95_us)),
            );
        }
        if let Some(probe) = snapshot.probe.as_ref().filter(|_| source.includes_probe()) {
            push_rows(
                &mut series,
                &snapshot.name,
                "probe",
                probe
                    .rows
                    .iter()
                    .map(|r| (r.id.clone(), r.median_us, r.p95_us)),
            );
        }
    }
    series
}

fn latest_present_ids(snapshots: &[PerfSnapshot], source: SourceFilter) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let Some(latest) = snapshots.last() else {
        return out;
    };
    if let Some(gate) = latest.gate.as_ref().filter(|_| source.includes_gate()) {
        for row in &gate.rows {
            out.insert(row.id.clone());
        }
    }
    if let Some(probe) = latest.probe.as_ref().filter(|_| source.includes_probe()) {
        for row in &probe.rows {
            out.insert(row.id.clone());
        }
    }
    out
}

fn stale_cases(
    series: &MetricSeries,
    snapshots: &[PerfSnapshot],
    source: SourceFilter,
    min_points: usize,
) -> Vec<StaleCase> {
    let latest_ids = latest_present_ids(snapshots, source);
    let mut points_by_id: BTreeMap<String, usize> = BTreeMap::new();
    for ((_, _, id), values) in series {
        let entry = points_by_id.entry(id.clone()).or_insert(0);
        *entry = (*entry).max(values.len());
    }
    let mut stale = Vec::new();
    for case in load_cases() {
        let points = points_by_id.get(&case.id).copied().unwrap_or(0);
        let in_latest = latest_ids.contains(&case.id);
        let reason = if points < min_points {
            format!("insufficient_points(<{})", min_points)
        } else if !in_latest {
            "missing_in_latest_snapshot".to_string()
        } else {
            continue;
        };
        stale.push(StaleCase {
            id: case.id,
            points,
            in_latest_snapshot: in_latest,
            reason,
        });
    }
    stale.sort_by(|a, b| a.id.cmp(&b.id));
    stale
}

fn noisy_cases(series: &MetricSeries, noisy_cv_pct_threshold: f64) -> Vec<NoisyCase> {
    let mut out = Vec::new();
    for ((source, metric, id), values) in series {
        if values.len() < 2 {
            continue;
        }
        let mut nums: Vec<f64> = values.iter().map(|(_, v)| *v).collect();
        let cv = stats_cv_pct(&nums);
        if cv > noisy_cv_pct_threshold {
            nums.sort_by(|a, b| a.partial_cmp(b).expect("finite floats"));
            out.push(NoisyCase {
                source: source.clone(),
                metric: metric.clone(),
                id: id.clone(),
                points: nums.len(),
                cv_pct: cv,
                mad_pct: stats_mad_pct(&nums),
            });
        }
    }
    out.sort_by(|a, b| {
        b.cv_pct
            .partial_cmp(&a.cv_pct)
            .expect("finite cv")
            .then_with(|| a.source.cmp(&b.source))
            .then_with(|| a.metric.cmp(&b.metric))
            .then_with(|| a.id.cmp(&b.id))
    });
    out
}

fn redundant_pairs(
    series: MetricSeries,
    min_points: usize,
    corr_min: f64,
    top: usize,
) -> Vec<RedundantPair> {
    let mut grouped: GroupedSeries = BTreeMap::new();
    for ((source, metric, id), values) in series {
        grouped
            .entry((source, metric))
            .or_default()
            .push((id, values));
    }

    let mut out = Vec::new();
    for ((source, metric), cases) in &grouped {
        let case_maps: Vec<BTreeMap<&str, f64>> = cases
            .iter()
            .map(|(_, vals)| vals.iter().map(|(s, v)| (s.as_str(), *v)).collect())
            .collect();
        for i in 0..cases.len() {
            for j in (i + 1)..cases.len() {
                let (id_a, vals_a) = &cases[i];
                let map_b = &case_maps[j];
                let mut xs = Vec::new();
                let mut ys = Vec::new();
                for (snap, va) in vals_a {
                    if let Some(vb) = map_b.get(snap.as_str()) {
                        xs.push(*va);
                        ys.push(*vb);
                    }
                }
                if xs.len() < min_points {
                    continue;
                }
                let Some(corr) = pearson_corr(&xs, &ys) else {
                    continue;
                };
                if corr < corr_min {
                    continue;
                }
                xs.sort_by(|a, b| a.partial_cmp(b).expect("finite floats"));
                ys.sort_by(|a, b| a.partial_cmp(b).expect("finite floats"));
                let med_a = stats_median_sorted(&xs);
                let med_b = stats_median_sorted(&ys);
                let ratio = if med_b == 0.0 { 0.0 } else { med_a / med_b };
                out.push(RedundantPair {
                    source: source.clone(),
                    metric: metric.clone(),
                    left_id: id_a.clone(),
                    right_id: cases[j].0.clone(),
                    points: xs.len(),
                    corr,
                    median_ratio: ratio,
                });
            }
        }
    }
    out.sort_by(|a, b| {
        b.corr
            .partial_cmp(&a.corr)
            .expect("finite corr")
            .then_with(|| a.source.cmp(&b.source))
            .then_with(|| a.metric.cmp(&b.metric))
            .then_with(|| a.left_id.cmp(&b.left_id))
            .then_with(|| a.right_id.cmp(&b.right_id))
    });
    if out.len() > top {
        out.truncate(top);
    }
    out
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

    let series = collect_series(&snapshots, args.source);
    let stale = stale_cases(&series, &snapshots, args.source, args.min_points);
    let noisy = noisy_cases(&series, args.noisy_cv_pct);
    let redundant = redundant_pairs(
        series,
        args.min_points,
        args.redundancy_corr_min,
        args.top_redundant,
    );

    let report = HealthReport {
        history_dir: args.history_dir.display().to_string(),
        source: args.source.to_str().to_string(),
        window: args.window,
        snapshots_scanned: snapshots.len(),
        min_points: args.min_points,
        noisy_cv_pct: args.noisy_cv_pct,
        redundancy_corr_min: args.redundancy_corr_min,
        stale_cases: stale,
        noisy_cases: noisy,
        redundant_pairs: redundant,
    };

    if args.json {
        println!(
            "{}",
            serde_json::to_string_pretty(&report).expect("serialize health report")
        );
        return;
    }

    println!(
        "perf corpus health history_dir={} source={} snapshots={} window={} min_points={} noisy_cv_pct={:.3} redundancy_corr_min={:.3}",
        report.history_dir,
        report.source,
        report.snapshots_scanned,
        report
            .window
            .map(|w| w.to_string())
            .unwrap_or_else(|| "-".to_string()),
        report.min_points,
        report.noisy_cv_pct,
        report.redundancy_corr_min
    );
    println!(
        "stale_cases={} noisy_cases={} redundant_pairs={}",
        report.stale_cases.len(),
        report.noisy_cases.len(),
        report.redundant_pairs.len()
    );

    println!("\n-- stale cases (top 20) --");
    for row in report.stale_cases.iter().take(20) {
        println!(
            "{} | points={} | in_latest={} | {}",
            row.id, row.points, row.in_latest_snapshot, row.reason
        );
    }

    println!("\n-- noisy cases (top 20 by cv) --");
    for row in report.noisy_cases.iter().take(20) {
        println!(
            "{}:{}:{} | points={} | cv={:.3}% | mad={:.3}%",
            row.source, row.metric, row.id, row.points, row.cv_pct, row.mad_pct
        );
    }

    println!("\n-- redundant pairs (top 20 by corr) --");
    for row in report.redundant_pairs.iter().take(20) {
        println!(
            "{}:{}:{}~{} | points={} | corr={:.6} | median_ratio={:.6}",
            row.source,
            row.metric,
            row.left_id,
            row.right_id,
            row.points,
            row.corr,
            row.median_ratio
        );
    }
}
