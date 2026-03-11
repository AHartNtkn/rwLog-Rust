#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use rwlog::perf_corpus::EnvironmentFingerprint;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;

#[derive(Clone, Debug, Deserialize)]
struct SanityCaseRow {
    tier: String,
    category: String,
}

#[derive(Clone, Debug, Deserialize)]
struct SanityReport {
    environment: EnvironmentFingerprint,
    selected_cases: usize,
    lint_requested: bool,
    lint_ok: bool,
    validate_requested: bool,
    validate_ok: bool,
    rows: Vec<SanityCaseRow>,
}

#[derive(Clone, Debug, Deserialize)]
struct GateRow {
    id: String,
    median_us: f64,
    p95_us: f64,
    budget_median_us: f64,
    budget_p95_us: f64,
    ok: bool,
}

#[derive(Clone, Debug, Deserialize)]
struct GateReport {
    environment: EnvironmentFingerprint,
    samples: usize,
    warmup: usize,
    tolerance_pct: f64,
    rows: Vec<GateRow>,
    failed: bool,
}

#[derive(Clone, Debug, Deserialize)]
struct RunRow {
    id: String,
    category: String,
    median_us: f64,
    p95_us: f64,
    #[serde(default)]
    engine_steps: u64,
    #[serde(default)]
    compose_attempts: u64,
    #[serde(default)]
    meet_attempts: u64,
}

#[derive(Clone, Debug, Deserialize)]
struct RunReport {
    environment: EnvironmentFingerprint,
    iters: usize,
    phase: String,
    rows: Vec<RunRow>,
}

#[derive(Debug)]
struct Args {
    title: String,
    sanity_json: PathBuf,
    gate_json: Option<PathBuf>,
    probe_json: Option<PathBuf>,
    out: Option<PathBuf>,
    status_json_out: Option<PathBuf>,
    fail_on_gate_regression: bool,
}

#[derive(Clone, Debug, Serialize)]
struct StatusCheck {
    name: String,
    status: String,
    message: String,
}

#[derive(Clone, Debug, Serialize)]
struct SanityStatus {
    selected_cases: usize,
    lint_ok: bool,
    validate_ok: bool,
}

#[derive(Clone, Debug, Serialize)]
struct GateStatus {
    total_cases: usize,
    failed_cases: usize,
    failed: bool,
}

#[derive(Clone, Debug, Serialize)]
struct ProbeStatus {
    phase: String,
    iters: usize,
    rows: usize,
}

#[derive(Clone, Debug, Serialize)]
struct CiStatusReport {
    title: String,
    overall_status: String,
    environment: EnvironmentFingerprint,
    sanity: SanityStatus,
    gate: Option<GateStatus>,
    probe: Option<ProbeStatus>,
    checks: Vec<StatusCheck>,
}

fn parse_args() -> Args {
    let mut title = "Perf Corpus Summary".to_string();
    let mut sanity_json = None;
    let mut gate_json = None;
    let mut probe_json = None;
    let mut out = None;
    let mut status_json_out = None;
    let mut fail_on_gate_regression = false;

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        if arg == "--title" {
            title = args.next().expect("--title requires value");
            continue;
        }
        if arg == "--sanity-json" {
            sanity_json = Some(PathBuf::from(
                args.next().expect("--sanity-json requires path"),
            ));
            continue;
        }
        if arg == "--gate-json" {
            gate_json = Some(PathBuf::from(
                args.next().expect("--gate-json requires path"),
            ));
            continue;
        }
        if arg == "--probe-json" {
            probe_json = Some(PathBuf::from(
                args.next().expect("--probe-json requires path"),
            ));
            continue;
        }
        if arg == "--out" {
            out = Some(PathBuf::from(args.next().expect("--out requires path")));
            continue;
        }
        if arg == "--status-json-out" {
            status_json_out = Some(PathBuf::from(
                args.next().expect("--status-json-out requires path"),
            ));
            continue;
        }
        if arg == "--fail-on-gate-regression" {
            fail_on_gate_regression = true;
            continue;
        }
        if arg == "--help" || arg == "-h" {
            println!(
                "Usage: perf_corpus_ci_summary --sanity-json <path> [--gate-json <path>] [--probe-json <path>] [--title <str>] [--out <path>] [--status-json-out <path>] [--fail-on-gate-regression]"
            );
            std::process::exit(0);
        }
        panic!("unknown argument: {arg}");
    }

    Args {
        title,
        sanity_json: sanity_json.expect("--sanity-json is required"),
        gate_json,
        probe_json,
        out,
        status_json_out,
        fail_on_gate_regression,
    }
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &PathBuf) -> T {
    let data =
        fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {}", path.display(), e));
    serde_json::from_str(&data).unwrap_or_else(|e| panic!("parse {}: {}", path.display(), e))
}

fn first_env(
    sanity: &SanityReport,
    gate: Option<&GateReport>,
    probe: Option<&RunReport>,
) -> EnvironmentFingerprint {
    if let Some(g) = gate {
        return g.environment.clone();
    }
    if let Some(p) = probe {
        return p.environment.clone();
    }
    sanity.environment.clone()
}

fn top_gate_rows(rows: &[GateRow], n: usize) -> Vec<GateRow> {
    let mut v: Vec<GateRow> = rows.to_vec();
    v.sort_by(|a, b| {
        let a_util = (a.median_us / a.budget_median_us).max(a.p95_us / a.budget_p95_us);
        let b_util = (b.median_us / b.budget_median_us).max(b.p95_us / b.budget_p95_us);
        b_util
            .partial_cmp(&a_util)
            .expect("finite utilization values")
            .then_with(|| a.id.cmp(&b.id))
    });
    v.truncate(n);
    v
}

fn top_probe_rows(rows: &[RunRow], n: usize) -> Vec<RunRow> {
    let mut v: Vec<RunRow> = rows.to_vec();
    v.sort_by(|a, b| {
        b.median_us
            .partial_cmp(&a.median_us)
            .expect("finite medians")
            .then_with(|| a.id.cmp(&b.id))
    });
    v.truncate(n);
    v
}

fn summarize_categories(rows: &[SanityCaseRow]) -> Vec<(String, usize)> {
    let mut by_cat: BTreeMap<String, usize> = BTreeMap::new();
    for row in rows {
        *by_cat.entry(row.category.clone()).or_insert(0) += 1;
    }
    by_cat.into_iter().collect()
}

fn build_status_report(
    title: &str,
    sanity: &SanityReport,
    gate: Option<&GateReport>,
    probe: Option<&RunReport>,
) -> CiStatusReport {
    let sanity_status = SanityStatus {
        selected_cases: sanity.selected_cases,
        lint_ok: sanity.lint_ok,
        validate_ok: sanity.validate_ok,
    };
    let gate_status = gate.map(|g| GateStatus {
        total_cases: g.rows.len(),
        failed_cases: g.rows.iter().filter(|r| !r.ok).count(),
        failed: g.failed,
    });
    let probe_status = probe.map(|p| ProbeStatus {
        phase: p.phase.clone(),
        iters: p.iters,
        rows: p.rows.len(),
    });
    let mut checks = Vec::new();
    checks.push(StatusCheck {
        name: "sanity_lint".to_string(),
        status: if !sanity.lint_requested {
            "skip".to_string()
        } else if sanity.lint_ok {
            "pass".to_string()
        } else {
            "fail".to_string()
        },
        message: format!(
            "lint_requested={} lint_ok={}",
            sanity.lint_requested, sanity.lint_ok
        ),
    });
    checks.push(StatusCheck {
        name: "sanity_validate".to_string(),
        status: if !sanity.validate_requested {
            "skip".to_string()
        } else if sanity.validate_ok {
            "pass".to_string()
        } else {
            "fail".to_string()
        },
        message: format!(
            "validate_requested={} validate_ok={}",
            sanity.validate_requested, sanity.validate_ok
        ),
    });
    if let Some(g) = &gate_status {
        checks.push(StatusCheck {
            name: "quick_gate".to_string(),
            status: if g.failed { "fail" } else { "pass" }.to_string(),
            message: format!(
                "failed_cases={} total_cases={}",
                g.failed_cases, g.total_cases
            ),
        });
    } else {
        checks.push(StatusCheck {
            name: "quick_gate".to_string(),
            status: "skip".to_string(),
            message: "no gate report provided".to_string(),
        });
    }
    if let Some(p) = &probe_status {
        checks.push(StatusCheck {
            name: "probe_rows".to_string(),
            status: if p.rows > 0 { "pass" } else { "warn" }.to_string(),
            message: format!("rows={} phase={} iters={}", p.rows, p.phase, p.iters),
        });
    } else {
        checks.push(StatusCheck {
            name: "probe_rows".to_string(),
            status: "skip".to_string(),
            message: "no probe report provided".to_string(),
        });
    }

    let gate_failed = gate_status.as_ref().map(|g| g.failed).unwrap_or(false);
    let lint_pass = !sanity.lint_requested || sanity.lint_ok;
    let validate_pass = !sanity.validate_requested || sanity.validate_ok;
    let overall_status = if lint_pass && validate_pass && !gate_failed {
        "pass".to_string()
    } else {
        "fail".to_string()
    };

    CiStatusReport {
        title: title.to_string(),
        overall_status,
        environment: first_env(sanity, gate, probe),
        sanity: sanity_status,
        gate: gate_status,
        probe: probe_status,
        checks,
    }
}

fn render_markdown(
    sanity: &SanityReport,
    gate: Option<&GateReport>,
    probe: Option<&RunReport>,
    title: &str,
) -> String {
    let env = first_env(sanity, gate, probe);
    let mut out = String::new();
    out.push_str(&format!("## {title}\n\n"));
    out.push_str("### Environment\n");
    out.push_str(&format!(
        "- os/arch: `{}` / `{}`\n- cpu: `{}`\n- rustc: `{}`\n- rustflags: `{}`\n- git_sha: `{}`\n- timestamp_unix_s: `{}`\n- run_id: `{}`\n\n",
        env.os,
        env.arch,
        env.cpu_model.as_deref().unwrap_or("-"),
        env.rustc_version,
        env.rustflags.as_deref().unwrap_or("-"),
        env.git_sha.as_deref().unwrap_or("-"),
        env.timestamp_unix_s,
        env.run_id.as_deref().unwrap_or("-"),
    ));

    out.push_str("### Sanity\n");
    out.push_str(&format!(
        "- selected_cases: `{}`\n- lint: `requested={} ok={}`\n- validate: `requested={} ok={}`\n",
        sanity.selected_cases,
        sanity.lint_requested,
        sanity.lint_ok,
        sanity.validate_requested,
        sanity.validate_ok
    ));
    let tiers: BTreeMap<String, usize> = {
        let mut m = BTreeMap::new();
        for row in &sanity.rows {
            *m.entry(row.tier.clone()).or_insert(0) += 1;
        }
        m
    };
    for (tier, count) in tiers {
        out.push_str(&format!("- tier `{}`: `{}`\n", tier, count));
    }
    let categories = summarize_categories(&sanity.rows);
    for (cat, count) in categories {
        out.push_str(&format!("- category `{}`: `{}`\n", cat, count));
    }
    out.push('\n');

    if let Some(g) = gate {
        let failed_count = g.rows.iter().filter(|r| !r.ok).count();
        out.push_str("### Gate\n");
        out.push_str(&format!(
            "- samples/warmup/tolerance: `{}/{}/{:.3}%`\n- failed: `{}`\n",
            g.samples, g.warmup, g.tolerance_pct, failed_count
        ));
        out.push_str(
            "\n| case | median_us | median_budget | p95_us | p95_budget | utilization |\n",
        );
        out.push_str("|---|---:|---:|---:|---:|---:|\n");
        for row in top_gate_rows(&g.rows, 8) {
            let utilization =
                (row.median_us / row.budget_median_us).max(row.p95_us / row.budget_p95_us);
            out.push_str(&format!(
                "| `{}` | {:.3} | {:.3} | {:.3} | {:.3} | {:.3} |\n",
                row.id,
                row.median_us,
                row.budget_median_us,
                row.p95_us,
                row.budget_p95_us,
                utilization
            ));
        }
        out.push('\n');
    }

    if let Some(p) = probe {
        out.push_str("### Probe\n");
        out.push_str(&format!(
            "- phase/iters: `{}` / `{}`\n- rows: `{}`\n",
            p.phase,
            p.iters,
            p.rows.len()
        ));
        out.push_str(
            "\n| case | category | median_us | p95_us | steps | compose_attempts | meet_attempts |\n",
        );
        out.push_str("|---|---|---:|---:|---:|---:|---:|\n");
        for row in top_probe_rows(&p.rows, 10) {
            out.push_str(&format!(
                "| `{}` | `{}` | {:.3} | {:.3} | {} | {} | {} |\n",
                row.id,
                row.category,
                row.median_us,
                row.p95_us,
                row.engine_steps,
                row.compose_attempts,
                row.meet_attempts,
            ));
        }
        out.push('\n');
    }

    out
}

fn main() {
    let args = parse_args();
    let sanity: SanityReport = read_json(&args.sanity_json);
    let gate: Option<GateReport> = args.gate_json.as_ref().map(read_json);
    let probe: Option<RunReport> = args.probe_json.as_ref().map(read_json);

    let markdown = render_markdown(&sanity, gate.as_ref(), probe.as_ref(), &args.title);
    let status_report = build_status_report(&args.title, &sanity, gate.as_ref(), probe.as_ref());

    if let Some(out_path) = args.out {
        fs::write(&out_path, markdown)
            .unwrap_or_else(|e| panic!("write {}: {}", out_path.display(), e));
    } else {
        print!("{}", markdown);
    }
    if let Some(status_json_out) = args.status_json_out {
        let status_json = serde_json::to_string_pretty(&status_report)
            .expect("serialize CI summary status report");
        fs::write(&status_json_out, status_json)
            .unwrap_or_else(|e| panic!("write {}: {}", status_json_out.display(), e));
    }

    if args.fail_on_gate_regression && gate.as_ref().map(|g| g.failed).unwrap_or(false) {
        eprintln!("gate report indicates regression");
        std::process::exit(1);
    }
}
