use serde_json::json;
use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_TMP_ID: AtomicU64 = AtomicU64::new(0);
const MANIFEST_PATH: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml");
const EXE_SUFFIX: &str = std::env::consts::EXE_SUFFIX;

fn bin_path(name: &str) -> PathBuf {
    let profile_dir = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join(profile_dir)
        .join(format!("{name}{EXE_SUFFIX}"))
}

fn run_bin(name: &str, args: &[&str], envs: &[(&str, &str)]) -> Output {
    let path = bin_path(name);
    let mut cmd = if path.exists() {
        Command::new(path)
    } else {
        let mut fallback = Command::new("cargo");
        fallback
            .arg("run")
            .arg("--release")
            .arg("--quiet")
            .arg("--manifest-path")
            .arg(MANIFEST_PATH)
            .arg("--bin")
            .arg(name)
            .arg("--");
        fallback
    };
    cmd.args(args);
    for (k, v) in envs {
        cmd.env(k, v);
    }
    cmd.output()
        .unwrap_or_else(|e| panic!("failed to run binary '{name}': {e}"))
}

fn run_bin_in_dir(name: &str, args: &[&str], cwd: &Path) -> Output {
    let path = bin_path(name);
    let mut cmd = if path.exists() {
        Command::new(path)
    } else {
        let mut fallback = Command::new("cargo");
        fallback
            .arg("run")
            .arg("--release")
            .arg("--quiet")
            .arg("--manifest-path")
            .arg(MANIFEST_PATH)
            .arg("--bin")
            .arg(name)
            .arg("--");
        fallback
    };
    cmd.args(args)
        .current_dir(cwd)
        .output()
        .unwrap_or_else(|e| panic!("failed to run binary '{name}' in {}: {e}", cwd.display()))
}

fn run_bash(script_path: &str, args: &[&str]) -> Output {
    run_bash_with_env(script_path, args, &[])
}

fn run_bash_with_env(script_path: &str, args: &[&str], envs: &[(&str, &str)]) -> Output {
    let mut cmd = Command::new("bash");
    cmd.arg(script_path).args(args);
    for (k, v) in envs {
        cmd.env(k, v);
    }
    cmd.output()
        .unwrap_or_else(|e| panic!("failed to run script '{script_path}': {e}"))
}

fn assert_success(output: &Output, context: &str) {
    if !output.status.success() {
        panic!(
            "{context} failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

fn temp_dir(prefix: &str) -> PathBuf {
    let mut p = std::env::temp_dir();
    let id = NEXT_TMP_ID.fetch_add(1, Ordering::Relaxed);
    p.push(format!("rwlog-{prefix}-{}-{}", std::process::id(), id));
    fs::create_dir_all(&p).expect("create temp dir");
    p
}

fn write_json(path: &Path, value: &Value) {
    fs::write(
        path,
        serde_json::to_vec_pretty(value).expect("serialize json"),
    )
    .expect("write json");
}

fn parse_stdout_json(output: &Output, context: &str) -> Value {
    serde_json::from_slice::<Value>(&output.stdout).unwrap_or_else(|e| {
        panic!(
            "{context}: failed to parse stdout as JSON: {e}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

#[test]
fn perf_binaries_smoke_json_and_csv() {
    let quick_env = [("RWLOG_CORPUS_TIER", "quick")];

    let sanity = run_bin(
        "perf_corpus_sanity",
        &["--lint", "--validate", "--json"],
        &quick_env,
    );
    assert_success(&sanity, "perf_corpus_sanity --json");
    let sanity_json = parse_stdout_json(&sanity, "sanity json");
    assert!(sanity_json["selected_cases"].as_u64().unwrap_or(0) > 0);
    assert!(sanity_json["rows"]
        .as_array()
        .map(|r| !r.is_empty())
        .unwrap_or(false));

    let run = run_bin(
        "perf_corpus_run",
        &[
            "--id",
            "identity_atom",
            "--iters",
            "1",
            "--phase",
            "execute",
            "--json",
        ],
        &quick_env,
    );
    assert_success(&run, "perf_corpus_run --json");
    let run_json = parse_stdout_json(&run, "run json");
    assert_eq!(run_json["selected_cases"].as_u64(), Some(1));
    assert_eq!(run_json["phase"].as_str(), Some("execute"));

    let run_compile = run_bin(
        "perf_corpus_run",
        &[
            "--id",
            "identity_atom",
            "--iters",
            "1",
            "--phase",
            "compile",
            "--json",
        ],
        &quick_env,
    );
    assert_success(&run_compile, "perf_corpus_run --phase compile --json");
    let run_compile_json = parse_stdout_json(&run_compile, "run compile json");
    assert_eq!(run_compile_json["selected_cases"].as_u64(), Some(1));
    assert_eq!(run_compile_json["phase"].as_str(), Some("compile"));

    let alloc = run_bin(
        "perf_corpus_alloc",
        &["--id", "identity_atom", "--iters", "1", "--json"],
        &quick_env,
    );
    assert_success(&alloc, "perf_corpus_alloc --json");
    let alloc_json = parse_stdout_json(&alloc, "alloc json");
    assert_eq!(alloc_json["selected_cases"].as_u64(), Some(1));
    assert!(alloc_json["rows"][0]["exec_alloc_calls"].as_u64().is_some());

    let gate = run_bin("perf_corpus_gate", &["--json"], &[]);
    assert_success(&gate, "perf_corpus_gate --json");
    let gate_json = parse_stdout_json(&gate, "gate json");
    assert!(gate_json["rows"]
        .as_array()
        .map(|r| !r.is_empty())
        .unwrap_or(false));
    assert!(gate_json["failed"].is_boolean());
    assert!(gate_json["rows"][0]["cv_pct"].is_number());
    assert!(gate_json["rows"][0]["samples_used"].as_u64().unwrap_or(0) >= 1);

    let recommend = run_bin(
        "perf_corpus_recommend_gate",
        &[
            "--samples",
            "1",
            "--warmup",
            "0",
            "--filter",
            "identity_atom",
            "--json",
        ],
        &[],
    );
    assert_success(&recommend, "perf_corpus_recommend_gate --json");
    let recommend_json = parse_stdout_json(&recommend, "recommend json");
    assert_eq!(recommend_json["rows"].as_array().map(|r| r.len()), Some(1));
    assert_eq!(
        recommend_json["rows"][0]["id"].as_str(),
        Some("identity_atom")
    );
}

#[test]
fn recommend_apply_and_trend_and_summary_and_diff_behave_as_expected() {
    let tmp = temp_dir("perf-tools");
    let cases_copy = tmp.join("cases.toml");
    fs::copy("benches/perf_corpus_cases.toml", &cases_copy).expect("copy corpus cases");

    let recommend_apply = run_bin(
        "perf_corpus_recommend_gate",
        &[
            "--samples",
            "1",
            "--warmup",
            "0",
            "--filter",
            "identity_atom",
            "--apply",
            "--apply-file",
            cases_copy.to_str().expect("utf8 path"),
            "--json",
        ],
        &[],
    );
    assert_success(
        &recommend_apply,
        "perf_corpus_recommend_gate --apply --json",
    );
    let recommend_apply_json = parse_stdout_json(&recommend_apply, "recommend apply json");
    assert_eq!(recommend_apply_json["applied"].as_bool(), Some(true));
    let copied_cases_text = fs::read_to_string(&cases_copy).expect("read copied cases");
    assert!(copied_cases_text.contains("id = \"identity_atom\""));
    assert!(copied_cases_text.contains("quick_gate_max_median_us ="));
    assert!(copied_cases_text.contains("quick_gate_max_p95_us ="));

    let history = tmp.join("history");
    let s1 = history.join("s1");
    let s2 = history.join("s2");
    fs::create_dir_all(&s1).expect("create snapshot s1");
    fs::create_dir_all(&s2).expect("create snapshot s2");
    write_json(
        &s1.join("probe.json"),
        &json!({"rows":[{"id":"id1","median_us":10.0,"p95_us":12.0}]}),
    );
    write_json(
        &s2.join("probe.json"),
        &json!({"rows":[{"id":"id1","median_us":12.0,"p95_us":14.0}]}),
    );

    let trend_json = run_bin(
        "perf_corpus_trend",
        &[
            "--history-dir",
            history.to_str().expect("utf8 path"),
            "--source",
            "probe",
            "--metric",
            "median",
            "--window",
            "2",
            "--json",
        ],
        &[],
    );
    assert_success(&trend_json, "perf_corpus_trend --json");
    let trend = parse_stdout_json(&trend_json, "trend json");
    assert_eq!(trend["snapshots_scanned"].as_u64(), Some(2));
    assert_eq!(trend["rows"][0]["id"].as_str(), Some("id1"));
    assert!(trend["rows"][0]["volatility_cv_pct"].is_number());
    assert!(trend["rows"][0]["regression_confidence"].is_number());

    let trend_fail = run_bin(
        "perf_corpus_trend",
        &[
            "--history-dir",
            history.to_str().expect("utf8 path"),
            "--source",
            "probe",
            "--metric",
            "median",
            "--window",
            "2",
            "--fail-regressions-pct",
            "10",
        ],
        &[],
    );
    assert_eq!(trend_fail.status.code(), Some(1));

    let sanity_json_path = tmp.join("sanity.json");
    let gate_json_path = tmp.join("gate.json");
    let probe_json_path = tmp.join("probe.json");
    let summary_md_path = tmp.join("summary.md");
    let summary_status_json_path = tmp.join("summary_status.json");
    write_json(
        &sanity_json_path,
        &json!({
            "environment":{
                "os":"linux",
                "arch":"x86_64",
                "cpu_model":null,
                "rustc_version":"rustc test",
                "rustflags":null,
                "timestamp_unix_s":1,
                "git_sha":"abc",
                "run_id":"run1"
            },
            "selected_cases":1,
            "lint_requested":true,
            "lint_ok":true,
            "validate_requested":true,
            "validate_ok":true,
            "rows":[{"tier":"quick","category":"finite_det"}]
        }),
    );
    write_json(
        &gate_json_path,
        &json!({
            "environment":{
                "os":"linux",
                "arch":"x86_64",
                "cpu_model":null,
                "rustc_version":"rustc test",
                "rustflags":null,
                "timestamp_unix_s":1,
                "git_sha":"abc",
                "run_id":"run1"
            },
            "samples":1,
            "warmup":0,
            "tolerance_pct":25.0,
            "rows":[{"id":"id1","median_us":1.0,"p95_us":2.0,"budget_median_us":3.0,"budget_p95_us":4.0,"ok":false}],
            "failed":true
        }),
    );
    write_json(
        &probe_json_path,
        &json!({
            "environment":{
                "os":"linux",
                "arch":"x86_64",
                "cpu_model":null,
                "rustc_version":"rustc test",
                "rustflags":null,
                "timestamp_unix_s":1,
                "git_sha":"abc",
                "run_id":"run1"
            },
            "iters":1,
            "phase":"end_to_end",
            "rows":[{"id":"id1","category":"finite_det","median_us":1.0,"p95_us":2.0,"engine_steps":3,"compose_attempts":4,"meet_attempts":5}]
        }),
    );

    let ci_summary = run_bin(
        "perf_corpus_ci_summary",
        &[
            "--title",
            "Smoke Summary",
            "--sanity-json",
            sanity_json_path.to_str().expect("utf8 path"),
            "--gate-json",
            gate_json_path.to_str().expect("utf8 path"),
            "--probe-json",
            probe_json_path.to_str().expect("utf8 path"),
            "--status-json-out",
            summary_status_json_path.to_str().expect("utf8 path"),
            "--out",
            summary_md_path.to_str().expect("utf8 path"),
        ],
        &[],
    );
    assert_success(&ci_summary, "perf_corpus_ci_summary");
    let summary_md = fs::read_to_string(&summary_md_path).expect("read summary md");
    assert!(summary_md.contains("Smoke Summary"));
    assert!(summary_md.contains("### Gate"));
    assert!(summary_md.contains("### Probe"));
    let status_json_text =
        fs::read_to_string(&summary_status_json_path).expect("read summary status json");
    let status_json: Value =
        serde_json::from_str(&status_json_text).expect("parse summary status json");
    assert_eq!(status_json["overall_status"].as_str(), Some("fail"));
    assert_eq!(status_json["gate"]["failed"].as_bool(), Some(true));
    assert_eq!(status_json["gate"]["failed_cases"].as_u64(), Some(1));
    assert_eq!(status_json["probe"]["rows"].as_u64(), Some(1));

    let ci_summary_fail = run_bin(
        "perf_corpus_ci_summary",
        &[
            "--sanity-json",
            sanity_json_path.to_str().expect("utf8 path"),
            "--gate-json",
            gate_json_path.to_str().expect("utf8 path"),
            "--fail-on-gate-regression",
        ],
        &[],
    );
    assert_eq!(ci_summary_fail.status.code(), Some(1));

    let diff_missing_root_dir = temp_dir("diff-missing");
    let diff_missing = run_bin_in_dir(
        "perf_corpus_diff",
        &["--threshold-pct", "5"],
        &diff_missing_root_dir,
    );
    assert_eq!(diff_missing.status.code(), Some(2));

    let diff_case_dir = tmp
        .join("diff-ok")
        .join("target")
        .join("criterion")
        .join("case_a")
        .join("change");
    fs::create_dir_all(&diff_case_dir).expect("create diff case dir");
    write_json(
        &diff_case_dir.join("estimates.json"),
        &json!({
            "mean":{"point_estimate":0.10},
            "median":{"point_estimate":0.12}
        }),
    );
    let diff_regress = run_bin_in_dir(
        "perf_corpus_diff",
        &["--threshold-pct", "5"],
        &tmp.join("diff-ok"),
    );
    assert_eq!(diff_regress.status.code(), Some(1));
}

#[test]
fn import_artifacts_snapshot_script_copies_expected_files() {
    let tmp = temp_dir("import-artifacts");
    let artifact_dir = tmp.join("artifacts");
    let history_dir = tmp.join("history");
    fs::create_dir_all(&artifact_dir).expect("create artifacts dir");
    fs::create_dir_all(&history_dir).expect("create history dir");

    write_json(
        &artifact_dir.join("quick_sanity.json"),
        &json!({"selected_cases":1}),
    );
    write_json(
        &artifact_dir.join("quick_gate.json"),
        &json!({"failed":false}),
    );
    write_json(&artifact_dir.join("quick_probe.json"), &json!({"rows":[]}));
    fs::write(artifact_dir.join("quick_summary.md"), "# summary\n").expect("write summary");

    let output = run_bash(
        "scripts/perf/import_artifacts_snapshot.sh",
        &[
            "--name",
            "smoke_snapshot",
            "--from",
            artifact_dir.to_str().expect("utf8 path"),
            "--history-dir",
            history_dir.to_str().expect("utf8 path"),
        ],
    );
    assert_success(&output, "import_artifacts_snapshot.sh");

    let imported = history_dir.join("smoke_snapshot");
    assert!(imported.join("sanity.json").exists());
    assert!(imported.join("gate.json").exists());
    assert!(imported.join("probe.json").exists());
    assert!(imported.join("summary.md").exists());

    let second = run_bash(
        "scripts/perf/import_artifacts_snapshot.sh",
        &[
            "--name",
            "smoke_snapshot",
            "--from",
            artifact_dir.to_str().expect("utf8 path"),
            "--history-dir",
            history_dir.to_str().expect("utf8 path"),
        ],
    );
    assert_eq!(second.status.code(), Some(2));
}

#[test]
fn capture_snapshot_and_trend_scripts_work() {
    let tmp = temp_dir("capture-trend");
    let history_dir = tmp.join("history");
    fs::create_dir_all(&history_dir).expect("create history dir");

    let capture = run_bash(
        "scripts/perf/capture_snapshot.sh",
        &[
            "--tier",
            "quick",
            "--iters",
            "1",
            "--max-cases",
            "1",
            "--history-dir",
            history_dir.to_str().expect("utf8 path"),
            "--label",
            "smoke",
        ],
    );
    assert_success(&capture, "capture_snapshot.sh");

    let mut snapshots = Vec::new();
    for entry in fs::read_dir(&history_dir).expect("read history dir") {
        let entry = entry.expect("dir entry");
        if entry.path().is_dir() {
            snapshots.push(entry.path());
        }
    }
    assert_eq!(snapshots.len(), 1);
    let snapshot = &snapshots[0];
    assert!(snapshot.join("sanity.json").exists());
    assert!(snapshot.join("gate.json").exists());
    assert!(snapshot.join("probe.json").exists());
    assert!(snapshot.join("summary.md").exists());
    assert!(snapshot.join("perf_corpus_cases.toml").exists());

    let trend = run_bash(
        "scripts/perf/trend.sh",
        &[
            "--history-dir",
            history_dir.to_str().expect("utf8 path"),
            "--source",
            "all",
            "--metric",
            "all",
            "--json",
        ],
    );
    assert_success(&trend, "trend.sh");
    let trend_json = parse_stdout_json(&trend, "trend.sh json");
    assert_eq!(trend_json["snapshots_scanned"].as_u64(), Some(1));
}

#[test]
fn trend_gate_script_fails_on_regression_with_env_defaults() {
    let tmp = temp_dir("trend-gate");
    let history_dir = tmp.join("history");
    let s1 = history_dir.join("s1");
    let s2 = history_dir.join("s2");
    fs::create_dir_all(&s1).expect("create s1");
    fs::create_dir_all(&s2).expect("create s2");
    write_json(
        &s1.join("probe.json"),
        &json!({"rows":[{"id":"id1","median_us":10.0,"p95_us":12.0}]}),
    );
    write_json(
        &s2.join("probe.json"),
        &json!({"rows":[{"id":"id1","median_us":12.0,"p95_us":14.0}]}),
    );

    let out = run_bash_with_env(
        "scripts/perf/trend_gate.sh",
        &[],
        &[
            (
                "RWLOG_PERF_HISTORY_DIR",
                history_dir.to_str().expect("utf8 path"),
            ),
            ("RWLOG_TREND_SOURCE", "probe"),
            ("RWLOG_TREND_METRIC", "median"),
            ("RWLOG_TREND_WINDOW", "2"),
            ("RWLOG_TREND_TOP", "10"),
            ("RWLOG_TREND_REGRESSION_PCT", "10"),
        ],
    );
    assert_eq!(out.status.code(), Some(1));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("regressions over threshold"));
}

#[test]
fn trend_env_compat_mode_can_fail_on_mixed_environments() {
    let tmp = temp_dir("trend-env-compat");
    let history_dir = tmp.join("history");
    let s1 = history_dir.join("s1");
    let s2 = history_dir.join("s2");
    fs::create_dir_all(&s1).expect("create s1");
    fs::create_dir_all(&s2).expect("create s2");
    write_json(
        &s1.join("probe.json"),
        &json!({
            "environment":{"os":"linux","arch":"x86_64","cpu_model":"cpu-a","rustc_version":"rustc test"},
            "rows":[{"id":"id1","median_us":10.0,"p95_us":12.0}]
        }),
    );
    write_json(
        &s2.join("probe.json"),
        &json!({
            "environment":{"os":"linux","arch":"x86_64","cpu_model":"cpu-b","rustc_version":"rustc test"},
            "rows":[{"id":"id1","median_us":12.0,"p95_us":14.0}]
        }),
    );

    let fail = run_bin(
        "perf_corpus_trend",
        &[
            "--history-dir",
            history_dir.to_str().expect("utf8 path"),
            "--source",
            "probe",
            "--metric",
            "median",
            "--env-compat",
            "fail",
            "--json",
        ],
        &[],
    );
    assert_eq!(fail.status.code(), Some(2));

    let warn = run_bin(
        "perf_corpus_trend",
        &[
            "--history-dir",
            history_dir.to_str().expect("utf8 path"),
            "--source",
            "probe",
            "--metric",
            "median",
            "--env-compat",
            "warn",
            "--json",
        ],
        &[],
    );
    assert_success(&warn, "perf_corpus_trend --env-compat warn --json");
    let warn_json = parse_stdout_json(&warn, "trend env compat warn json");
    let mismatch_fields = warn_json["env_mismatch_fields"]
        .as_array()
        .expect("env_mismatch_fields array");
    assert!(mismatch_fields
        .iter()
        .any(|v| v.as_str() == Some("cpu_model")));
}

#[test]
fn prune_history_script_reports_and_applies_deletions() {
    let tmp = temp_dir("prune-history");
    let history_dir = tmp.join("history");
    fs::create_dir_all(&history_dir).expect("create history dir");

    let d1 = history_dir.join("20250101T000000Z_quick");
    let d2 = history_dir.join("20250102T000000Z_quick");
    let d3 = history_dir.join("20250103T000000Z_quick");
    fs::create_dir_all(&d1).expect("create d1");
    fs::create_dir_all(&d2).expect("create d2");
    fs::create_dir_all(&d3).expect("create d3");

    let dry_run = run_bash(
        "scripts/perf/prune_history.sh",
        &[
            "--history-dir",
            history_dir.to_str().expect("utf8 path"),
            "--keep-last",
            "2",
            "--json",
        ],
    );
    assert_success(&dry_run, "prune_history.sh dry-run");
    let dry_json = parse_stdout_json(&dry_run, "prune_history dry-run json");
    assert_eq!(dry_json["total_snapshots"].as_u64(), Some(3));
    assert_eq!(dry_json["delete_count"].as_u64(), Some(1));
    assert_eq!(dry_json["applied"].as_bool(), Some(false));
    assert!(dry_json["would_delete"]
        .as_array()
        .map(|a| a
            .iter()
            .any(|v| v.as_str() == Some("20250101T000000Z_quick")))
        .unwrap_or(false));
    assert!(d1.exists());

    let apply = run_bash(
        "scripts/perf/prune_history.sh",
        &[
            "--history-dir",
            history_dir.to_str().expect("utf8 path"),
            "--keep-last",
            "2",
            "--apply",
            "--json",
        ],
    );
    assert_success(&apply, "prune_history.sh apply");
    let apply_json = parse_stdout_json(&apply, "prune_history apply json");
    assert_eq!(apply_json["applied"].as_bool(), Some(true));
    assert_eq!(apply_json["delete_count"].as_u64(), Some(1));
    assert!(!d1.exists());
    assert!(d2.exists());
    assert!(d3.exists());
}

#[test]
fn perf_health_audit_reports_stale_noisy_and_redundant_patterns() {
    let tmp = temp_dir("perf-health");
    let history_dir = tmp.join("history");
    let s1 = history_dir.join("s1");
    let s2 = history_dir.join("s2");
    let s3 = history_dir.join("s3");
    fs::create_dir_all(&s1).expect("create s1");
    fs::create_dir_all(&s2).expect("create s2");
    fs::create_dir_all(&s3).expect("create s3");

    write_json(
        &s1.join("probe.json"),
        &json!({
            "rows":[
                {"id":"identity_atom","median_us":10.0,"p95_us":11.0},
                {"id":"sequence_chain_len12","median_us":10.0,"p95_us":11.0},
                {"id":"recursive_add_forward_n8","median_us":10.0,"p95_us":12.0}
            ]
        }),
    );
    write_json(
        &s2.join("probe.json"),
        &json!({
            "rows":[
                {"id":"identity_atom","median_us":11.0,"p95_us":12.0},
                {"id":"sequence_chain_len12","median_us":11.0,"p95_us":12.0},
                {"id":"recursive_add_forward_n8","median_us":40.0,"p95_us":45.0}
            ]
        }),
    );
    write_json(
        &s3.join("probe.json"),
        &json!({
            "rows":[
                {"id":"identity_atom","median_us":12.0,"p95_us":13.0},
                {"id":"sequence_chain_len12","median_us":12.0,"p95_us":13.0}
            ]
        }),
    );

    let out = run_bin(
        "perf_corpus_health",
        &[
            "--history-dir",
            history_dir.to_str().expect("utf8 path"),
            "--source",
            "probe",
            "--min-points",
            "3",
            "--noisy-cv-pct",
            "20",
            "--redundancy-corr-min",
            "0.99",
            "--json",
        ],
        &[],
    );
    assert_success(&out, "perf_corpus_health --json");
    let report = parse_stdout_json(&out, "perf_corpus_health json");
    assert_eq!(report["snapshots_scanned"].as_u64(), Some(3));
    assert!(report["stale_cases"]
        .as_array()
        .map(|a| a
            .iter()
            .any(|v| v["id"].as_str() == Some("recursive_add_forward_n8")))
        .unwrap_or(false));
    assert!(report["noisy_cases"]
        .as_array()
        .map(|a| a
            .iter()
            .any(|v| v["id"].as_str() == Some("recursive_add_forward_n8")))
        .unwrap_or(false));
    assert!(report["redundant_pairs"]
        .as_array()
        .map(|a| {
            a.iter().any(|v| {
                v["left_id"].as_str() == Some("identity_atom")
                    && v["right_id"].as_str() == Some("sequence_chain_len12")
            }) || a.iter().any(|v| {
                v["left_id"].as_str() == Some("sequence_chain_len12")
                    && v["right_id"].as_str() == Some("identity_atom")
            })
        })
        .unwrap_or(false));
}
