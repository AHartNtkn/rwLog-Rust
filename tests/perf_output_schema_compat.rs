use serde::Deserialize;
use serde_json::json;
use serde_json::Map;
use serde_json::Value;
use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const MANIFEST_PATH: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml");
const EXE_SUFFIX: &str = std::env::consts::EXE_SUFFIX;
static NEXT_TMP_ID: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Deserialize)]
struct ToolJsonSchema {
    top_keys: Vec<String>,
    row_keys: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct OutputSchemaFixture {
    json: BTreeMap<String, ToolJsonSchema>,
    csv_headers: BTreeMap<String, Vec<String>>,
}

fn temp_dir(prefix: &str) -> PathBuf {
    let mut p = std::env::temp_dir();
    let id = NEXT_TMP_ID.fetch_add(1, Ordering::Relaxed);
    p.push(format!("rwlog-{prefix}-{}-{}", std::process::id(), id));
    fs::create_dir_all(&p).expect("create temp dir");
    p
}

fn run_bin(name: &str, args: &[&str], envs: &[(&str, &str)]) -> Output {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug")
        .join(format!("{name}{EXE_SUFFIX}"));
    let mut cmd = if path.exists() {
        Command::new(path)
    } else {
        let mut fallback = Command::new("cargo");
        fallback
            .arg("run")
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

fn parse_stdout_json(output: &Output, context: &str) -> Value {
    serde_json::from_slice::<Value>(&output.stdout).unwrap_or_else(|e| {
        panic!(
            "{context}: failed to parse stdout as JSON: {e}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

fn first_csv_header(output: &Output, context: &str) -> Vec<String> {
    let text = String::from_utf8(output.stdout.clone()).unwrap_or_else(|e| {
        panic!(
            "{context}: stdout is not utf-8: {e}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stderr)
        )
    });
    let header = text
        .lines()
        .next()
        .unwrap_or_else(|| panic!("{context}: missing csv header line"));
    header.split(',').map(|s| s.to_string()).collect()
}

fn assert_has_keys(obj: &Map<String, Value>, keys: &[String], context: &str) {
    for key in keys {
        assert!(
            obj.contains_key(key),
            "{context}: missing expected key '{key}'"
        );
    }
}

fn load_fixture() -> OutputSchemaFixture {
    let text = fs::read_to_string("tests/fixtures/perf_output_schema.json")
        .expect("read tests/fixtures/perf_output_schema.json");
    serde_json::from_str(&text).expect("parse perf output schema fixture")
}

#[test]
fn perf_json_and_csv_outputs_match_schema_fixture() {
    let fixture = load_fixture();

    let quick_env = [("RWLOG_CORPUS_TIER", "quick")];

    let sanity_json_out = run_bin(
        "perf_corpus_sanity",
        &["--lint", "--validate", "--json"],
        &quick_env,
    );
    assert_success(&sanity_json_out, "perf_corpus_sanity --json");
    let sanity_json = parse_stdout_json(&sanity_json_out, "sanity json");
    let sanity_schema = fixture
        .json
        .get("perf_corpus_sanity")
        .expect("sanity schema fixture");
    let sanity_obj = sanity_json.as_object().expect("sanity top object");
    assert_has_keys(sanity_obj, &sanity_schema.top_keys, "sanity top");
    let sanity_row = sanity_json["rows"][0]
        .as_object()
        .expect("sanity first row");
    assert_has_keys(sanity_row, &sanity_schema.row_keys, "sanity row");

    let run_json_out = run_bin(
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
    assert_success(&run_json_out, "perf_corpus_run --json");
    let run_json = parse_stdout_json(&run_json_out, "run json");
    let run_schema = fixture
        .json
        .get("perf_corpus_run")
        .expect("run schema fixture");
    let run_obj = run_json.as_object().expect("run top object");
    assert_has_keys(run_obj, &run_schema.top_keys, "run top");
    let run_row = run_json["rows"][0].as_object().expect("run first row");
    assert_has_keys(run_row, &run_schema.row_keys, "run row");

    let alloc_json_out = run_bin(
        "perf_corpus_alloc",
        &["--id", "identity_atom", "--iters", "1", "--json"],
        &quick_env,
    );
    assert_success(&alloc_json_out, "perf_corpus_alloc --json");
    let alloc_json = parse_stdout_json(&alloc_json_out, "alloc json");
    let alloc_schema = fixture
        .json
        .get("perf_corpus_alloc")
        .expect("alloc schema fixture");
    let alloc_obj = alloc_json.as_object().expect("alloc top object");
    assert_has_keys(alloc_obj, &alloc_schema.top_keys, "alloc top");
    let alloc_row = alloc_json["rows"][0].as_object().expect("alloc first row");
    assert_has_keys(alloc_row, &alloc_schema.row_keys, "alloc row");

    let gate_json_out = run_bin("perf_corpus_gate", &["--json"], &[]);
    assert_success(&gate_json_out, "perf_corpus_gate --json");
    let gate_json = parse_stdout_json(&gate_json_out, "gate json");
    let gate_schema = fixture
        .json
        .get("perf_corpus_gate")
        .expect("gate schema fixture");
    let gate_obj = gate_json.as_object().expect("gate top object");
    assert_has_keys(gate_obj, &gate_schema.top_keys, "gate top");
    let gate_row = gate_json["rows"][0].as_object().expect("gate first row");
    assert_has_keys(gate_row, &gate_schema.row_keys, "gate row");

    let recommend_json_out = run_bin(
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
    assert_success(&recommend_json_out, "perf_corpus_recommend_gate --json");
    let recommend_json = parse_stdout_json(&recommend_json_out, "recommend json");
    let recommend_schema = fixture
        .json
        .get("perf_corpus_recommend_gate")
        .expect("recommend schema fixture");
    let recommend_obj = recommend_json.as_object().expect("recommend top object");
    assert_has_keys(recommend_obj, &recommend_schema.top_keys, "recommend top");
    let recommend_row = recommend_json["rows"][0]
        .as_object()
        .expect("recommend first row");
    assert_has_keys(recommend_row, &recommend_schema.row_keys, "recommend row");

    let history = temp_dir("schema-trend-history");
    let s1 = history.join("s1");
    let s2 = history.join("s2");
    fs::create_dir_all(&s1).expect("create s1");
    fs::create_dir_all(&s2).expect("create s2");
    fs::write(
        s1.join("probe.json"),
        serde_json::to_vec_pretty(&json!({"rows":[{"id":"id1","median_us":10.0,"p95_us":12.0}]}))
            .expect("serialize probe s1"),
    )
    .expect("write probe s1");
    fs::write(
        s2.join("probe.json"),
        serde_json::to_vec_pretty(&json!({"rows":[{"id":"id1","median_us":12.0,"p95_us":14.0}]}))
            .expect("serialize probe s2"),
    )
    .expect("write probe s2");

    let trend_json_out = run_bin(
        "perf_corpus_trend",
        &[
            "--history-dir",
            history.to_str().expect("utf8 path"),
            "--source",
            "probe",
            "--metric",
            "median",
            "--json",
        ],
        &[],
    );
    assert_success(&trend_json_out, "perf_corpus_trend --json");
    let trend_json = parse_stdout_json(&trend_json_out, "trend json");
    let trend_schema = fixture
        .json
        .get("perf_corpus_trend")
        .expect("trend schema fixture");
    let trend_obj = trend_json.as_object().expect("trend top object");
    assert_has_keys(trend_obj, &trend_schema.top_keys, "trend top");
    let trend_row = trend_json["rows"][0].as_object().expect("trend first row");
    assert_has_keys(trend_row, &trend_schema.row_keys, "trend row");

    let sanity_csv_out = run_bin("perf_corpus_sanity", &["--csv"], &quick_env);
    assert_success(&sanity_csv_out, "perf_corpus_sanity --csv");
    assert_eq!(
        first_csv_header(&sanity_csv_out, "sanity csv"),
        *fixture
            .csv_headers
            .get("perf_corpus_sanity")
            .expect("sanity csv header fixture")
    );

    let run_csv_out = run_bin(
        "perf_corpus_run",
        &[
            "--id",
            "identity_atom",
            "--iters",
            "1",
            "--phase",
            "execute",
            "--csv",
        ],
        &quick_env,
    );
    assert_success(&run_csv_out, "perf_corpus_run --csv");
    assert_eq!(
        first_csv_header(&run_csv_out, "run csv"),
        *fixture
            .csv_headers
            .get("perf_corpus_run")
            .expect("run csv header fixture")
    );

    let alloc_csv_out = run_bin(
        "perf_corpus_alloc",
        &["--id", "identity_atom", "--iters", "1", "--csv"],
        &quick_env,
    );
    assert_success(&alloc_csv_out, "perf_corpus_alloc --csv");
    assert_eq!(
        first_csv_header(&alloc_csv_out, "alloc csv"),
        *fixture
            .csv_headers
            .get("perf_corpus_alloc")
            .expect("alloc csv header fixture")
    );

    let gate_csv_out = run_bin("perf_corpus_gate", &["--csv"], &[]);
    assert_success(&gate_csv_out, "perf_corpus_gate --csv");
    assert_eq!(
        first_csv_header(&gate_csv_out, "gate csv"),
        *fixture
            .csv_headers
            .get("perf_corpus_gate")
            .expect("gate csv header fixture")
    );

    let recommend_csv_out = run_bin(
        "perf_corpus_recommend_gate",
        &[
            "--samples",
            "1",
            "--warmup",
            "0",
            "--filter",
            "identity_atom",
            "--csv",
        ],
        &[],
    );
    assert_success(&recommend_csv_out, "perf_corpus_recommend_gate --csv");
    assert_eq!(
        first_csv_header(&recommend_csv_out, "recommend csv"),
        *fixture
            .csv_headers
            .get("perf_corpus_recommend_gate")
            .expect("recommend csv header fixture")
    );

    let trend_csv_out = run_bin(
        "perf_corpus_trend",
        &[
            "--history-dir",
            history.to_str().expect("utf8 path"),
            "--source",
            "probe",
            "--metric",
            "median",
            "--csv",
        ],
        &[],
    );
    assert_success(&trend_csv_out, "perf_corpus_trend --csv");
    assert_eq!(
        first_csv_header(&trend_csv_out, "trend csv"),
        *fixture
            .csv_headers
            .get("perf_corpus_trend")
            .expect("trend csv header fixture")
    );
}
