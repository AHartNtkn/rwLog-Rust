mod common;

use common::process_helpers::*;
use serde::Deserialize;
use serde_json::json;
use serde_json::{Map, Value};
use std::collections::BTreeMap;
use std::fs;

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

fn assert_json_schema(
    bin_name: &str,
    args: &[&str],
    envs: &[(&str, &str)],
    fixture: &OutputSchemaFixture,
) {
    let output = run_bin(bin_name, args, envs);
    assert_success(&output, &format!("{bin_name} --json"));
    let json = parse_stdout_json(&output, &format!("{bin_name} json"));
    let schema = fixture
        .json
        .get(bin_name)
        .unwrap_or_else(|| panic!("{bin_name} schema fixture"));
    let obj = json
        .as_object()
        .unwrap_or_else(|| panic!("{bin_name} top object"));
    assert_has_keys(obj, &schema.top_keys, &format!("{bin_name} top"));
    let row = json["rows"][0]
        .as_object()
        .unwrap_or_else(|| panic!("{bin_name} first row"));
    assert_has_keys(row, &schema.row_keys, &format!("{bin_name} row"));
}

fn assert_csv_schema(
    bin_name: &str,
    args: &[&str],
    envs: &[(&str, &str)],
    fixture: &OutputSchemaFixture,
) {
    let output = run_bin(bin_name, args, envs);
    assert_success(&output, &format!("{bin_name} --csv"));
    assert_eq!(
        first_csv_header(&output, &format!("{bin_name} csv")),
        *fixture
            .csv_headers
            .get(bin_name)
            .unwrap_or_else(|| panic!("{bin_name} csv header fixture"))
    );
}

#[test]
fn perf_json_and_csv_outputs_match_schema_fixture() {
    let fixture = load_fixture();
    let quick_env: &[(&str, &str)] = &[("RWLOG_CORPUS_TIER", "quick")];
    let no_env: &[(&str, &str)] = &[];

    let sanity_args = &["--lint", "--validate", "--json"];
    let run_args = &[
        "--id",
        "identity_atom",
        "--iters",
        "1",
        "--phase",
        "execute",
        "--json",
    ];
    let alloc_args = &["--id", "identity_atom", "--iters", "1", "--json"];
    let gate_args = &["--json"];
    let recommend_args = &[
        "--samples",
        "1",
        "--warmup",
        "0",
        "--filter",
        "identity_atom",
        "--json",
    ];

    // JSON schema checks
    assert_json_schema("perf_corpus_sanity", sanity_args, quick_env, &fixture);
    assert_json_schema("perf_corpus_run", run_args, quick_env, &fixture);
    assert_json_schema("perf_corpus_alloc", alloc_args, quick_env, &fixture);
    assert_json_schema("perf_corpus_gate", gate_args, no_env, &fixture);
    assert_json_schema(
        "perf_corpus_recommend_gate",
        recommend_args,
        no_env,
        &fixture,
    );

    // Trend needs history data
    let history = temp_dir("schema-trend-history");
    create_probe_snapshots(
        &history,
        &[
            ("s1", json!({"rows":[{"id":"id1","median_us":10.0,"p95_us":12.0}]})),
            ("s2", json!({"rows":[{"id":"id1","median_us":12.0,"p95_us":14.0}]})),
        ],
    );
    let history_str = history.to_str().expect("utf8 path");
    let trend_args = &[
        "--history-dir",
        history_str,
        "--source",
        "probe",
        "--metric",
        "median",
        "--json",
    ];
    assert_json_schema("perf_corpus_trend", trend_args, no_env, &fixture);

    // CSV schema checks (replace --json with --csv in args)
    let sanity_csv_args = &["--lint", "--validate", "--csv"];
    let run_csv_args = &[
        "--id",
        "identity_atom",
        "--iters",
        "1",
        "--phase",
        "execute",
        "--csv",
    ];
    let alloc_csv_args = &["--id", "identity_atom", "--iters", "1", "--csv"];
    let gate_csv_args = &["--csv"];
    let recommend_csv_args = &[
        "--samples",
        "1",
        "--warmup",
        "0",
        "--filter",
        "identity_atom",
        "--csv",
    ];
    let trend_csv_args = &[
        "--history-dir",
        history_str,
        "--source",
        "probe",
        "--metric",
        "median",
        "--csv",
    ];

    assert_csv_schema("perf_corpus_sanity", sanity_csv_args, quick_env, &fixture);
    assert_csv_schema("perf_corpus_run", run_csv_args, quick_env, &fixture);
    assert_csv_schema("perf_corpus_alloc", alloc_csv_args, quick_env, &fixture);
    assert_csv_schema("perf_corpus_gate", gate_csv_args, no_env, &fixture);
    assert_csv_schema(
        "perf_corpus_recommend_gate",
        recommend_csv_args,
        no_env,
        &fixture,
    );
    assert_csv_schema("perf_corpus_trend", trend_csv_args, no_env, &fixture);
}
