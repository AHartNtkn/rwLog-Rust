use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_TMP_ID: AtomicU64 = AtomicU64::new(0);
const MANIFEST_PATH: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml");
const EXE_SUFFIX: &str = std::env::consts::EXE_SUFFIX;

pub fn bin_path(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug")
        .join(format!("{name}{EXE_SUFFIX}"))
}

pub fn run_bin(name: &str, args: &[&str], envs: &[(&str, &str)]) -> Output {
    run_bin_impl(name, args, envs, None)
}

pub fn run_bin_in_dir(name: &str, args: &[&str], cwd: &Path) -> Output {
    run_bin_impl(name, args, &[], Some(cwd))
}

fn run_bin_impl(name: &str, args: &[&str], envs: &[(&str, &str)], cwd: Option<&Path>) -> Output {
    let path = bin_path(name);
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
    if let Some(dir) = cwd {
        cmd.current_dir(dir);
    }
    let context = if let Some(dir) = cwd {
        format!("'{name}' in {}", dir.display())
    } else {
        format!("'{name}'")
    };
    cmd.output()
        .unwrap_or_else(|e| panic!("failed to run binary {context}: {e}"))
}

pub fn run_bash(script_path: &str, args: &[&str]) -> Output {
    run_bash_with_env(script_path, args, &[])
}

pub fn run_bash_with_env(script_path: &str, args: &[&str], envs: &[(&str, &str)]) -> Output {
    let mut cmd = Command::new("bash");
    cmd.arg(script_path).args(args);
    for (k, v) in envs {
        cmd.env(k, v);
    }
    cmd.output()
        .unwrap_or_else(|e| panic!("failed to run script '{script_path}': {e}"))
}

pub fn assert_success(output: &Output, context: &str) {
    if !output.status.success() {
        panic!(
            "{context} failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

pub fn parse_stdout_json(output: &Output, context: &str) -> Value {
    serde_json::from_slice::<Value>(&output.stdout).unwrap_or_else(|e| {
        panic!(
            "{context}: failed to parse stdout as JSON: {e}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

pub fn first_csv_header(output: &Output, context: &str) -> Vec<String> {
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

pub fn temp_dir(prefix: &str) -> PathBuf {
    let mut p = std::env::temp_dir();
    let id = NEXT_TMP_ID.fetch_add(1, Ordering::Relaxed);
    p.push(format!("rwlog-{prefix}-{}-{}", std::process::id(), id));
    fs::create_dir_all(&p).expect("create temp dir");
    p
}

pub fn write_json(path: &Path, value: &Value) {
    fs::write(
        path,
        serde_json::to_vec_pretty(value).expect("serialize json"),
    )
    .expect("write json");
}
