use super::*;

#[test]
fn metrics_report_default() {
    let report = MetricsReport::default();
    assert_eq!(report.steps, 0);
    assert_eq!(report.compositions, 0);
}

#[test]
fn metrics_report_success_rates() {
    let mut report = MetricsReport::default();

    // No operations = 100% success
    assert_eq!(report.composition_success_rate(), 1.0);

    // 3 success, 1 failure = 75%
    report.compositions = 3;
    report.composition_failures = 1;
    assert!((report.composition_success_rate() - 0.75).abs() < 0.001);
}

#[test]
fn metrics_report_display() {
    let report = MetricsReport {
        steps: 100,
        compositions: 50,
        composition_failures: 10,
        ..Default::default()
    };

    let output = format!("{}", report);
    assert!(output.contains("Steps:"));
    assert!(output.contains("100"));
    assert!(output.contains("Compositions:"));
}

#[cfg(feature = "tracing")]
#[test]
fn eval_metrics_basic_operations() {
    let metrics = EvalMetrics::new();

    metrics.record_step();
    metrics.record_step();
    metrics.record_composition();
    metrics.record_backtrack();

    let report = metrics.report();
    assert_eq!(report.steps, 2);
    assert_eq!(report.compositions, 1);
    assert_eq!(report.backtracks, 1);
}

#[cfg(feature = "tracing")]
#[test]
fn eval_metrics_max_depth_tracking() {
    let metrics = EvalMetrics::new();

    metrics.update_max_kont_depth(5);
    assert_eq!(metrics.max_kont_depth.load(Ordering::Relaxed), 5);

    metrics.update_max_kont_depth(3); // Should not update
    assert_eq!(metrics.max_kont_depth.load(Ordering::Relaxed), 5);

    metrics.update_max_kont_depth(10); // Should update
    assert_eq!(metrics.max_kont_depth.load(Ordering::Relaxed), 10);
}

#[cfg(feature = "tracing")]
#[test]
fn eval_metrics_reset() {
    let metrics = EvalMetrics::new();

    metrics.record_step();
    metrics.record_composition();
    assert_eq!(metrics.steps.load(Ordering::Relaxed), 1);

    metrics.reset();
    assert_eq!(metrics.steps.load(Ordering::Relaxed), 0);
    assert_eq!(metrics.compositions.load(Ordering::Relaxed), 0);
}

#[test]
fn noop_metrics_compile() {
    // This test verifies the no-op implementation compiles and runs
    let metrics = EvalMetrics::new();
    metrics.record_step();
    metrics.record_composition();
    let _ = metrics.report();
}
