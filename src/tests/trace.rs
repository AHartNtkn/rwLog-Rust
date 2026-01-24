use super::*;

#[test]
fn trace_macros_compile() {
    // These should compile to no-ops without the tracing feature
    trace!("trace message");
    debug!("debug message");
    info!("info message");
    warn!("warn message");
    error!("error message");

    let _span = span!(Level::DEBUG, "test_span", value = 42);
    let _entered = debug_span!("entered_span").entered();
}

#[test]
fn init_subscriber_is_idempotent() {
    // Should not panic even when called multiple times
    init_subscriber();
    init_subscriber();
}
