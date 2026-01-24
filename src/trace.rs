//! Feature-gated tracing macros for zero-overhead instrumentation.
//!
//! When the `tracing` feature is enabled, this module re-exports the tracing crate's
//! macros. When disabled, all macros compile to no-ops with zero overhead.
//!
//! # Usage
//!
//! ```rust,ignore
//! use crate::trace::{debug, trace, info, span, Level};
//!
//! fn my_function() {
//!     let _span = span!(Level::DEBUG, "my_function", arg = 42).entered();
//!     trace!("doing work");
//!     debug!(result = ?value, "completed");
//! }
//! ```

// When tracing feature is enabled, re-export from tracing crate
#[cfg(feature = "tracing")]
pub use tracing::{
    debug, debug_span, error, error_span, event, info, info_span, instrument, span, trace,
    trace_span, warn, warn_span, Level, Span,
};

// When tracing feature is disabled, provide no-op implementations
#[cfg(not(feature = "tracing"))]
mod noop {
    /// No-op span that does nothing
    pub struct Span;

    impl Span {
        pub fn none() -> Self {
            Span
        }

        pub fn entered(self) -> SpanGuard {
            SpanGuard
        }

        pub fn enter(&self) -> SpanGuard {
            SpanGuard
        }
    }

    /// No-op guard that implements Drop
    pub struct SpanGuard;

    impl Drop for SpanGuard {
        fn drop(&mut self) {}
    }

    /// Tracing levels (no-op)
    #[derive(Clone, Copy, Debug)]
    pub struct Level;

    impl Level {
        pub const TRACE: Level = Level;
        pub const DEBUG: Level = Level;
        pub const INFO: Level = Level;
        pub const WARN: Level = Level;
        pub const ERROR: Level = Level;
    }

    /// No-op trace macro
    #[macro_export]
    macro_rules! trace {
        ($($tt:tt)*) => {};
    }

    /// No-op debug macro
    #[macro_export]
    macro_rules! debug {
        ($($tt:tt)*) => {};
    }

    /// No-op info macro
    #[macro_export]
    macro_rules! info {
        ($($tt:tt)*) => {};
    }

    /// No-op warn macro
    #[macro_export]
    macro_rules! warn {
        ($($tt:tt)*) => {};
    }

    /// No-op error macro
    #[macro_export]
    macro_rules! error {
        ($($tt:tt)*) => {};
    }

    /// No-op event macro
    #[macro_export]
    macro_rules! event {
        ($($tt:tt)*) => {};
    }

    /// No-op span macro
    #[macro_export]
    macro_rules! span {
        ($($tt:tt)*) => {
            $crate::trace::Span::none()
        };
    }

    /// No-op trace_span macro
    #[macro_export]
    macro_rules! trace_span {
        ($($tt:tt)*) => {
            $crate::trace::Span::none()
        };
    }

    /// No-op debug_span macro
    #[macro_export]
    macro_rules! debug_span {
        ($($tt:tt)*) => {
            $crate::trace::Span::none()
        };
    }

    /// No-op info_span macro
    #[macro_export]
    macro_rules! info_span {
        ($($tt:tt)*) => {
            $crate::trace::Span::none()
        };
    }

    /// No-op warn_span macro
    #[macro_export]
    macro_rules! warn_span {
        ($($tt:tt)*) => {
            $crate::trace::Span::none()
        };
    }

    /// No-op error_span macro
    #[macro_export]
    macro_rules! error_span {
        ($($tt:tt)*) => {
            $crate::trace::Span::none()
        };
    }

    /// No-op instrument attribute (identity function)
    pub use core::convert::identity as instrument;

    // Re-export macros at module level
    pub use crate::{
        debug, debug_span, error, error_span, event, info, info_span, span, trace, trace_span,
        warn, warn_span,
    };
}

#[cfg(not(feature = "tracing"))]
pub use noop::*;

/// Initialize tracing subscriber for tests/development.
///
/// This function should be called once at the start of a test or application
/// when tracing is enabled.
#[cfg(feature = "tracing")]
pub fn init_subscriber() {
    use tracing_subscriber::{fmt, prelude::*, EnvFilter};

    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));

    tracing_subscriber::registry()
        .with(
            fmt::layer()
                .with_writer(std::io::stderr)
                .with_target(true)
                .with_level(true)
                .with_ansi(false),
        )
        .with(filter)
        .try_init()
        .ok(); // Ignore error if already initialized
}

#[cfg(not(feature = "tracing"))]
pub fn init_subscriber() {
    // No-op when tracing is disabled
}

/// Initialize flamegraph-compatible tracing.
///
/// Returns a guard that must be held until tracing is complete.
/// When the guard is dropped, the folded stack trace is written to the file.
#[cfg(feature = "tracing")]
pub fn init_flamegraph(path: &str) -> impl Drop {
    use tracing_flame::FlameLayer;
    use tracing_subscriber::{prelude::*, registry::Registry};

    let (flame_layer, guard) = FlameLayer::with_file(path).expect("Failed to create flame layer");

    Registry::default().with(flame_layer).init();

    guard
}

#[cfg(not(feature = "tracing"))]
pub fn init_flamegraph(_path: &str) -> impl Drop {
    // Return a dummy guard
    struct DummyGuard;
    impl Drop for DummyGuard {
        fn drop(&mut self) {}
    }
    DummyGuard
}


#[cfg(test)]
#[path = "tests/trace.rs"]
mod tests;
