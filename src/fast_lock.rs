//! Zero-cost lock for single-threaded execution.
//!
//! Replaces `parking_lot::Mutex` with a no-op wrapper when the evaluator
//! is known to be single-threaded. This eliminates the overhead of atomic
//! compare-and-swap operations on every lock/unlock cycle.
//!
//! SAFETY: This is only correct when the evaluator is single-threaded.
//! The `unsafe impl Sync` allows `FastLock<T>` inside `Arc`, but concurrent
//! mutable access from multiple threads would be undefined behavior.

use std::cell::UnsafeCell;
use std::ops::{Deref, DerefMut};

/// A zero-cost "mutex" for single-threaded use.
///
/// Has the same API as `parking_lot::Mutex<T>` but performs no atomic
/// operations. Lock/unlock is a no-op.
pub struct FastLock<T>(UnsafeCell<T>);

// SAFETY: The rwlog evaluator is single-threaded. No concurrent access occurs.
// If parallel evaluation is added, this must be replaced with a real Mutex.
unsafe impl<T: Send> Sync for FastLock<T> {}
unsafe impl<T: Send> Send for FastLock<T> {}

impl<T: std::fmt::Debug> std::fmt::Debug for FastLock<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // SAFETY: single-threaded, no concurrent access
        let inner = unsafe { &*self.0.get() };
        f.debug_tuple("FastLock").field(inner).finish()
    }
}

/// Guard returned by `FastLock::lock()`.
///
/// Mirrors `parking_lot::MutexGuard` — derefs to `&T` / `&mut T`.
pub struct FastLockGuard<'a, T>(&'a mut T);

impl<T> Deref for FastLockGuard<'_, T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        self.0
    }
}

impl<T> DerefMut for FastLockGuard<'_, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        self.0
    }
}

impl<T> Drop for FastLockGuard<'_, T> {
    #[inline(always)]
    fn drop(&mut self) {}
}

impl<T> FastLock<T> {
    /// Create a new FastLock wrapping `val`.
    #[inline(always)]
    pub fn new(val: T) -> Self {
        Self(UnsafeCell::new(val))
    }

    /// "Lock" the value (no-op in single-threaded mode).
    #[inline(always)]
    pub fn lock(&self) -> FastLockGuard<'_, T> {
        // SAFETY: single-threaded evaluator — no concurrent access
        unsafe { FastLockGuard(&mut *self.0.get()) }
    }

    /// Try-lock (always succeeds in single-threaded mode).
    #[inline(always)]
    pub fn try_lock(&self) -> Option<FastLockGuard<'_, T>> {
        Some(self.lock())
    }
}
