//! Factors - A rope-of-slices for efficient deque operations on Rel sequences.
//!
//! This data structure allows O(1) push/pop from both ends without copying,
//! by maintaining a list of slices into Arc-backed arrays.

use crate::rel::Rel;
use smallvec::SmallVec;
use std::sync::Arc;

/// A slice into an Arc-backed array of Rel elements.
///
/// Represents a contiguous sub-range [start, end) of the underlying array.
#[derive(Clone, Debug)]
pub struct Slice<C> {
    /// The underlying shared array.
    arc: Arc<[Arc<Rel<C>>]>,
    /// Start index (inclusive).
    start: usize,
    /// End index (exclusive).
    end: usize,
}

impl<C> Slice<C> {
    /// Create a new Slice covering the entire array.
    pub fn new(arc: Arc<[Arc<Rel<C>>]>) -> Self {
        let end = arc.len();
        Self { arc, start: 0, end }
    }

    /// Create a Slice with a specific range.
    pub fn with_range(arc: Arc<[Arc<Rel<C>>]>, start: usize, end: usize) -> Self {
        debug_assert!(start <= end);
        debug_assert!(end <= arc.len());
        Self { arc, start, end }
    }

    /// Check if this slice is empty.
    pub fn is_empty(&self) -> bool {
        self.start >= self.end
    }

    /// Get the number of elements in this slice.
    pub fn len(&self) -> usize {
        self.end.saturating_sub(self.start)
    }

    /// Get the first element, if any.
    pub fn front(&self) -> Option<&Arc<Rel<C>>> {
        if self.is_empty() {
            None
        } else {
            Some(&self.arc[self.start])
        }
    }

    /// Get the last element, if any.
    pub fn back(&self) -> Option<&Arc<Rel<C>>> {
        if self.is_empty() {
            None
        } else {
            Some(&self.arc[self.end - 1])
        }
    }

    /// Pop the first element from this slice.
    fn pop_front(&mut self) -> Option<Arc<Rel<C>>> {
        if self.is_empty() {
            None
        } else {
            let elem = Arc::clone(&self.arc[self.start]);
            self.start += 1;
            Some(elem)
        }
    }

    /// Pop the last element from this slice.
    fn pop_back(&mut self) -> Option<Arc<Rel<C>>> {
        if self.is_empty() {
            None
        } else {
            self.end -= 1;
            Some(Arc::clone(&self.arc[self.end]))
        }
    }
}

/// A rope-of-slices for efficient deque operations on Rel sequences.
///
/// Maintains a list of slices, allowing O(1) push/pop from both ends.
/// Empty slices are automatically filtered out to maintain the invariant
/// that all slices in `chunks` are non-empty (or `chunks` is empty).
#[derive(Clone, Debug)]
pub struct Factors<C> {
    /// The list of slices. Invariant: all slices are non-empty.
    chunks: SmallVec<[Slice<C>; 4]>,
}

impl<C> Factors<C> {
    /// Create a new empty Factors.
    pub fn new() -> Self {
        Self {
            chunks: SmallVec::new(),
        }
    }

    /// Create Factors from a sequence (single slice).
    pub fn from_seq(seq: Arc<[Arc<Rel<C>>]>) -> Self {
        let slice = Slice::new(seq);
        if slice.is_empty() {
            Self::new()
        } else {
            let mut chunks = SmallVec::new();
            chunks.push(slice);
            Self { chunks }
        }
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.chunks.is_empty()
    }

    /// Get the total number of elements across all slices.
    pub fn len(&self) -> usize {
        self.chunks.iter().map(|s| s.len()).sum()
    }

    /// Collect all elements into a Vec in order.
    pub fn to_vec(&self) -> Vec<Arc<Rel<C>>> {
        let mut out = Vec::new();
        for slice in &self.chunks {
            for idx in slice.start..slice.end {
                out.push(Arc::clone(&slice.arc[idx]));
            }
        }
        out
    }

    /// Get the first element, if any.
    pub fn front(&self) -> Option<&Arc<Rel<C>>> {
        self.chunks.first().and_then(|s| s.front())
    }

    /// Get the last element, if any.
    pub fn back(&self) -> Option<&Arc<Rel<C>>> {
        self.chunks.last().and_then(|s| s.back())
    }

    /// Pop the first element.
    pub fn pop_front(&mut self) -> Option<Arc<Rel<C>>> {
        if self.chunks.is_empty() {
            return None;
        }

        let elem = self.chunks[0].pop_front();

        // Remove slice if it became empty
        if self.chunks[0].is_empty() {
            self.chunks.remove(0);
        }

        elem
    }

    /// Pop the last element.
    pub fn pop_back(&mut self) -> Option<Arc<Rel<C>>> {
        if self.chunks.is_empty() {
            return None;
        }

        let last_idx = self.chunks.len() - 1;
        let elem = self.chunks[last_idx].pop_back();

        // Remove slice if it became empty
        if self.chunks[last_idx].is_empty() {
            self.chunks.pop();
        }

        elem
    }

    /// Push a slice to the front. Empty slices are ignored.
    pub fn push_front_slice(&mut self, slice: Slice<C>) {
        if !slice.is_empty() {
            self.chunks.insert(0, slice);
        }
    }

    /// Push a slice to the back. Empty slices are ignored.
    pub fn push_back_slice(&mut self, slice: Slice<C>) {
        if !slice.is_empty() {
            self.chunks.push(slice);
        }
    }

    /// Push a single Rel to the front.
    pub fn push_front_rel(&mut self, rel: Arc<Rel<C>>) {
        let arr: Arc<[Arc<Rel<C>>]> = Arc::from(vec![rel]);
        self.push_front_slice(Slice::new(arr));
    }

    /// Push a single Rel to the back.
    pub fn push_back_rel(&mut self, rel: Arc<Rel<C>>) {
        let arr: Arc<[Arc<Rel<C>>]> = Arc::from(vec![rel]);
        self.push_back_slice(Slice::new(arr));
    }

    /// Push a Seq's contents to the front as a slice.
    pub fn push_front_slice_from_seq(&mut self, seq: Arc<[Arc<Rel<C>>]>) {
        self.push_front_slice(Slice::new(seq));
    }

    /// Push a Seq's contents to the back as a slice.
    pub fn push_back_slice_from_seq(&mut self, seq: Arc<[Arc<Rel<C>>]>) {
        self.push_back_slice(Slice::new(seq));
    }
}

impl<C> Default for Factors<C> {
    fn default() -> Self {
        Self::new()
    }
}


#[cfg(test)]
mod tests;
