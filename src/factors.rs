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
        if self.start >= self.end {
            0
        } else {
            self.end - self.start
        }
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
mod tests {
    use super::{Factors, Slice};
    use crate::rel::Rel;
    use std::sync::Arc;

    // Helper to create a Rel::Zero
    fn make_rel() -> Arc<Rel<()>> {
        Arc::new(Rel::Zero)
    }

    // Helper to create an Arc slice with n elements
    fn make_arc_slice(n: usize) -> Arc<[Arc<Rel<()>>]> {
        let elements: Vec<Arc<Rel<()>>> = (0..n).map(|_| make_rel()).collect();
        Arc::from(elements)
    }

    // Helper to create a Slice with n elements
    fn slice_with_n_elements(n: usize) -> Slice<()> {
        let arc = make_arc_slice(n);
        Slice::new(arc)
    }

    // Helper to create an empty slice
    fn empty_slice() -> Slice<()> {
        let arc = make_arc_slice(0);
        Slice::new(arc)
    }

    // Helper to create Factors with a single slice containing n elements
    fn factors_with_single_slice(n: usize) -> Factors<()> {
        let mut f = Factors::new();
        if n > 0 {
            f.push_back_slice(slice_with_n_elements(n));
        }
        f
    }

    // Helper to create Factors with multiple slices of given sizes
    fn factors_with_slices(sizes: Vec<usize>) -> Factors<()> {
        let mut f = Factors::new();
        for size in sizes {
            if size > 0 {
                f.push_back_slice(slice_with_n_elements(size));
            }
        }
        f
    }

    // ========================================================================
    // SLICE TESTS
    // ========================================================================

    #[test]
    fn slice_new_creates_full_range() {
        let arc = make_arc_slice(5);
        let slice = Slice::new(arc);
        assert_eq!(slice.len(), 5);
        assert!(!slice.is_empty());
    }

    #[test]
    fn slice_empty_is_empty() {
        let arc = make_arc_slice(0);
        let slice = Slice::new(arc);
        assert!(slice.is_empty());
        assert_eq!(slice.len(), 0);
    }

    #[test]
    fn slice_with_range_respects_bounds() {
        let arc = make_arc_slice(5);
        let slice = Slice::with_range(arc, 1, 4);
        assert_eq!(slice.len(), 3);
    }

    #[test]
    fn slice_with_range_start_equals_end_is_empty() {
        let arc = make_arc_slice(5);
        let slice = Slice::with_range(arc, 2, 2);
        assert!(slice.is_empty());
        assert_eq!(slice.len(), 0);
    }

    #[test]
    fn slice_front_returns_element_at_start() {
        let arc = make_arc_slice(3);
        let expected = Arc::clone(&arc[1]);
        let slice = Slice::with_range(arc, 1, 3);
        assert!(Arc::ptr_eq(slice.front().unwrap(), &expected));
    }

    #[test]
    fn slice_back_returns_element_at_end_minus_one() {
        let arc = make_arc_slice(3);
        let expected = Arc::clone(&arc[1]);
        let slice = Slice::with_range(arc, 0, 2);
        assert!(Arc::ptr_eq(slice.back().unwrap(), &expected));
    }

    #[test]
    fn slice_front_empty_returns_none() {
        let slice = empty_slice();
        assert!(slice.front().is_none());
    }

    #[test]
    fn slice_back_empty_returns_none() {
        let slice = empty_slice();
        assert!(slice.back().is_none());
    }

    // ========================================================================
    // EMPTY FACTORS TESTS
    // ========================================================================

    #[test]
    fn empty_factors_is_empty() {
        let f: Factors<()> = Factors::new();
        assert!(f.is_empty());
        assert_eq!(f.len(), 0);
    }

    #[test]
    fn empty_factors_front_returns_none() {
        let f: Factors<()> = Factors::new();
        assert!(f.front().is_none());
    }

    #[test]
    fn empty_factors_back_returns_none() {
        let f: Factors<()> = Factors::new();
        assert!(f.back().is_none());
    }

    #[test]
    fn empty_factors_pop_front_returns_none() {
        let mut f: Factors<()> = Factors::new();
        assert!(f.pop_front().is_none());
        assert!(f.is_empty());
    }

    #[test]
    fn empty_factors_pop_back_returns_none() {
        let mut f: Factors<()> = Factors::new();
        assert!(f.pop_back().is_none());
        assert!(f.is_empty());
    }

    // ========================================================================
    // SINGLE-ELEMENT FACTORS TESTS
    // ========================================================================

    #[test]
    fn single_element_len_is_one() {
        let f = factors_with_single_slice(1);
        assert_eq!(f.len(), 1);
        assert!(!f.is_empty());
    }

    #[test]
    fn single_element_front_and_back_same() {
        let f = factors_with_single_slice(1);
        assert!(Arc::ptr_eq(f.front().unwrap(), f.back().unwrap()));
    }

    #[test]
    fn single_element_pop_front_empties() {
        let mut f = factors_with_single_slice(1);
        let elem = f.pop_front();
        assert!(elem.is_some());
        assert!(f.is_empty());
        assert_eq!(f.len(), 0);
    }

    #[test]
    fn single_element_pop_back_empties() {
        let mut f = factors_with_single_slice(1);
        let elem = f.pop_back();
        assert!(elem.is_some());
        assert!(f.is_empty());
        assert_eq!(f.len(), 0);
    }

    #[test]
    fn single_element_pop_front_then_front_is_none() {
        let mut f = factors_with_single_slice(1);
        f.pop_front();
        assert!(f.front().is_none());
        assert!(f.back().is_none());
    }

    // ========================================================================
    // SLICE EXHAUSTION TESTS
    // ========================================================================

    #[test]
    fn pop_front_exhausts_first_slice_advances_to_next() {
        // Two slices: first has 1 element, second has 2
        let arc1 = make_arc_slice(1);
        let first_elem = Arc::clone(&arc1[0]);
        let arc2 = make_arc_slice(2);
        let second_first_elem = Arc::clone(&arc2[0]);

        let mut f: Factors<()> = Factors::new();
        f.push_back_slice(Slice::new(arc1));
        f.push_back_slice(Slice::new(arc2));

        assert_eq!(f.len(), 3);

        // Pop first element
        let popped = f.pop_front().unwrap();
        assert!(Arc::ptr_eq(&popped, &first_elem));

        // First slice exhausted, now pointing to second slice
        assert_eq!(f.len(), 2);
        assert!(Arc::ptr_eq(f.front().unwrap(), &second_first_elem));
    }

    #[test]
    fn pop_back_exhausts_last_slice_retreats_to_previous() {
        let arc1 = make_arc_slice(2);
        let first_last_elem = Arc::clone(&arc1[1]);
        let arc2 = make_arc_slice(1);
        let second_elem = Arc::clone(&arc2[0]);

        let mut f: Factors<()> = Factors::new();
        f.push_back_slice(Slice::new(arc1));
        f.push_back_slice(Slice::new(arc2));

        assert_eq!(f.len(), 3);

        // Pop last element
        let popped = f.pop_back().unwrap();
        assert!(Arc::ptr_eq(&popped, &second_elem));

        // Last slice exhausted
        assert_eq!(f.len(), 2);
        assert!(Arc::ptr_eq(f.back().unwrap(), &first_last_elem));
    }

    // ========================================================================
    // EMPTY SLICE HANDLING ON PUSH
    // ========================================================================

    #[test]
    fn push_front_empty_slice_is_noop() {
        let mut f = factors_with_single_slice(1);
        let original_len = f.len();

        f.push_front_slice(empty_slice());

        assert_eq!(f.len(), original_len);
    }

    #[test]
    fn push_back_empty_slice_is_noop() {
        let mut f = factors_with_single_slice(1);
        let original_len = f.len();

        f.push_back_slice(empty_slice());

        assert_eq!(f.len(), original_len);
    }

    #[test]
    fn push_front_slice_to_empty_factors() {
        let mut f: Factors<()> = Factors::new();
        f.push_front_slice(slice_with_n_elements(3));

        assert_eq!(f.len(), 3);
        assert!(!f.is_empty());
    }

    #[test]
    fn push_empty_slice_to_empty_factors_stays_empty() {
        let mut f: Factors<()> = Factors::new();
        f.push_front_slice(empty_slice());

        assert!(f.is_empty());
        assert_eq!(f.len(), 0);
    }

    // ========================================================================
    // OFF-BY-ONE TESTS
    // ========================================================================

    #[test]
    fn pop_front_decrements_correctly() {
        let mut f = factors_with_single_slice(3);

        f.pop_front();
        assert_eq!(f.len(), 2);

        f.pop_front();
        assert_eq!(f.len(), 1);

        f.pop_front();
        assert!(f.is_empty());
    }

    #[test]
    fn pop_back_decrements_correctly() {
        let mut f = factors_with_single_slice(3);

        f.pop_back();
        assert_eq!(f.len(), 2);

        f.pop_back();
        assert_eq!(f.len(), 1);

        f.pop_back();
        assert!(f.is_empty());
    }

    #[test]
    fn front_returns_element_at_correct_position() {
        let arc = make_arc_slice(3);
        let expected = Arc::clone(&arc[1]);

        // Slice skipping first element
        let slice = Slice::with_range(arc, 1, 3);
        let mut f = Factors::new();
        f.push_back_slice(slice);

        assert!(Arc::ptr_eq(f.front().unwrap(), &expected));
    }

    #[test]
    fn back_returns_element_at_correct_position() {
        let arc = make_arc_slice(3);
        let expected = Arc::clone(&arc[1]);

        // Slice ending before last element
        let slice = Slice::with_range(arc, 0, 2);
        let mut f = Factors::new();
        f.push_back_slice(slice);

        assert!(Arc::ptr_eq(f.back().unwrap(), &expected));
    }

    // ========================================================================
    // MULTIPLE SLICES INTERACTION
    // ========================================================================

    #[test]
    fn len_sums_all_slice_lengths() {
        let f = factors_with_slices(vec![3, 2, 5]);
        assert_eq!(f.len(), 10);
    }

    #[test]
    fn front_returns_first_element_of_first_slice() {
        let arc1 = make_arc_slice(2);
        let expected = Arc::clone(&arc1[0]);

        let mut f: Factors<()> = Factors::new();
        f.push_back_slice(Slice::new(arc1));
        f.push_back_slice(slice_with_n_elements(3));

        assert!(Arc::ptr_eq(f.front().unwrap(), &expected));
    }

    #[test]
    fn back_returns_last_element_of_last_slice() {
        let arc2 = make_arc_slice(3);
        let expected = Arc::clone(&arc2[2]);

        let mut f: Factors<()> = Factors::new();
        f.push_back_slice(slice_with_n_elements(2));
        f.push_back_slice(Slice::new(arc2));

        assert!(Arc::ptr_eq(f.back().unwrap(), &expected));
    }

    #[test]
    fn interleaved_push_front_back_maintains_order() {
        let middle_arc = make_arc_slice(1);
        let middle_elem = Arc::clone(&middle_arc[0]);

        let front_arc = make_arc_slice(1);
        let front_elem = Arc::clone(&front_arc[0]);

        let back_arc = make_arc_slice(1);
        let back_elem = Arc::clone(&back_arc[0]);

        let mut f: Factors<()> = Factors::new();
        f.push_back_slice(Slice::new(middle_arc));
        f.push_front_slice(Slice::new(front_arc));
        f.push_back_slice(Slice::new(back_arc));

        // Order should be: front_elem, middle_elem, back_elem
        assert_eq!(f.len(), 3);
        assert!(Arc::ptr_eq(f.front().unwrap(), &front_elem));
        assert!(Arc::ptr_eq(f.back().unwrap(), &back_elem));

        f.pop_front();
        assert!(Arc::ptr_eq(f.front().unwrap(), &middle_elem));
    }

    // ========================================================================
    // STRESS/EXHAUSTION TESTS
    // ========================================================================

    #[test]
    fn exhaust_factors_via_pop_front() {
        let mut f = factors_with_slices(vec![3, 2, 4]);
        let total = f.len();

        let mut count = 0;
        while f.pop_front().is_some() {
            count += 1;
            assert_eq!(f.len(), total - count);
        }

        assert_eq!(count, total);
        assert!(f.is_empty());
    }

    #[test]
    fn exhaust_factors_via_pop_back() {
        let mut f = factors_with_slices(vec![3, 2, 4]);
        let total = f.len();

        let mut count = 0;
        while f.pop_back().is_some() {
            count += 1;
        }

        assert_eq!(count, total);
        assert!(f.is_empty());
    }

    #[test]
    fn alternating_pop_front_back_until_empty() {
        let mut f = factors_with_slices(vec![2, 3, 2]);
        let total = f.len();

        let mut count = 0;
        let mut toggle = true;

        while !f.is_empty() {
            if toggle {
                f.pop_front();
            } else {
                f.pop_back();
            }
            count += 1;
            toggle = !toggle;
        }

        assert_eq!(count, total);
    }

    // ========================================================================
    // ARC SHARING TESTS
    // ========================================================================

    #[test]
    fn slices_share_underlying_arc() {
        let arc = make_arc_slice(4);
        let elem1 = Arc::clone(&arc[1]);
        let elem3 = Arc::clone(&arc[3]);

        let slice1 = Slice::with_range(Arc::clone(&arc), 0, 2);
        let slice2 = Slice::with_range(arc, 2, 4);

        let mut f: Factors<()> = Factors::new();
        f.push_back_slice(slice1);
        f.push_back_slice(slice2);

        assert_eq!(f.len(), 4);

        // Pop first element, front should now be arc[1]
        f.pop_front();
        assert!(Arc::ptr_eq(f.front().unwrap(), &elem1));

        // Pop until we get to second slice
        f.pop_front(); // Now at arc[2]
        f.pop_front(); // Now at arc[3]
        assert!(Arc::ptr_eq(f.front().unwrap(), &elem3));
    }

    // ========================================================================
    // INVARIANT TESTS
    // ========================================================================

    #[test]
    fn len_invariant_maintained_through_operations() {
        let mut f = factors_with_slices(vec![3, 2]);

        assert_eq!(f.len(), 5);

        f.push_front_slice(slice_with_n_elements(2));
        assert_eq!(f.len(), 7);

        f.pop_back();
        assert_eq!(f.len(), 6);

        f.pop_front();
        f.pop_front();
        assert_eq!(f.len(), 4);
    }

    // ========================================================================
    // CONSTRUCTION TESTS
    // ========================================================================

    #[test]
    fn from_seq_creates_single_slice() {
        let elements: Vec<Arc<Rel<()>>> = (0..5).map(|_| make_rel()).collect();
        let arc: Arc<[Arc<Rel<()>>]> = Arc::from(elements);
        let f = Factors::from_seq(arc);

        assert_eq!(f.len(), 5);
    }

    #[test]
    fn from_seq_empty_creates_empty_factors() {
        let elements: Vec<Arc<Rel<()>>> = vec![];
        let arc: Arc<[Arc<Rel<()>>]> = Arc::from(elements);
        let f = Factors::from_seq(arc);

        assert!(f.is_empty());
    }

    // ========================================================================
    // HELPER METHOD TESTS - push_front_rel, push_back_rel, etc.
    // ========================================================================

    #[test]
    fn push_front_rel_adds_single_element_to_front() {
        let mut f = factors_with_single_slice(2);
        let new_rel = make_rel();

        f.push_front_rel(new_rel.clone());

        assert_eq!(f.len(), 3);
        assert!(Arc::ptr_eq(f.front().unwrap(), &new_rel));
    }

    #[test]
    fn push_front_rel_to_empty_factors() {
        let mut f: Factors<()> = Factors::new();
        let new_rel = make_rel();

        f.push_front_rel(new_rel.clone());

        assert_eq!(f.len(), 1);
        assert!(Arc::ptr_eq(f.front().unwrap(), &new_rel));
        assert!(Arc::ptr_eq(f.back().unwrap(), &new_rel));
    }

    #[test]
    fn push_back_rel_adds_single_element_to_back() {
        let mut f = factors_with_single_slice(2);
        let new_rel = make_rel();

        f.push_back_rel(new_rel.clone());

        assert_eq!(f.len(), 3);
        assert!(Arc::ptr_eq(f.back().unwrap(), &new_rel));
    }

    #[test]
    fn push_back_rel_to_empty_factors() {
        let mut f: Factors<()> = Factors::new();
        let new_rel = make_rel();

        f.push_back_rel(new_rel.clone());

        assert_eq!(f.len(), 1);
        assert!(Arc::ptr_eq(f.front().unwrap(), &new_rel));
        assert!(Arc::ptr_eq(f.back().unwrap(), &new_rel));
    }

    #[test]
    fn push_front_rel_then_pop_front_returns_same() {
        let mut f = factors_with_single_slice(1);
        let new_rel = make_rel();

        f.push_front_rel(new_rel.clone());
        let popped = f.pop_front().unwrap();

        assert!(Arc::ptr_eq(&popped, &new_rel));
    }

    #[test]
    fn push_back_rel_then_pop_back_returns_same() {
        let mut f = factors_with_single_slice(1);
        let new_rel = make_rel();

        f.push_back_rel(new_rel.clone());
        let popped = f.pop_back().unwrap();

        assert!(Arc::ptr_eq(&popped, &new_rel));
    }

    #[test]
    fn push_front_slice_from_seq_adds_all_elements() {
        let mut f = factors_with_single_slice(2);
        let seq = make_arc_slice(3);
        let first_of_seq = Arc::clone(&seq[0]);

        f.push_front_slice_from_seq(seq);

        assert_eq!(f.len(), 5);
        assert!(Arc::ptr_eq(f.front().unwrap(), &first_of_seq));
    }

    #[test]
    fn push_front_slice_from_seq_empty_is_noop() {
        let mut f = factors_with_single_slice(2);
        let seq = make_arc_slice(0);

        f.push_front_slice_from_seq(seq);

        assert_eq!(f.len(), 2);
    }

    #[test]
    fn push_back_slice_from_seq_adds_all_elements() {
        let mut f = factors_with_single_slice(2);
        let seq = make_arc_slice(3);
        let last_of_seq = Arc::clone(&seq[2]);

        f.push_back_slice_from_seq(seq);

        assert_eq!(f.len(), 5);
        assert!(Arc::ptr_eq(f.back().unwrap(), &last_of_seq));
    }

    #[test]
    fn push_back_slice_from_seq_empty_is_noop() {
        let mut f = factors_with_single_slice(2);
        let seq = make_arc_slice(0);

        f.push_back_slice_from_seq(seq);

        assert_eq!(f.len(), 2);
    }

    #[test]
    fn push_front_slice_from_seq_to_empty_factors() {
        let mut f: Factors<()> = Factors::new();
        let seq = make_arc_slice(3);

        f.push_front_slice_from_seq(seq);

        assert_eq!(f.len(), 3);
    }

    #[test]
    fn push_back_slice_from_seq_to_empty_factors() {
        let mut f: Factors<()> = Factors::new();
        let seq = make_arc_slice(3);

        f.push_back_slice_from_seq(seq);

        assert_eq!(f.len(), 3);
    }
}
