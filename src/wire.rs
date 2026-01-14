use smallvec::SmallVec;

/// A Wire represents a monotone partial injection between two arities.
///
/// Semantically: Start with `in_arity` values, the Wire specifies which
/// input positions map to which output positions. Positions not in the
/// mapping are "dropped" (inputs) or "fresh" (outputs).
///
/// The map is a list of (input_pos, output_pos) pairs that must be:
/// - Strictly increasing in both coordinates
/// - All input positions < in_arity
/// - All output positions < out_arity
///
/// Example: Wire { in: 3, out: 2, map: [(0,0), (2,1)] }
/// - Input 0 maps to output 0
/// - Input 1 is dropped
/// - Input 2 maps to output 1
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Wire<C> {
    /// Number of input positions.
    pub in_arity: u32,
    /// Number of output positions.
    pub out_arity: u32,
    /// Monotone partial injection: (input_pos, output_pos) pairs.
    /// Must be strictly increasing in both coordinates.
    pub map: SmallVec<[(u32, u32); 4]>,
    /// Associated constraint.
    pub constraint: C,
}

impl<C: Default> Wire<C> {
    /// Create an identity wire of the given arity.
    /// Maps position i to position i for all i in 0..arity.
    pub fn identity(arity: u32) -> Self {
        let map: SmallVec<[(u32, u32); 4]> = (0..arity).map(|i| (i, i)).collect();
        Self {
            in_arity: arity,
            out_arity: arity,
            map,
            constraint: C::default(),
        }
    }
}

impl<C> Wire<C> {
    /// Create an identity wire of the given arity with a specific constraint.
    /// Maps position i to position i for all i in 0..arity.
    pub fn identity_with_constraint(arity: u32, constraint: C) -> Self {
        let map: SmallVec<[(u32, u32); 4]> = (0..arity).map(|i| (i, i)).collect();
        Self {
            in_arity: arity,
            out_arity: arity,
            map,
            constraint,
        }
    }
}

impl<C: Clone> Wire<C> {
    /// Create a new wire with validation.
    /// Returns None if the mapping is not monotone or out of bounds.
    pub fn new(in_arity: u32, out_arity: u32, map: SmallVec<[(u32, u32); 4]>, constraint: C) -> Option<Self> {
        let wire = Self {
            in_arity,
            out_arity,
            map,
            constraint,
        };
        if wire.validate() {
            Some(wire)
        } else {
            None
        }
    }

    /// Create a wire that drops all inputs and produces all fresh outputs.
    /// No inputs are connected to outputs.
    pub fn disconnect(in_arity: u32, out_arity: u32, constraint: C) -> Self {
        Self {
            in_arity,
            out_arity,
            map: SmallVec::new(),
            constraint,
        }
    }

    /// Compose two wires: self ; other.
    /// The output arity of self must match the input arity of other.
    /// Returns None if arities don't match.
    pub fn compose(&self, other: &Wire<C>) -> Option<Wire<C>>
    where
        C: Default,
    {
        if self.out_arity != other.in_arity {
            return None;
        }

        // Compose the mappings:
        // For each (in_a, mid) in self.map and (mid, out_b) in other.map
        // where mid matches, produce (in_a, out_b)
        let mut result_map = SmallVec::new();

        // Use merge-join since both maps are sorted by their output/input respectively
        let mut i = 0;
        let mut j = 0;

        while i < self.map.len() && j < other.map.len() {
            let (in_a, mid_a) = self.map[i];
            let (mid_b, out_b) = other.map[j];

            if mid_a < mid_b {
                // self's output not in other's input, skip
                i += 1;
            } else if mid_a > mid_b {
                // other's input not in self's output, skip
                j += 1;
            } else {
                // mid_a == mid_b: they connect
                result_map.push((in_a, out_b));
                i += 1;
                j += 1;
            }
        }

        Some(Wire {
            in_arity: self.in_arity,
            out_arity: other.out_arity,
            map: result_map,
            constraint: C::default(),
        })
    }

    /// Get the number of positions that are mapped (shared between in and out).
    pub fn shared_count(&self) -> usize {
        self.map.len()
    }

    /// Check if this is an identity wire.
    pub fn is_identity(&self) -> bool {
        if self.in_arity != self.out_arity {
            return false;
        }
        if self.map.len() != self.in_arity as usize {
            return false;
        }
        // Check that each position maps to itself
        self.map.iter().enumerate().all(|(i, &(inp, out))| {
            inp == i as u32 && out == i as u32
        })
    }

    /// Check if this wire connects no positions.
    pub fn is_disconnect(&self) -> bool {
        self.map.is_empty()
    }

    /// Get the output position for a given input position, if mapped.
    pub fn forward(&self, input_pos: u32) -> Option<u32> {
        // Binary search since map is sorted by input position
        self.map
            .binary_search_by_key(&input_pos, |&(inp, _)| inp)
            .ok()
            .map(|idx| self.map[idx].1)
    }

    /// Get the input position for a given output position, if mapped.
    pub fn backward(&self, output_pos: u32) -> Option<u32> {
        // Linear search since map is sorted by input, not output
        // (Could optimize with a parallel sorted structure if needed)
        self.map
            .iter()
            .find(|&&(_, out)| out == output_pos)
            .map(|&(inp, _)| inp)
    }

    /// Validate that the wire is well-formed.
    fn validate(&self) -> bool {
        // Empty map is always valid
        if self.map.is_empty() {
            return true;
        }

        // Check bounds and strict monotonicity
        let mut prev_in = None;
        let mut prev_out = None;

        for &(inp, out) in &self.map {
            // Check bounds
            if inp >= self.in_arity || out >= self.out_arity {
                return false;
            }

            // Check strictly increasing in input positions
            if let Some(p) = prev_in {
                if inp <= p {
                    return false;
                }
            }
            prev_in = Some(inp);

            // Check strictly increasing in output positions
            if let Some(p) = prev_out {
                if out <= p {
                    return false;
                }
            }
            prev_out = Some(out);
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========== HAPPY PATH: CONSTRUCTION TESTS ==========

    #[test]
    fn identity_wire_arity_0() {
        let wire: Wire<()> = Wire::identity(0);
        assert_eq!(wire.in_arity, 0);
        assert_eq!(wire.out_arity, 0);
        assert!(wire.map.is_empty());
    }

    #[test]
    fn identity_wire_arity_1() {
        let wire: Wire<()> = Wire::identity(1);
        assert_eq!(wire.in_arity, 1);
        assert_eq!(wire.out_arity, 1);
        assert_eq!(wire.map.as_slice(), &[(0, 0)]);
    }

    #[test]
    fn identity_wire_arity_3() {
        let wire: Wire<()> = Wire::identity(3);
        assert_eq!(wire.in_arity, 3);
        assert_eq!(wire.out_arity, 3);
        assert_eq!(wire.map.as_slice(), &[(0, 0), (1, 1), (2, 2)]);
    }

    #[test]
    fn identity_is_identity() {
        let wire: Wire<()> = Wire::identity(5);
        assert!(wire.is_identity());
    }

    #[test]
    fn new_valid_wire() {
        let map = smallvec::smallvec![(0u32, 0u32), (2, 1)];
        let wire: Wire<()> = Wire::new(3, 2, map.clone(), ()).unwrap();
        assert_eq!(wire.in_arity, 3);
        assert_eq!(wire.out_arity, 2);
        assert_eq!(wire.map.as_slice(), &[(0, 0), (2, 1)]);
    }

    #[test]
    fn disconnect_wire() {
        let wire: Wire<()> = Wire::disconnect(3, 2, ());
        assert_eq!(wire.in_arity, 3);
        assert_eq!(wire.out_arity, 2);
        assert!(wire.map.is_empty());
        assert!(wire.is_disconnect());
    }

    #[test]
    fn disconnect_is_not_identity() {
        let wire: Wire<()> = Wire::disconnect(2, 2, ());
        assert!(!wire.is_identity());
    }

    #[test]
    fn shared_count_for_identity() {
        let wire: Wire<()> = Wire::identity(5);
        assert_eq!(wire.shared_count(), 5);
    }

    #[test]
    fn shared_count_for_partial() {
        let map = smallvec::smallvec![(0u32, 0u32), (2, 1)];
        let wire: Wire<()> = Wire::new(4, 3, map, ()).unwrap();
        assert_eq!(wire.shared_count(), 2);
    }

    // ========== HAPPY PATH: FORWARD/BACKWARD LOOKUP ==========

    #[test]
    fn forward_lookup_identity() {
        let wire: Wire<()> = Wire::identity(3);
        assert_eq!(wire.forward(0), Some(0));
        assert_eq!(wire.forward(1), Some(1));
        assert_eq!(wire.forward(2), Some(2));
    }

    #[test]
    fn forward_lookup_partial() {
        let map = smallvec::smallvec![(0u32, 1u32), (2, 3)];
        let wire: Wire<()> = Wire::new(4, 5, map, ()).unwrap();
        assert_eq!(wire.forward(0), Some(1), "0 -> 1");
        assert_eq!(wire.forward(1), None, "1 not mapped");
        assert_eq!(wire.forward(2), Some(3), "2 -> 3");
        assert_eq!(wire.forward(3), None, "3 not mapped");
    }

    #[test]
    fn backward_lookup_identity() {
        let wire: Wire<()> = Wire::identity(3);
        assert_eq!(wire.backward(0), Some(0));
        assert_eq!(wire.backward(1), Some(1));
        assert_eq!(wire.backward(2), Some(2));
    }

    #[test]
    fn backward_lookup_partial() {
        let map = smallvec::smallvec![(0u32, 1u32), (2, 3)];
        let wire: Wire<()> = Wire::new(4, 5, map, ()).unwrap();
        assert_eq!(wire.backward(0), None, "0 not mapped");
        assert_eq!(wire.backward(1), Some(0), "1 <- 0");
        assert_eq!(wire.backward(2), None, "2 not mapped");
        assert_eq!(wire.backward(3), Some(2), "3 <- 2");
        assert_eq!(wire.backward(4), None, "4 not mapped");
    }

    // ========== HAPPY PATH: COMPOSITION TESTS ==========

    #[test]
    fn compose_identity_identity() {
        let a: Wire<()> = Wire::identity(3);
        let b: Wire<()> = Wire::identity(3);
        let c = a.compose(&b).unwrap();
        assert!(c.is_identity());
        assert_eq!(c.in_arity, 3);
        assert_eq!(c.out_arity, 3);
    }

    #[test]
    fn compose_identity_with_other() {
        let id: Wire<()> = Wire::identity(3);
        let map = smallvec::smallvec![(0u32, 0u32), (2, 1)];
        let other: Wire<()> = Wire::new(3, 2, map, ()).unwrap();

        let result = id.compose(&other).unwrap();
        assert_eq!(result.in_arity, 3);
        assert_eq!(result.out_arity, 2);
        assert_eq!(result.map.as_slice(), &[(0, 0), (2, 1)]);
    }

    #[test]
    fn compose_other_with_identity() {
        let map = smallvec::smallvec![(0u32, 0u32), (2, 1)];
        let other: Wire<()> = Wire::new(3, 2, map, ()).unwrap();
        let id: Wire<()> = Wire::identity(2);

        let result = other.compose(&id).unwrap();
        assert_eq!(result.in_arity, 3);
        assert_eq!(result.out_arity, 2);
        assert_eq!(result.map.as_slice(), &[(0, 0), (2, 1)]);
    }

    #[test]
    fn compose_drops_unmapped() {
        // First wire: 3 inputs, 2 outputs, maps 0->0, 1->1
        let a_map = smallvec::smallvec![(0u32, 0u32), (1, 1)];
        let a: Wire<()> = Wire::new(3, 2, a_map, ()).unwrap();

        // Second wire: 2 inputs, 2 outputs, maps 1->0
        let b_map = smallvec::smallvec![(1u32, 0u32)];
        let b: Wire<()> = Wire::new(2, 2, b_map, ()).unwrap();

        // Composition: input 1 of a goes to output 1, which is input 1 of b,
        // which maps to output 0 of b. So result maps 1->0.
        let c = a.compose(&b).unwrap();
        assert_eq!(c.in_arity, 3);
        assert_eq!(c.out_arity, 2);
        assert_eq!(c.map.as_slice(), &[(1, 0)]);
    }

    #[test]
    fn compose_chain_of_projections() {
        // a: 4 -> 3, keeps positions 0, 1, 3
        let a: Wire<()> = Wire::new(4, 3, smallvec::smallvec![(0u32, 0u32), (1, 1), (3, 2)], ()).unwrap();

        // b: 3 -> 2, keeps positions 0, 2
        let b: Wire<()> = Wire::new(3, 2, smallvec::smallvec![(0u32, 0u32), (2, 1)], ()).unwrap();

        // Composed: should keep input 0 -> output 0, input 3 -> output 1
        let c = a.compose(&b).unwrap();
        assert_eq!(c.in_arity, 4);
        assert_eq!(c.out_arity, 2);
        assert_eq!(c.map.as_slice(), &[(0, 0), (3, 1)]);
    }

    #[test]
    fn compose_disconnect_with_anything() {
        let disc: Wire<()> = Wire::disconnect(3, 2, ());
        let other: Wire<()> = Wire::identity(2);

        let result = disc.compose(&other).unwrap();
        assert!(result.is_disconnect());
        assert_eq!(result.in_arity, 3);
        assert_eq!(result.out_arity, 2);
    }

    #[test]
    fn compose_anything_with_disconnect() {
        let other: Wire<()> = Wire::identity(3);
        let disc: Wire<()> = Wire::disconnect(3, 2, ());

        let result = other.compose(&disc).unwrap();
        assert!(result.is_disconnect());
        assert_eq!(result.in_arity, 3);
        assert_eq!(result.out_arity, 2);
    }

    // ========== UNHAPPY PATH: VALIDATION TESTS ==========

    #[test]
    fn new_rejects_non_monotone_input() {
        // Input positions not strictly increasing: (1, 0), (0, 1)
        let map = smallvec::smallvec![(1u32, 0u32), (0, 1)];
        let result: Option<Wire<()>> = Wire::new(3, 2, map, ());
        assert!(result.is_none(), "Should reject non-monotone input positions");
    }

    #[test]
    fn new_rejects_non_monotone_output() {
        // Output positions not strictly increasing: (0, 1), (1, 0)
        let map = smallvec::smallvec![(0u32, 1u32), (1, 0)];
        let result: Option<Wire<()>> = Wire::new(3, 2, map, ());
        assert!(result.is_none(), "Should reject non-monotone output positions");
    }

    #[test]
    fn new_rejects_duplicate_input() {
        // Same input position twice: (0, 0), (0, 1)
        let map = smallvec::smallvec![(0u32, 0u32), (0, 1)];
        let result: Option<Wire<()>> = Wire::new(3, 2, map, ());
        assert!(result.is_none(), "Should reject duplicate input positions");
    }

    #[test]
    fn new_rejects_duplicate_output() {
        // Same output position twice: (0, 0), (1, 0)
        let map = smallvec::smallvec![(0u32, 0u32), (1, 0)];
        let result: Option<Wire<()>> = Wire::new(3, 2, map, ());
        assert!(result.is_none(), "Should reject duplicate output positions");
    }

    #[test]
    fn new_rejects_out_of_bounds_input() {
        // Input position 5 >= in_arity 3
        let map = smallvec::smallvec![(0u32, 0u32), (5, 1)];
        let result: Option<Wire<()>> = Wire::new(3, 2, map, ());
        assert!(result.is_none(), "Should reject out of bounds input position");
    }

    #[test]
    fn new_rejects_out_of_bounds_output() {
        // Output position 5 >= out_arity 2
        let map = smallvec::smallvec![(0u32, 0u32), (1, 5)];
        let result: Option<Wire<()>> = Wire::new(3, 2, map, ());
        assert!(result.is_none(), "Should reject out of bounds output position");
    }

    #[test]
    fn compose_rejects_arity_mismatch() {
        let a: Wire<()> = Wire::identity(3);
        let b: Wire<()> = Wire::identity(2);
        let result = a.compose(&b);
        assert!(result.is_none(), "Should reject composition with mismatched arities");
    }

    // ========== EDGE CASES ==========

    #[test]
    fn wire_with_constraint() {
        let map = smallvec::smallvec![(0u32, 0u32)];
        let wire: Wire<i32> = Wire::new(2, 2, map, 42).unwrap();
        assert_eq!(wire.constraint, 42);
    }

    #[test]
    fn empty_wire_is_valid() {
        let wire: Wire<()> = Wire::new(0, 0, SmallVec::new(), ()).unwrap();
        assert_eq!(wire.in_arity, 0);
        assert_eq!(wire.out_arity, 0);
        assert!(wire.is_identity()); // identity on 0 elements
    }

    #[test]
    fn large_wire() {
        // Create a large identity wire
        let wire: Wire<()> = Wire::identity(100);
        assert_eq!(wire.in_arity, 100);
        assert_eq!(wire.out_arity, 100);
        assert_eq!(wire.shared_count(), 100);
        assert!(wire.is_identity());
    }

    #[test]
    fn forward_out_of_range() {
        let wire: Wire<()> = Wire::identity(3);
        assert_eq!(wire.forward(5), None, "Should return None for out of range input");
    }

    #[test]
    fn backward_out_of_range() {
        let wire: Wire<()> = Wire::identity(3);
        assert_eq!(wire.backward(5), None, "Should return None for out of range output");
    }
}
