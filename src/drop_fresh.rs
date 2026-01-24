use smallvec::SmallVec;

/// A DropFresh represents a monotone partial injection between two arities.
///
/// Semantically: Start with `in_arity` values, the DropFresh specifies which
/// input positions map to which output positions. Positions not in the
/// mapping are "dropped" (inputs) or "fresh" (outputs).
///
/// The map is a list of (input_pos, output_pos) pairs that must be:
/// - Strictly increasing in both coordinates
/// - All input positions < in_arity
/// - All output positions < out_arity
///
/// Example: DropFresh { in: 3, out: 2, map: [(0,0), (2,1)] }
/// - Input 0 maps to output 0
/// - Input 1 is dropped
/// - Input 2 maps to output 1
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DropFresh<C> {
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

impl<C: Default> DropFresh<C> {
    /// Create an identity DropFresh of the given arity.
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

impl<C> DropFresh<C> {
    /// Create an identity DropFresh of the given arity with a specific constraint.
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

impl<C: Clone> DropFresh<C> {
    /// Create a new DropFresh with validation.
    /// Returns None if the mapping is not monotone or out of bounds.
    pub fn new(
        in_arity: u32,
        out_arity: u32,
        map: SmallVec<[(u32, u32); 4]>,
        constraint: C,
    ) -> Option<Self> {
        let drop_fresh = Self {
            in_arity,
            out_arity,
            map,
            constraint,
        };
        if drop_fresh.validate() {
            Some(drop_fresh)
        } else {
            None
        }
    }

    /// Create a DropFresh that drops all inputs and produces all fresh outputs.
    /// No inputs are connected to outputs.
    pub fn disconnect(in_arity: u32, out_arity: u32, constraint: C) -> Self {
        Self {
            in_arity,
            out_arity,
            map: SmallVec::new(),
            constraint,
        }
    }

    /// Compose two DropFresh values: self ; other.
    /// The output arity of self must match the input arity of other.
    /// Returns None if arities don't match.
    pub fn compose(&self, other: &DropFresh<C>) -> Option<DropFresh<C>>
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

        Some(DropFresh {
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

    /// Check if this is an identity DropFresh.
    pub fn is_identity(&self) -> bool {
        if self.in_arity != self.out_arity {
            return false;
        }
        if self.map.len() != self.in_arity as usize {
            return false;
        }
        // Check that each position maps to itself
        self.map
            .iter()
            .enumerate()
            .all(|(i, &(inp, out))| inp == i as u32 && out == i as u32)
    }

    /// Check if this DropFresh connects no positions.
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

    /// Validate that the DropFresh is well-formed.
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
mod tests;
