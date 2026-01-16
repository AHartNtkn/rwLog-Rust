//! Dual operation for NFs - swaps match/build and inverts wire direction.
//!
//! The dual of a relation R is its converse: if R relates a to b,
//! then dual(R) relates b to a.

use crate::nf::NF;
use crate::wire::Wire;
use smallvec::SmallVec;

/// Compute the dual of a wire.
///
/// The dual swaps input and output arities, and inverts the mapping.
/// After inversion, the map is re-sorted by first coordinate to maintain
/// the strictly-increasing invariant.
///
/// Properties:
/// - dual(dual(w)) == w (involution)
/// - dual swaps in_arity and out_arity
/// - Constraint is preserved
pub fn dual_wire<C: Clone>(wire: &Wire<C>) -> Wire<C> {
    // Swap arities
    let new_in_arity = wire.out_arity;
    let new_out_arity = wire.in_arity;

    // Invert map: (i, j) -> (j, i)
    let mut inverted: SmallVec<[(u32, u32); 4]> = wire
        .map
        .iter()
        .map(|&(i, j)| (j, i))
        .collect();

    // CRITICAL: Re-sort by first coordinate to maintain invariant
    // The original map is sorted by i, so after inversion the j values
    // (now first) may not be in order.
    inverted.sort_by_key(|&(first, _)| first);

    Wire {
        in_arity: new_in_arity,
        out_arity: new_out_arity,
        map: inverted,
        constraint: wire.constraint.clone(),
    }
}

/// Compute the dual of a Normal Form.
///
/// The dual:
/// - Swaps match_pats and build_pats
/// - Dualizes the wire
///
/// Properties:
/// - dual(dual(nf)) == nf (involution)
/// - If nf represents relation R, dual(nf) represents the converse R^(-1)
pub fn dual_nf<C: Clone>(nf: &NF<C>) -> NF<C> {
    NF {
        match_pats: nf.build_pats.clone(),
        wire: dual_wire(&nf.wire),
        build_pats: nf.match_pats.clone(),
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::compose_nf;
    use crate::nf::NF;
    use crate::test_utils::setup;
    use crate::wire::Wire;
    use smallvec::SmallVec;

    // Import the functions we're testing (don't exist yet - will fail to compile)
    use super::{dual_nf, dual_wire};

    // ========================================================================
    // WIRE TESTS - BASIC PROPERTIES
    // ========================================================================

    #[test]
    fn dual_wire_identity_zero_arity() {
        // Identity on zero elements is self-dual
        let wire: Wire<()> = Wire::identity(0);
        let dual = dual_wire(&wire);

        assert!(dual.is_identity(), "identity(0) should be self-dual");
        assert_eq!(dual.in_arity, 0);
        assert_eq!(dual.out_arity, 0);
    }

    #[test]
    fn dual_wire_identity_single() {
        // Identity on 1 element is self-dual
        let wire: Wire<()> = Wire::identity(1);
        let dual = dual_wire(&wire);

        assert!(dual.is_identity());
        assert_eq!(dual.in_arity, 1);
        assert_eq!(dual.out_arity, 1);
        assert_eq!(dual.map.as_slice(), &[(0, 0)]);
    }

    #[test]
    fn dual_wire_identity_multiple() {
        // Identity on n elements is self-dual
        let wire: Wire<()> = Wire::identity(5);
        let dual = dual_wire(&wire);

        assert!(dual.is_identity());
        assert_eq!(dual.in_arity, 5);
        assert_eq!(dual.out_arity, 5);
    }

    #[test]
    fn dual_wire_swaps_arities() {
        // Fundamental: dual swaps in_arity and out_arity
        let wire: Wire<()> = Wire {
            in_arity: 3,
            out_arity: 7,
            map: SmallVec::from_slice(&[(0, 2), (2, 5)]),
            constraint: (),
        };
        let dual = dual_wire(&wire);

        assert_eq!(dual.in_arity, 7, "in_arity should become old out_arity");
        assert_eq!(dual.out_arity, 3, "out_arity should become old in_arity");
    }

    #[test]
    fn dual_wire_involution() {
        // CRITICAL: dual(dual(w)) == w
        let wire: Wire<()> = Wire {
            in_arity: 4,
            out_arity: 3,
            map: SmallVec::from_slice(&[(0, 0), (2, 1), (3, 2)]),
            constraint: (),
        };
        let dual1 = dual_wire(&wire);
        let dual2 = dual_wire(&dual1);

        assert_eq!(dual2.in_arity, wire.in_arity);
        assert_eq!(dual2.out_arity, wire.out_arity);
        assert_eq!(dual2.map, wire.map, "dual(dual(wire)) should equal wire");
    }

    #[test]
    fn dual_wire_involution_complex() {
        // Involution with more complex wire
        let wire: Wire<()> = Wire {
            in_arity: 6,
            out_arity: 5,
            map: SmallVec::from_slice(&[(1, 0), (2, 2), (4, 3), (5, 4)]),
            constraint: (),
        };
        let dual1 = dual_wire(&wire);
        let dual2 = dual_wire(&dual1);

        assert_eq!(dual2.in_arity, wire.in_arity);
        assert_eq!(dual2.out_arity, wire.out_arity);
        assert_eq!(dual2.map, wire.map);
    }

    // ========================================================================
    // WIRE TESTS - MAP INVERSION AND RE-SORTING (CRITICAL BUG AREA)
    // ========================================================================

    #[test]
    fn dual_wire_simple_inversion() {
        // Simple case: (0,1) becomes (1,0)
        let wire: Wire<()> = Wire {
            in_arity: 2,
            out_arity: 3,
            map: SmallVec::from_slice(&[(0, 1), (1, 2)]),
            constraint: (),
        };
        let dual = dual_wire(&wire);

        // After inversion: (1,0), (2,1)
        // These are already sorted by first coord
        assert_eq!(dual.map.as_slice(), &[(1, 0), (2, 1)]);
    }

    #[test]
    fn dual_wire_requires_resorting() {
        // CRITICAL: After inversion, map may not be sorted and MUST be re-sorted
        // Original: [(0, 3), (1, 1), (2, 2)]
        // After naive inversion: [(3, 0), (1, 1), (2, 2)] - NOT sorted!
        // After proper sorting: [(1, 1), (2, 2), (3, 0)]
        let wire: Wire<()> = Wire {
            in_arity: 3,
            out_arity: 4,
            map: SmallVec::from_slice(&[(0, 3), (1, 1), (2, 2)]),
            constraint: (),
        };
        let dual = dual_wire(&wire);

        assert_eq!(dual.in_arity, 4);
        assert_eq!(dual.out_arity, 3);
        // Must be sorted by first coordinate (input position)
        assert_eq!(
            dual.map.as_slice(),
            &[(1, 1), (2, 2), (3, 0)],
            "Map must be re-sorted after inversion"
        );
    }

    #[test]
    fn dual_wire_complex_resorting() {
        // More complex case requiring careful re-sorting
        // Original: [(0, 4), (1, 2), (3, 0), (4, 3)]
        // After inversion: [(4, 0), (2, 1), (0, 3), (3, 4)]
        // After sorting by first coord: [(0, 3), (2, 1), (3, 4), (4, 0)]
        let wire: Wire<()> = Wire {
            in_arity: 5,
            out_arity: 5,
            map: SmallVec::from_slice(&[(0, 4), (1, 2), (3, 0), (4, 3)]),
            constraint: (),
        };
        let dual = dual_wire(&wire);

        assert_eq!(
            dual.map.as_slice(),
            &[(0, 3), (2, 1), (3, 4), (4, 0)],
            "Complex map must be correctly re-sorted"
        );
    }

    #[test]
    fn dual_wire_preserves_monotonicity() {
        // After dual, map must still be strictly increasing in BOTH coordinates
        let wire: Wire<()> = Wire {
            in_arity: 4,
            out_arity: 5,
            map: SmallVec::from_slice(&[(0, 1), (1, 3), (3, 4)]),
            constraint: (),
        };
        let dual = dual_wire(&wire);

        // Verify strictly increasing in first coord
        for i in 1..dual.map.len() {
            assert!(
                dual.map[i].0 > dual.map[i - 1].0,
                "Map must be strictly increasing in first coord"
            );
        }
        // Verify strictly increasing in second coord
        for i in 1..dual.map.len() {
            assert!(
                dual.map[i].1 > dual.map[i - 1].1,
                "Map must be strictly increasing in second coord"
            );
        }
    }

    // ========================================================================
    // WIRE TESTS - EDGE CASES (EMPTY, DISCONNECT, DROPS, ADDS)
    // ========================================================================

    #[test]
    fn dual_wire_empty_map_disconnect() {
        // Disconnect wire (no connections) stays disconnect
        let wire: Wire<()> = Wire {
            in_arity: 3,
            out_arity: 4,
            map: SmallVec::new(),
            constraint: (),
        };
        let dual = dual_wire(&wire);

        assert_eq!(dual.in_arity, 4);
        assert_eq!(dual.out_arity, 3);
        assert!(dual.map.is_empty(), "Disconnect stays disconnect");
    }

    #[test]
    fn dual_wire_zero_in_arity() {
        // Wire that introduces all fresh variables (no input)
        let wire: Wire<()> = Wire {
            in_arity: 0,
            out_arity: 3,
            map: SmallVec::new(),
            constraint: (),
        };
        let dual = dual_wire(&wire);

        assert_eq!(dual.in_arity, 3);
        assert_eq!(dual.out_arity, 0);
        assert!(dual.map.is_empty());
    }

    #[test]
    fn dual_wire_zero_out_arity() {
        // Wire that drops all variables (no output)
        let wire: Wire<()> = Wire {
            in_arity: 3,
            out_arity: 0,
            map: SmallVec::new(),
            constraint: (),
        };
        let dual = dual_wire(&wire);

        assert_eq!(dual.in_arity, 0);
        assert_eq!(dual.out_arity, 3);
    }

    #[test]
    fn dual_wire_drops_become_adds() {
        // Wire that drops variables becomes wire that adds fresh variables
        // Original: 5 inputs, 2 outputs, keeps positions 1->0 and 3->1
        let wire: Wire<()> = Wire {
            in_arity: 5,
            out_arity: 2,
            map: SmallVec::from_slice(&[(1, 0), (3, 1)]),
            constraint: (),
        };
        let dual = dual_wire(&wire);

        assert_eq!(dual.in_arity, 2, "Was out_arity");
        assert_eq!(dual.out_arity, 5, "Was in_arity");
        assert_eq!(dual.map.as_slice(), &[(0, 1), (1, 3)]);
    }

    #[test]
    fn dual_wire_adds_become_drops() {
        // Wire that adds fresh variables becomes wire that drops
        let wire: Wire<()> = Wire {
            in_arity: 2,
            out_arity: 5,
            map: SmallVec::from_slice(&[(0, 1), (1, 3)]),
            constraint: (),
        };
        let dual = dual_wire(&wire);

        assert_eq!(dual.in_arity, 5);
        assert_eq!(dual.out_arity, 2);
        assert_eq!(dual.map.as_slice(), &[(1, 0), (3, 1)]);
    }

    #[test]
    fn dual_wire_single_mapping() {
        // Minimal non-empty case
        let wire: Wire<()> = Wire {
            in_arity: 3,
            out_arity: 4,
            map: SmallVec::from_slice(&[(2, 1)]),
            constraint: (),
        };
        let dual = dual_wire(&wire);

        assert_eq!(dual.in_arity, 4);
        assert_eq!(dual.out_arity, 3);
        assert_eq!(dual.map.as_slice(), &[(1, 2)]);
    }

    #[test]
    fn dual_wire_boundary_indices() {
        // Test with boundary indices (0 and max-1)
        let wire: Wire<()> = Wire {
            in_arity: 4,
            out_arity: 5,
            map: SmallVec::from_slice(&[(0, 0), (3, 4)]),
            constraint: (),
        };
        let dual = dual_wire(&wire);

        assert_eq!(dual.map.as_slice(), &[(0, 0), (4, 3)]);
    }

    #[test]
    fn dual_wire_preserves_constraint() {
        let wire: Wire<i32> = Wire {
            in_arity: 2,
            out_arity: 3,
            map: SmallVec::from_slice(&[(0, 1)]),
            constraint: 42,
        };
        let dual = dual_wire(&wire);

        assert_eq!(dual.constraint, 42, "Constraint must be preserved");
    }

    // ========================================================================
    // NF TESTS - BASIC PROPERTIES
    // ========================================================================

    #[test]
    fn dual_nf_empty_identity() {
        // Empty identity NF is self-dual
        let nf: NF<()> = NF::identity(());
        let dual = dual_nf(&nf);

        assert!(dual.match_pats.is_empty());
        assert!(dual.build_pats.is_empty());
        assert!(dual.wire.is_identity());
    }

    #[test]
    fn dual_nf_swaps_patterns() {
        // Fundamental: dual swaps match_pats and build_pats
        let (symbols, terms) = setup();
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let ta = terms.app0(a);
        let tb = terms.app0(b);

        // NF: A -> B
        let nf: NF<()> = NF::new(
            SmallVec::from_slice(&[ta]),
            Wire::identity(0),
            SmallVec::from_slice(&[tb]),
        );

        let dual = dual_nf(&nf);

        // dual: B -> A
        assert_eq!(dual.match_pats.as_slice(), &[tb], "match should be B");
        assert_eq!(dual.build_pats.as_slice(), &[ta], "build should be A");
    }

    #[test]
    fn dual_nf_involution() {
        // CRITICAL: dual(dual(nf)) == nf
        let (symbols, terms) = setup();
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let ta = terms.app0(a);
        let tb = terms.app0(b);

        let nf: NF<()> = NF::new(
            SmallVec::from_slice(&[ta]),
            Wire::identity(0),
            SmallVec::from_slice(&[tb]),
        );

        let dual1 = dual_nf(&nf);
        let dual2 = dual_nf(&dual1);

        assert_eq!(dual2.match_pats, nf.match_pats);
        assert_eq!(dual2.build_pats, nf.build_pats);
        assert_eq!(dual2.wire.in_arity, nf.wire.in_arity);
        assert_eq!(dual2.wire.out_arity, nf.wire.out_arity);
        assert_eq!(dual2.wire.map, nf.wire.map);
    }

    #[test]
    fn dual_nf_identity_is_self_dual() {
        // x -> x should be self-dual
        let (_, terms) = setup();
        let v0 = terms.var(0);

        let nf: NF<()> = NF::new(
            SmallVec::from_slice(&[v0]),
            Wire::identity(1),
            SmallVec::from_slice(&[v0]),
        );

        let dual = dual_nf(&nf);

        assert_eq!(terms.is_var(dual.match_pats[0]), Some(0));
        assert_eq!(terms.is_var(dual.build_pats[0]), Some(0));
        assert!(dual.wire.is_identity());
    }

    // ========================================================================
    // NF TESTS - WIRE INTEGRATION
    // ========================================================================

    #[test]
    fn dual_nf_dualizes_wire() {
        // Wire arities should swap when NF is dualized
        let (_, terms) = setup();
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // 2 input vars, 1 output var
        let nf: NF<()> = NF::new(
            SmallVec::from_slice(&[v0, v1]),
            Wire {
                in_arity: 2,
                out_arity: 1,
                map: SmallVec::from_slice(&[(0, 0)]),
                constraint: (),
            },
            SmallVec::from_slice(&[v0]),
        );

        let dual = dual_nf(&nf);

        // Dual should have 1 input var, 2 output vars
        assert_eq!(dual.wire.in_arity, 1);
        assert_eq!(dual.wire.out_arity, 2);
    }

    #[test]
    fn dual_nf_with_complex_wire() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let g = symbols.intern("G");
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let v2 = terms.var(2);

        let f_term = terms.app2(f, v0, v1);
        let g_term = terms.app1(g, v2);

        // F(x,y) -> G(z) with wire that maps x to z, drops y
        let nf: NF<()> = NF::new(
            SmallVec::from_slice(&[f_term]),
            Wire {
                in_arity: 2,
                out_arity: 1,
                map: SmallVec::from_slice(&[(0, 0)]),
                constraint: (),
            },
            SmallVec::from_slice(&[g_term]),
        );

        let dual = dual_nf(&nf);

        // Dual: G(z) -> F(x,y) with wire that maps z to x, adds fresh y
        assert_eq!(dual.match_pats[0], g_term);
        assert_eq!(dual.build_pats[0], f_term);
        assert_eq!(dual.wire.in_arity, 1);
        assert_eq!(dual.wire.out_arity, 2);
    }

    // ========================================================================
    // NF TESTS - PATTERN EDGE CASES
    // ========================================================================

    #[test]
    fn dual_nf_ground_patterns() {
        // No variables - wire should be identity on 0
        let (symbols, terms) = setup();
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let ta = terms.app0(a);
        let tb = terms.app0(b);

        let nf: NF<()> = NF::new(
            SmallVec::from_slice(&[ta]),
            Wire::identity(0),
            SmallVec::from_slice(&[tb]),
        );

        let dual = dual_nf(&nf);

        assert_eq!(dual.match_pats[0], tb);
        assert_eq!(dual.build_pats[0], ta);
        assert_eq!(dual.wire.in_arity, 0);
        assert_eq!(dual.wire.out_arity, 0);
    }

    #[test]
    fn dual_nf_empty_match_pats() {
        // Empty match (introduces fresh variables)
        let (_, terms) = setup();
        let v0 = terms.var(0);

        let nf: NF<()> = NF::new(
            SmallVec::new(),
            Wire {
                in_arity: 0,
                out_arity: 1,
                map: SmallVec::new(),
                constraint: (),
            },
            SmallVec::from_slice(&[v0]),
        );

        let dual = dual_nf(&nf);

        assert!(dual.match_pats.len() == 1);
        assert!(dual.build_pats.is_empty());
    }

    #[test]
    fn dual_nf_empty_build_pats() {
        // Empty build (drops all variables)
        let (_, terms) = setup();
        let v0 = terms.var(0);

        let nf: NF<()> = NF::new(
            SmallVec::from_slice(&[v0]),
            Wire {
                in_arity: 1,
                out_arity: 0,
                map: SmallVec::new(),
                constraint: (),
            },
            SmallVec::new(),
        );

        let dual = dual_nf(&nf);

        assert!(dual.match_pats.is_empty());
        assert!(dual.build_pats.len() == 1);
    }

    #[test]
    fn dual_nf_multiple_patterns() {
        // Multiple patterns in both match and build
        let (symbols, terms) = setup();
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let c = symbols.intern("C");
        let ta = terms.app0(a);
        let tb = terms.app0(b);
        let tc = terms.app0(c);

        let nf: NF<()> = NF::new(
            SmallVec::from_slice(&[ta, tb]),
            Wire::identity(0),
            SmallVec::from_slice(&[tc]),
        );

        let dual = dual_nf(&nf);

        assert_eq!(dual.match_pats.len(), 1);
        assert_eq!(dual.build_pats.len(), 2);
        assert_eq!(dual.match_pats[0], tc);
        assert_eq!(dual.build_pats.as_slice(), &[ta, tb]);
    }

    #[test]
    fn dual_nf_deeply_nested_terms() {
        // Deep nesting should work
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let v0 = terms.var(0);

        // F(F(F(F(x))))
        let f1 = terms.app1(f, v0);
        let f2 = terms.app1(f, f1);
        let f3 = terms.app1(f, f2);
        let f4 = terms.app1(f, f3);

        let nf: NF<()> = NF::new(
            SmallVec::from_slice(&[f4]),
            Wire::identity(1),
            SmallVec::from_slice(&[v0]),
        );

        let dual = dual_nf(&nf);

        assert_eq!(dual.match_pats[0], v0);
        assert_eq!(dual.build_pats[0], f4);
    }

    // ========================================================================
    // COMPOSITION REVERSAL TESTS (SEMANTIC CORRECTNESS)
    // ========================================================================

    #[test]
    fn dual_reverses_composition_ground() {
        // dual(compose(a, b)) == compose(dual(b), dual(a)) for ground terms
        let (symbols, mut terms) = setup();
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let c = symbols.intern("C");
        let ta = terms.app0(a);
        let tb = terms.app0(b);
        let tc = terms.app0(c);

        // a: A -> B
        let nf_a: NF<()> = NF::new(
            SmallVec::from_slice(&[ta]),
            Wire::identity(0),
            SmallVec::from_slice(&[tb]),
        );
        // b: B -> C
        let nf_b: NF<()> = NF::new(
            SmallVec::from_slice(&[tb]),
            Wire::identity(0),
            SmallVec::from_slice(&[tc]),
        );

        // compose(a, b) = A -> C
        let composed = compose_nf(&nf_a, &nf_b, &mut terms).expect("composition should succeed");
        let dual_composed = dual_nf(&composed);

        // dual(b) = C -> B, dual(a) = B -> A
        // compose(dual(b), dual(a)) = C -> A
        let dual_b = dual_nf(&nf_b);
        let dual_a = dual_nf(&nf_a);
        let composed_duals = compose_nf(&dual_b, &dual_a, &mut terms).expect("composition should succeed");

        assert_eq!(dual_composed.match_pats, composed_duals.match_pats);
        assert_eq!(dual_composed.build_pats, composed_duals.build_pats);
    }

    #[test]
    fn dual_reverses_composition_with_vars() {
        // Same test but with variables
        let (symbols, mut terms) = setup();
        let f = symbols.intern("F");
        let g = symbols.intern("G");
        let h = symbols.intern("H");
        let v0 = terms.var(0);

        let f_x = terms.app1(f, v0);
        let g_x = terms.app1(g, v0);
        let h_x = terms.app1(h, v0);

        // a: F(x) -> G(x)
        let nf_a: NF<()> = NF::new(
            SmallVec::from_slice(&[f_x]),
            Wire::identity(1),
            SmallVec::from_slice(&[g_x]),
        );
        // b: G(x) -> H(x)
        let nf_b: NF<()> = NF::new(
            SmallVec::from_slice(&[g_x]),
            Wire::identity(1),
            SmallVec::from_slice(&[h_x]),
        );

        let composed = compose_nf(&nf_a, &nf_b, &mut terms).expect("composition should succeed");
        let dual_composed = dual_nf(&composed);

        let dual_b = dual_nf(&nf_b);
        let dual_a = dual_nf(&nf_a);
        let composed_duals = compose_nf(&dual_b, &dual_a, &mut terms).expect("composition should succeed");

        // Both should be H(x) -> F(x)
        let (dc_match_f, _) = terms.is_app(dual_composed.match_pats[0]).unwrap();
        let (cd_match_f, _) = terms.is_app(composed_duals.match_pats[0]).unwrap();
        assert_eq!(symbols.resolve(dc_match_f), Some("H"));
        assert_eq!(symbols.resolve(cd_match_f), Some("H"));

        let (dc_build_f, _) = terms.is_app(dual_composed.build_pats[0]).unwrap();
        let (cd_build_f, _) = terms.is_app(composed_duals.build_pats[0]).unwrap();
        assert_eq!(symbols.resolve(dc_build_f), Some("F"));
        assert_eq!(symbols.resolve(cd_build_f), Some("F"));
    }

    #[test]
    fn dual_reverses_peel_composition() {
        // Test from spec: B(A(x),y)->B(x,y) composed with itself
        let (symbols, mut terms) = setup();
        let a = symbols.intern("A");
        let b = symbols.intern("B");
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // B(A(x), y) -> B(x, y)
        let a_x = terms.app1(a, v0);
        let lhs = terms.app2(b, a_x, v1);
        let rhs = terms.app2(b, v0, v1);

        let peel: NF<()> = NF::factor(lhs, rhs, (), &mut terms);

        // compose(peel, peel)
        let composed = compose_nf(&peel, &peel, &mut terms).expect("composition should succeed");
        let dual_composed = dual_nf(&composed);

        // compose(dual(peel), dual(peel))
        let dual_peel = dual_nf(&peel);
        let composed_duals = compose_nf(&dual_peel, &dual_peel, &mut terms).expect("composition should succeed");

        // Verify structure matches
        assert_eq!(dual_composed.wire.in_arity, composed_duals.wire.in_arity);
        assert_eq!(dual_composed.wire.out_arity, composed_duals.wire.out_arity);
    }

    // ========================================================================
    // ASYMMETRIC CASES (DROPS/ADDS VARIABLES)
    // ========================================================================

    #[test]
    fn dual_nf_drops_become_fresh() {
        // NF that drops a variable becomes NF that introduces fresh variable
        let (symbols, terms) = setup();
        let pair = symbols.intern("Pair");
        let fst = symbols.intern("Fst");
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // Pair(x, y) -> Fst(x)  (drops y)
        let pair_xy = terms.app2(pair, v0, v1);
        let fst_x = terms.app1(fst, v0);

        let nf: NF<()> = NF::new(
            SmallVec::from_slice(&[pair_xy]),
            Wire {
                in_arity: 2,
                out_arity: 1,
                map: SmallVec::from_slice(&[(0, 0)]),
                constraint: (),
            },
            SmallVec::from_slice(&[fst_x]),
        );

        let dual = dual_nf(&nf);

        // dual: Fst(x) -> Pair(x, y)  (introduces fresh y)
        assert_eq!(dual.match_pats[0], fst_x);
        assert_eq!(dual.build_pats[0], pair_xy);
        assert_eq!(dual.wire.in_arity, 1);
        assert_eq!(dual.wire.out_arity, 2);
    }

    #[test]
    fn dual_nf_fresh_become_drops() {
        // Inverse of above
        let (symbols, terms) = setup();
        let unit = symbols.intern("Unit");
        let pair = symbols.intern("Pair");
        let v0 = terms.var(0);
        let v1 = terms.var(1);

        // Unit -> Pair(x, y)  (introduces fresh x, y)
        let unit_term = terms.app0(unit);
        let pair_xy = terms.app2(pair, v0, v1);

        let nf: NF<()> = NF::new(
            SmallVec::from_slice(&[unit_term]),
            Wire {
                in_arity: 0,
                out_arity: 2,
                map: SmallVec::new(),
                constraint: (),
            },
            SmallVec::from_slice(&[pair_xy]),
        );

        let dual = dual_nf(&nf);

        // dual: Pair(x, y) -> Unit  (drops x, y)
        assert_eq!(dual.match_pats[0], pair_xy);
        assert_eq!(dual.build_pats[0], unit_term);
        assert_eq!(dual.wire.in_arity, 2);
        assert_eq!(dual.wire.out_arity, 0);
    }
}
